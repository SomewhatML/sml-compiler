use super::*;
use sml_util::diagnostics::Diagnostic;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub enum Occurence<'a> {
    Expr(Expr<'a>),
    Path(Box<Occurence<'a>>, usize),
}

#[derive(Debug)]
pub struct Switch<'a> {
    occurence: Occurence<'a>,
    list: Vec<Tree<'a>>,
    default: Option<usize>,
}

#[derive(Debug)]
pub enum Tree<'a> {
    Leaf(Expr<'a>),
    Switch(Switch<'a>),
    Fail,
}

#[derive(Debug)]
pub struct DecisionTree<'a> {
    nodes: Vec<Tree<'a>>,
}

/// A column-oriented matrix
#[derive(Clone, Debug)]
pub struct Matrix<'a> {
    occs: Vec<Occurence<'a>>,
    patterns: Vec<Vec<&'a PatKind<'a>>>,
    exprs: Vec<Expr<'a>>,

    wild: &'a PatKind<'a>,
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
enum Head {
    Enum(Constructor),
    Const(Const),
    List,
    Record(usize),
    Variable,
    Wild,
}

impl<'ar> PatKind<'ar> {
    fn head(&self) -> Head {
        match self {
            PatKind::App(c, _) => Head::Enum(*c),
            PatKind::Const(c) => Head::Const(*c),
            PatKind::List(_) => Head::List,
            PatKind::Record(r) => Head::Record(r.len()),
            PatKind::Var(_) => Head::Variable,
            PatKind::Wild => Head::Wild,
        }
    }

    fn irrefutable(&self) -> bool {
        match self {
            PatKind::App(c, inner) => inner.map(|pat| pat.pat.irrefutable()).unwrap_or(true),
            PatKind::Const(c) => false,
            PatKind::List(_) => false,
            PatKind::Record(r) => r.iter().all(|row| row.data.pat.irrefutable()),
            PatKind::Var(_) => true,
            PatKind::Wild => true,
        }
    }

    fn pop_constructor(&self, v: &mut Vec<&'ar PatKind<'ar>>) {
        match self {
            PatKind::Record(r) => {
                for row in r.iter() {
                    v.push(row.data.pat);
                }
            }

            PatKind::App(c, inner) => match inner {
                Some(pat) => v.push(pat.pat),
                None => {}
            },
            _ => {}
        }
    }
}

impl Head {
    fn arity(&self) -> usize {
        match self {
            Head::Enum(c) => c.arity as usize,
            Head::Record(r) => *r,
            _ => 1,
        }
    }
}

fn find_record_field<T>(rows: &[Row<T>], label: Symbol) -> Option<&T> {
    for row in rows {
        if row.label == label {
            return Some(&row.data);
        }
    }
    None
}

fn expand_pat<'a>(pat: Pat<'a>, v: &mut Vec<Pat<'a>>) {
    match &pat.pat {
        PatKind::Record(rows) => {
            for row in rows.iter() {
                expand_pat(row.data, v);
            }
        }
        _ => v.push(pat),
    }
}

fn mk_occurrence_vector<'a>(expr: Expr<'a>, v: &mut Vec<Occurence<'a>>) {
    match &expr.expr {
        ExprKind::Record(rows) => {
            for row in rows.iter() {
                mk_occurrence_vector(row.data, v);
            }
        }
        _ => v.push(Occurence::Expr(expr)),
    }
}

impl<'arena> elaborate::Context<'arena> {
    pub(crate) fn build_decision_tree(&mut self, expr: Expr<'arena>, rules: &[Rule<'arena>]) {
        // let mut occs = Vec::new();
        // mk_occurrence_vector(expr, &mut occs);
        // println!("expand {:?} -> {:?}", expr, occs);

        // let mut patterns = Vec::new();
        // for rule in rules {
        //     let mut row = Vec::new();
        //     expand_pat(rule.pat, &mut row);
        //     for (idx, pat) in row.into_iter().enumerate() {
        //         if patterns.len() <= idx {
        //             patterns.push(Vec::with_capacity(rules.len()));
        //         }
        //         patterns[idx].push(pat.clone());
        //     }
        // }

        let matrix = Matrix {
            occs: vec![Occurence::Expr(expr)],
            patterns: rules.iter().map(|rule| vec![rule.pat.pat]).collect(),
            exprs: rules.iter().map(|rule| rule.expr).collect(),
            wild: self.arena.pats.wild(),
        };

        dbg!(&matrix);
        dbg!(matrix.compile());
    }
}

impl<'a> Matrix<'a> {
    fn col_iter(&self, col: usize) -> ColIter<'_, 'a> {
        ColIter {
            matrix: self,
            col,
            row: 0,
        }
    }

    fn default_matrix(&self) -> Matrix<'a> {
        let mut mat = Matrix {
            patterns: Vec::with_capacity(self.patterns.len()),
            exprs: Vec::with_capacity(self.exprs.len()),
            occs: self.occs.clone(),
            wild: self.wild,
        };

        for idx in 0..self.patterns.len() {
            match self.patterns[idx].first() {
                Some(&x) => match x.head() {
                    Head::Variable | Head::Wild => {
                        mat.patterns
                            .push(self.patterns[idx].iter().skip(1).copied().collect());
                        mat.exprs.push(self.exprs[idx].clone());
                    }
                    _ => {}
                },
                None => {}
            }
        }
        mat
    }

    fn specialize(&self, head: Head) -> Matrix<'a> {
        let mut mat = Matrix {
            patterns: Vec::with_capacity(self.patterns.len()),
            exprs: Vec::with_capacity(self.exprs.len()),
            occs: self.occs.clone(),
            wild: self.wild,
        };

        for idx in 0..self.patterns.len() {
            match self.patterns[idx].first() {
                Some(&x) => {
                    if x.head() == head {
                        let mut row = Vec::new();
                        x.pop_constructor(&mut row);
                        row.extend(self.patterns[idx].iter().skip(1).copied());
                        mat.patterns.push(row);
                        mat.exprs.push(self.exprs[idx].clone());
                    } else if head.arity() != 0 {
                        match x.head() {
                            Head::Variable | Head::Wild => {
                                mat.patterns
                                    .push(self.patterns[idx].iter().copied().collect());
                                mat.exprs.push(self.exprs[idx].clone());
                            }
                            _ => {}
                        }
                    }
                }
                None => {}
            }
        }
        mat
    }

    fn compile(&self) -> Tree<'a> {
        if self.patterns.is_empty() {
            Tree::Fail
        } else if self.patterns[0].iter().all(|pat| pat.head() == Head::Wild) {
            Tree::Leaf(self.exprs[0])
        } else {
            let mut set = HashSet::new();
            for pat in self.col_iter(0) {
                set.insert(pat.head());
            }
            let wildcard = set.remove(&Head::Wild);
            let var = set.remove(&Head::Variable);

            let exhaustive = if set.is_empty() {
                false
            } else {
                let fst = set.iter().next().unwrap();
                match fst {
                    Head::Variable | Head::Wild => unreachable!(),
                    Head::Enum(c) => c.type_arity as usize == set.len(),
                    Head::Record(_) => self.col_iter(0).any(|pat| pat.irrefutable()),
                    Head::List => false,
                    Head::Const(_) => false,
                }
            };

            let mut branches = Vec::new();
            for h in set {
                let mut mat = self.specialize(h);
                let o = mat.occs.remove(0);
                for i in 0..h.arity() {
                    mat.occs.insert(i, Occurence::Path(Box::new(o.clone()), i));
                }
                branches.push(mat.compile());
            }

            if !exhaustive {
                let mut mat = self.default_matrix();
                mat.occs.remove(0);
                branches.push(mat.compile());
            }

            let default = match exhaustive {
                false => Some(branches.len()),
                true => None,
            };

            Tree::Switch(Switch {
                occurence: self.occs[0].clone(),
                list: branches,
                default,
            })
        }
    }
}

struct ColIter<'m, 'arena> {
    matrix: &'m Matrix<'arena>,
    col: usize,
    row: usize,
}

impl<'m, 'arena> Iterator for ColIter<'m, 'arena> {
    type Item = &'arena PatKind<'arena>;
    fn next(&mut self) -> Option<Self::Item> {
        let r = self.row;
        self.row += 1;
        self.matrix.patterns.get(r)?.get(self.col).copied()
    }
}
