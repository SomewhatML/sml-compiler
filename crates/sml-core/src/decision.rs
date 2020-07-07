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
    list: Vec<(Head, Tree<'a>)>,
    default: Option<usize>,
}

#[derive(Debug)]
pub enum Tree<'a> {
    Leaf(Expr<'a>),
    Switch(Switch<'a>),
    Swap(usize, Box<Tree<'a>>),
    Fail,
}

#[derive(Debug)]
pub struct DecisionTree<'a> {
    nodes: Vec<Tree<'a>>,
}

/// A column-oriented matrix
#[derive(Clone)]
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
    // Variable,
    Wild,
}

impl<'ar> PatKind<'ar> {
    fn head(&self) -> Head {
        match self {
            PatKind::App(c, _) => Head::Enum(*c),
            PatKind::Const(c) => Head::Const(*c),
            PatKind::List(_) => Head::List,
            PatKind::Record(r) => Head::Record(r.len()),
            PatKind::Var(_) => Head::Wild,
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

    fn accepts(&self, head: Head) -> bool {
        match self {
            PatKind::Wild | PatKind::Var(_) => true,
            _ => self.head() == head,
        }
    }
}

impl<'a> Tree<'a> {
    fn pp(&self, depth: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = (0..depth).map(|_| '\t').collect::<String>();
        match self {
            Tree::Leaf(e) => write!(f, "{}{:?}", s, e.expr),
            Tree::Fail => write!(f, "{}FAIL", s),
            Tree::Swap(idx, tree) => {
                write!(f, "{} Swap {}", s, idx)?;
                tree.pp(depth, f)
            }
            Tree::Switch(Switch {
                occurence,
                list,
                default,
            }) => {
                for (head, tree) in list {
                    writeln!(f, "{}{} -> {}", s, occurence, head)?;
                    tree.pp(depth + 1, f)?;
                    writeln!(f, "")?;
                }
                write!(f, "")
            }
        }
    }
}

impl<'a> std::fmt::Display for Tree<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.pp(0, f)
    }
}

impl<'a> std::fmt::Display for Occurence<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Occurence::Expr(e) => write!(f, "root"),
            Occurence::Path(o, i) => write!(f, "{}.{}", o, i),
        }
    }
}

impl std::fmt::Display for Head {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Head::Const(c) => write!(f, "{:?}", c),
            Head::Enum(c) => write!(f, "{:?}", c.name),
            _ => write!(f, "{:?}", self),
        }
    }
}

impl<'a> std::fmt::Debug for Matrix<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{}",
            self.occs
                .iter()
                .map(|o| o.to_string())
                .collect::<Vec<String>>()
                .join(",")
        )?;
        for idx in 0..self.patterns.len() {
            writeln!(f, "{:?} => {:?}", self.patterns[idx], self.exprs[idx].expr)?;
        }
        write!(f, "")
    }
}

impl Head {
    fn arity(&self) -> usize {
        match self {
            Head::Enum(c) => c.arity as usize,
            Head::Record(r) => *r,
            _ => 0,
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
        let mut matrix = Matrix {
            occs: vec![Occurence::Expr(expr)],
            patterns: rules.iter().map(|rule| vec![rule.pat.pat]).collect(),
            exprs: rules.iter().map(|rule| rule.expr).collect(),
            wild: self.arena.pats.wild(),
        };

        dbg!(&matrix);
        println!("{}", matrix.compile());
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
                    Head::Wild => {
                        mat.patterns
                            .push(self.patterns[idx].iter().skip(1).copied().collect());
                        mat.exprs.push(self.exprs[idx].clone());
                    }
                    _ => {}
                },
                None => {}
            }
        }
        mat.occs.remove(0);
        mat
    }

    fn constructor_rule(&mut self, head: Head, col: usize) {
        let mut filtered = Vec::new();
        let mut ex = Vec::new();
        for (mut row, expr) in self.patterns.drain(..).zip(self.exprs.drain(..)) {
            if row.is_empty() {
                continue;
            }

            let fst = row.remove(col);
            if fst.head() == head {
                match fst {
                    PatKind::App(_, Some(p)) => row.insert(col + 0, p.pat),
                    PatKind::Record(r) => {
                        for (idx, r) in r.iter().enumerate() {
                            row.insert(col + idx, r.data.pat);
                        }
                    }
                    _ => {}
                }
                filtered.push(row);
                ex.push(expr);
            } else if fst.accepts(head) {
                for _ in 0..head.arity() {
                    row.insert(col + 0, self.wild);
                }
                filtered.push(row);
                ex.push(expr);
            }
        }
        self.patterns = filtered;
        self.exprs = ex;

        let o = self.occs.remove(col);
        for i in 0..head.arity() {
            self.occs
                .insert(col + i, Occurence::Path(Box::new(o.clone()), i));
        }
    }

    fn specialize(&self, head: Head, col: usize) -> Matrix<'a> {
        let mut mat = self.clone();
        mat.constructor_rule(head, col);
        mat
    }

    fn heuristic(&self) -> usize {
        let mut i = 0;
        while self.col_iter(i).all(|p| p.head() == Head::Wild) {
            i += 1;
        }
        i
    }

    fn swap(&mut self, col: usize) {
        self.occs.swap(0, col);
        for row in self.patterns.iter_mut() {
            row.swap(0, col);
        }
    }

    fn compile(&mut self) -> Tree<'a> {
        if self.patterns.is_empty() {
            Tree::Fail
        } else if self.patterns[0].iter().all(|pat| pat.head() == Head::Wild) {
            Tree::Leaf(self.exprs[0])
        } else {
            let mut set = HashSet::new();
            let col = self.heuristic();

            // if col != 0 {
            //     println!("SWAPPING {}", col);
            //     self.swap(col);
            // }

            for pat in self.col_iter(col) {
                set.insert(pat.head());
            }
            let wildcard = set.remove(&Head::Wild);
            // let var = set.remove(&Head::Variable);

            let exhaustive = if set.is_empty() {
                wildcard
            } else {
                let fst = set.iter().next().unwrap();
                match fst {
                    Head::Wild => unreachable!(),
                    Head::Enum(c) => c.type_arity as usize == set.len(),
                    Head::Record(_) => {
                        self.constructor_rule(*fst, col);
                        return self.compile();
                        // self.col_iter(col).any(|pat| pat.irrefutable())
                    }
                    Head::List => false,
                    Head::Const(_) => false,
                }
            };

            let mut branches = Vec::new();

            for h in set {
                let mut mat = self.specialize(h, col);

                println!("{:?}:\n{:?}\nspecial: {:?}\n", h, self, &mat);
                // let tree = match (mat.compile(), col) {
                //     (tree, 0) => tree,
                //     (tree, _) => Tree::Swap(col, Box::new(tree)),
                // };
                let tree = mat.compile();
                branches.push((h, tree));
            }

            if !exhaustive {
                let mut mat = self.default_matrix();
                println!("default {:#?}", &mat);
                // let tree = match (mat.compile(), col) {
                //     (tree, 0) => tree,
                //     (tree, _) => Tree::Swap(col, Box::new(tree)),
                // };
                let tree = mat.compile();
                branches.push((Head::Wild, tree));
            }

            let default = match exhaustive {
                false => Some(branches.len()),
                true => None,
            };

            Tree::Switch(Switch {
                occurence: self.occs[col].clone(),
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
