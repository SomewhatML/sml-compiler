use super::*;
use elaborate::Context;
use sml_util::diagnostics::Diagnostic;
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

pub struct PMat<'a> {
    pats: Vec<Vec<&'a Pat<'a>>>,
    exprs: Vec<&'a Expr<'a>>,
}

fn default_matrix<'a>(ctx: &'a mut Context<'a>, mat: &PMat<'a>) -> Expr<'a> {
    todo!()
}

pub fn match_compile<'a>(ctx: &'a mut Context<'a>) {
    todo!()
}

#[derive(Clone)]
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
    Leaf(Action<'a>),
    Switch(Switch<'a>),
    Fail,
}

#[derive(Debug)]
pub struct DecisionTree<'a> {
    nodes: Vec<Tree<'a>>,
}

#[derive(Clone, Debug)]
pub struct Action<'a> {
    variable_map: Rc<RefCell<HashMap<Symbol, Vec<Occurence<'a>>>>>,
    expr: Expr<'a>,
}

/// A column-oriented matrix
#[derive(Clone)]
pub struct Matrix<'a> {
    occs: Vec<Occurence<'a>>,
    patterns: Vec<Vec<&'a PatKind<'a>>>,
    exprs: Vec<Action<'a>>,

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

impl<'a> Action<'a> {
    fn new(expr: Expr<'a>) -> Action<'a> {
        Action {
            variable_map: Rc::new(RefCell::new(HashMap::new())),
            expr,
        }
    }

    fn add_var(&mut self, s: Symbol, o: Occurence<'a>) {}
}

impl<'arena> elaborate::Context<'arena> {
    pub(crate) fn build_decision_tree(&mut self, expr: Expr<'arena>, rules: &[Rule<'arena>]) {
        let mut matrix = Matrix {
            occs: vec![Occurence::Expr(expr)],
            patterns: rules.iter().map(|rule| vec![rule.pat.pat]).collect(),
            exprs: rules.iter().map(|rule| Action::new(rule.expr)).collect(),
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
            } else if fst.head() == Head::Wild {
                if let PatKind::Var(sym) = fst {
                    // TODO: Handle generation of fresh variables, and rewriting in expression
                    //
                    // is this the best place to handle this though? Also perhaps we want
                    // to eta-expand/close over all variables in `expr` that are bound
                    // in a pattern to make this step easier. e.g.
                    //      fun m x       [] = x    --> (fn a => a) x
                    //        | m (y::ys) xs = ys   --> (fn b => b) ys
                    // if head.arity() > 1 {
                    //     println!("binding {:?} to {:?} occurrences", sym, self.occs);
                    // }

                    println!("bind {:?} to {:?}", sym, self.occs[col]);
                    // if let Head::Record(_) =
                    expr.variable_map
                        .borrow_mut()
                        .insert(*sym, vec![self.occs[col].clone()]);
                }
                for _ in 0..head.arity() {
                    row.insert(col, self.wild);
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
        // dbg!(self);
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

    fn compile(&mut self) -> Tree<'a> {
        if self.patterns.is_empty() {
            Tree::Fail
        } else if self.patterns[0].iter().all(|pat| pat.head() == Head::Wild) {
            Tree::Leaf(self.exprs[0].clone())
        } else {
            let mut set = HashSet::new();
            let col = self.heuristic();

            for pat in self.col_iter(col) {
                set.insert(pat.head());
            }
            let wildcard = set.remove(&Head::Wild);

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

                let tree = mat.compile();
                branches.push((h, tree));
            }

            if !exhaustive {
                let mut mat = self.default_matrix();
                println!("default {:#?}", &mat);

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

impl<'a> Tree<'a> {
    fn pp(&self, depth: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = (0..depth).map(|_| '\t').collect::<String>();
        match self {
            Tree::Leaf(e) => write!(f, "{}{:#?}", s, e),
            Tree::Fail => write!(f, "{}FAIL", s),
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

impl<'a> std::fmt::Debug for Occurence<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Occurence::Expr(e) => write!(f, "root"),
            Occurence::Path(o, i) => write!(f, "{}.{}", o, i),
        }
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
            writeln!(f, "{:?} => {:?}", self.patterns[idx], self.exprs[idx])?;
        }
        write!(f, "")
    }
}
