use super::*;

pub enum Occurence {
    Var(Symbol),
    Path(Box<Occurence>, usize),
}

#[derive(Debug)]
pub struct Switch<'ar> {
    occurence: Expr<'ar>,
    list: Vec<usize>,
}

#[derive(Debug)]
pub enum Tree<'ar> {
    Leaf(Expr<'ar>),
    Switch(Switch<'ar>),
    Fail,
}

#[derive(Debug)]
pub struct DecisionTree<'a> {
    nodes: Vec<Switch<'a>>,
}

/// A column-oriented matrix
#[derive(Debug)]
pub struct Matrix<'ar> {
    patterns: Vec<Vec<Pat<'ar>>>,
    exprs: Vec<Expr<'ar>>,
}

fn find_record_field<T>(rows: &[Row<T>], label: Symbol) -> Option<&T> {
    for row in rows {
        if row.label == label {
            return Some(&row.data);
        }
    }
    None
}

fn expand_pat<'ar>(pat: Pat<'ar>, v: &mut Vec<Pat<'ar>>) {
    match &pat.pat {
        PatKind::Record(rows) => {
            for row in rows.iter() {
                expand_pat(row.data, v);
            }
        }
        _ => v.push(pat),
    }
}

impl<'ar> elaborate::Context<'ar> {
    pub(crate) fn build_decision_tree(&self, expr: &Expr<'ar>, rules: &[Rule<'ar>]) {
        let mut patterns = Vec::new();
        for rule in rules {
            let mut row = Vec::new();
            expand_pat(rule.pat, &mut row);
            for (idx, pat) in row.into_iter().enumerate() {
                if patterns.len() <= idx {
                    patterns.push(Vec::with_capacity(rules.len()));
                }
                patterns[idx].push(pat.clone());
            }
        }

        let mut matrix = Matrix {
            patterns,
            exprs: rules.iter().map(|rule| rule.expr).collect(),
        };

        dbg!(&matrix);
    }
}
