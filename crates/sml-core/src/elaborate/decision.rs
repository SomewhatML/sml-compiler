use super::*;

#[derive(Debug)]
pub struct Switch<'a> {
    occurence: &'a Expr,
    list: Vec<usize>,
}

#[derive(Debug)]
pub enum Tree<'a> {
    Leaf(&'a Expr),
    Switch(Switch<'a>),
    Fail,
}

#[derive(Debug)]
pub struct DecisionTree<'a> {
    nodes: Vec<Switch<'a>>,
}

/// A column-oriented matrix
#[derive(Debug)]
pub struct Matrix<'a> {
    patterns: Vec<Vec<Pat>>,
    exprs: Vec<&'a Expr>,
}

fn find_record_field<T>(rows: &[Row<T>], label: Symbol) -> Option<&T> {
    for row in rows {
        if row.label == label {
            return Some(&row.data);
        }
    }
    None
}

fn deconstruct_record(ty: &[Row<Type>], pat: &[Row<Pat>]) -> Vec<Pat> {
    let mut v = Vec::new();
    for row in ty {
        let p = match find_record_field(&pat, row.label) {
            Some(p) => p.clone(),
            None => Pat::new(PatKind::Wild, row.data.clone(), Span::dummy()),
        };
        v.push(p);
    }
    v
}

fn expand_pat<'a>(pat: &'a Pat, v: &mut Vec<&'a Pat>) {
    match &pat.pat {
        PatKind::Record(rows) => {
            for row in rows {
                expand_pat(&row.data, v);
            }
        }
        // PatKind::App(constr, Some(pat)) => {
        //     let mut inner = Vec::new();
        // },
        _ => v.push(pat),
    }
}

// impl<'a> Matrix<'a> {
//     pub fn special(&self, con: Constructor, arity: usize) -> Matrix<'a> {

//     }
// }

impl Context {
    pub(crate) fn build_decision_tree(&self, expr: &Expr, rules: &[Rule]) {
        // let patterns = match &expr.ty {
        //     Type::Record(rho) => {
        //         let mut pats: Vec<Vec<Pat>> = (0..rho.len()).map(|_| Vec::with_capacity(rules.len())).collect();
        //         for rule in rules {
        //             match &rule.pat.pat {
        //                 PatKind::Record(p) => {
        //                     for (idx, p) in deconstruct_record(rho, p).into_iter().enumerate() {
        //                         pats[idx].push(p);
        //                     }
        //                 }
        //                 _ => {
        //                     panic!("internal compiler bug, invalid pattern type checking!")
        //                 }
        //             }
        //         }
        //         pats
        //     },
        //     _ => vec![rules.iter().cloned().map(|rule| rule.pat).collect()]
        // };

        let mut patterns = Vec::new();
        for rule in rules {
            let mut row = Vec::new();
            expand_pat(&rule.pat, &mut row);
            for (idx, pat) in row.into_iter().enumerate() {
                if patterns.len() <= idx {
                    patterns.push(Vec::with_capacity(rules.len()));
                }
                patterns[idx].push(pat.clone());
            }
        }

        let mut matrix = Matrix {
            patterns,
            exprs: rules.iter().map(|rule| &rule.expr).collect(),
        };

        dbg!(&matrix);
    }
}
