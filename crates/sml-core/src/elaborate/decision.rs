use super::*;

pub struct Node<'a> {
    test: &'a Expr,
    branches: Vec<usize>,
    exhaustive: bool,
}

pub struct DecisionTree<'a> {
    nodes: Vec<Node<'a>>,
}

impl Context {
    fn build_decision_tree(&self, expr: &Expr, rules: &[Rule]) {
        for rule in rules {}
    }
}
