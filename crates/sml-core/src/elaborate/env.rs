use super::*;
use std::collections::HashMap;

pub struct Namespace {
    parent: Option<usize>,
    types: HashMap<Symbol, TypeId>,
    exprs: HashMap<Symbol, ExprId>,
}
