use super::*;
use std::collections::HashMap;

pub struct Namespace {
    parent: Option<usize>,
    // types: HashMap<String, CoreId>
}
