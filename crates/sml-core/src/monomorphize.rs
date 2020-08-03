#![allow(dead_code)]
use super::*;

#[derive(Default)]
pub struct Cache<'a> {
    defs: HashMap<Symbol, CacheEntry<'a>>,
    names: Vec<HashMap<Symbol, Symbol>>,
}

pub struct CacheEntry<'a> {
    usages: HashMap<&'a Type<'a>, Symbol>,
}
