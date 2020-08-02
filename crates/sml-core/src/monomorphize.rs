#![allow(dead_code)]
use super::*;

pub struct Cache<'a> {
    defs: HashMap<Symbol, CacheEntry<'a>>,
    names: Vec<HashMap<Symbol, Symbol>>,
}

pub struct CacheEntry<'a> {
    usages: HashMap<&'a Type<'a>, Symbol>,
}
