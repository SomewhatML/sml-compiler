use crate::arenas::CoreArena;
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord};
use sml_util::diagnostics::Diagnostic;
use sml_util::hasher::IntHashMap;
use sml_util::interner::Symbol;
use sml_util::pretty_print::PrettyPrinter;
use sml_util::span::Span;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

/// A [`Hash`] implementation that ignores type variables. This really shouldn't
/// be used anywhere outside of the monomorphization code
impl<'a> Hash for Type<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self {
            Type::Var(tv) => match tv.ty() {
                Some(ty) => ty.hash(state),
                None => tv.id.hash(state),
            },
            Type::Flex(tv) => match tv.ty() {
                Some(ty) => ty.hash(state),
                None => 0.hash(state),
            },
            Type::Con(tc, vars) => {
                tc.hash(state);
                vars.iter().for_each(|ty| ty.hash(state))
            }
            Type::Record(fields) => fields.iter().for_each(|f| f.data.hash(state)),
        }
    }
}

/// A [`PartialEq`] implementation that ignores type variables. This really shouldn't
/// be used anywhere outside of the monomorphization code
impl<'a> Eq for Type<'a> {}
impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (&self, other) {
            (Type::Var(a), Type::Var(b)) => match (a.ty(), b.ty()) {
                (Some(a), Some(b)) => a == b,
                (Some(_), None) => false,
                (None, Some(_)) => false,
                (None, None) => a.id == b.id,
            },
            (Type::Flex(a), Type::Flex(b)) => match (a.ty(), b.ty()) {
                (Some(a), Some(b)) => a == b,
                (Some(_), None) => false,
                (None, Some(_)) => false,
                (None, None) => a
                    .constraints
                    .iter()
                    .zip(b.constraints.iter())
                    .all(|(a, b)| a.label == b.label && a.data == b.data),
            },
            (Type::Con(a, b), Type::Con(c, d)) => a == c && b == d,
            (Type::Record(a), Type::Record(b)) => a
                .iter()
                .zip(b.iter())
                .all(|(a, b)| a.label == b.label && a.data == b.data),
            _ => false,
        }
    }
}

#[derive(Clone)]
pub struct Entry<'a> {
    /// Relate each instantiation of a type to a fresh name
    usages: HashMap<Vec<&'a Type<'a>>, Symbol>,
    tyvars: Vec<usize>,
}

pub struct Mono<'a> {
    arena: &'a CoreArena<'a>,
    stack: Vec<Namespace>,
    cache: HashMap<Symbol, Entry<'a>>,
    diags: Vec<Diagnostic>,
    id: Cell<u32>,
}

#[derive(Default)]
pub struct Namespace {
    types: HashMap<Symbol, Symbol>,
    values: HashMap<Symbol, Symbol>,
}

pub struct Program<'a> {
    datatypes: Vec<crate::Datatype<'a>>,
    exceptions: Vec<(Constructor, Option<&'a Type<'a>>)>,
    body: Expr<'a>,
}

impl<'a> Mono<'a> {
    pub fn mono_decl(&mut self, decl: &Decl<'a>) -> Decl<'a> {
        match decl {
            Decl::Datatype(datatypes) => todo!(),
            Decl::Fun(tvs, funs) => todo!(),
            Decl::Val(tvs, name, expr) => todo!(),
            Decl::Exn(con, ty) => Decl::Exn(*con, *ty),
        }
    }
}
