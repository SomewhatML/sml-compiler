#![allow(dead_code)]
#![allow(unused_imports)]
use crate::elaborate::{Context, ElabError, ErrorKind};
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord};
use sml_frontend::ast::Const;
use sml_util::interner::Symbol;
use sml_util::span::Span;
use std::collections::HashMap;

#[derive(Default)]
pub struct Cache<'a> {
    defs: HashMap<Symbol, CacheEntry<'a>>,
    names: Vec<HashMap<Symbol, Symbol>>,
}

pub struct CacheEntry<'a> {
    usages: HashMap<&'a Type<'a>, Symbol>,
}

impl<'a> Cache<'a> {
    pub fn visit_expr(&mut self, expr: Expr<'a>) -> Expr<'a> {
        match expr.kind {
            ExprKind::App(e1, e2) => todo!(),
            ExprKind::Case(casee, rules) => todo!(),
            ExprKind::Con(con, tys) => todo!(),
            ExprKind::Const(c) => todo!(),
            ExprKind::Handle(tryy, sym, handler) => todo!(),
            ExprKind::Lambda(lam) => todo!(),
            ExprKind::Let(decls, body) => todo!(),
            ExprKind::List(exprs) => todo!(),
            ExprKind::Primitive(sym) => todo!(),
            ExprKind::Raise(e) => todo!(),
            ExprKind::Record(rows) => todo!(),
            ExprKind::Seq(exprs) => todo!(),
            ExprKind::Var(s) => todo!(),
        }
    }
}
