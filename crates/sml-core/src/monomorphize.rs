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
