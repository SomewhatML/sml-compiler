#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::elaborate::{Context, ElabError, ErrorKind};
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord};
use sml_util::interner::Symbol;
use sml_util::span::Span;
use sml_util::Const;
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
    pub fn visit_decl(&mut self, decl: &Decl<'a>) {
        match decl {
            Decl::Val(Rule { pat, expr }) => {
                self.visit_expr(expr);
            }
            Decl::Fun(_, funs) => {
                for (name, lam) in funs {
                    self.visit_expr(&lam.body);
                }
            }
            _ => {}
        }
    }
    pub fn visit_expr(&mut self, expr: &Expr<'a>) {
        match expr.kind {
            ExprKind::App(e1, e2) => {
                self.visit_expr(e1);
                self.visit_expr(e2);
            }
            ExprKind::Case(casee, rules) => {
                self.visit_expr(casee);
                for rule in rules {
                    self.visit_expr(&rule.expr);
                }
            }
            ExprKind::Con(con, tys) => {}
            ExprKind::Const(c) => {}
            ExprKind::Handle(tryy, sym, handler) => {
                self.visit_expr(tryy);
                self.visit_expr(handler);
            }
            ExprKind::Lambda(lam) => {
                self.visit_expr(&lam.body);
            }
            ExprKind::Let(decls, body) => {
                for decl in decls {}
                self.visit_expr(body);
            }
            ExprKind::List(exprs) => {
                for expr in exprs {
                    self.visit_expr(expr);
                }
            }
            ExprKind::Primitive(sym) => {}
            ExprKind::Raise(e) => {
                self.visit_expr(e);
            }
            ExprKind::Record(rows) => {
                for expr in rows {
                    self.visit_expr(&expr.data);
                }
            }
            ExprKind::Seq(exprs) => {
                for expr in exprs {
                    self.visit_expr(expr);
                }
            }
            ExprKind::Var(s) => {
                // s.set(Symbol::Gensym(0));
            }
        }
    }
}
