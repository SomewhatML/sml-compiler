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
pub struct Cache {
    types: Vec<HashMap<Symbol, Symbol>>,
    values: Vec<HashMap<Symbol, Symbol>>,
    id: u32,
}

impl Cache {
    // pub fn register(&mut self, name: Symbol, decl: )

    pub fn enter(&mut self) {
        self.types.push(HashMap::new())
    }

    pub fn leave(&mut self) {
        self.types.pop();
    }

    pub fn register_type(&mut self, sym: Symbol) -> Symbol {
        let id = self.id;
        self.id += 1;
        self.types.last_mut().unwrap().insert(sym, Symbol::gensym(id));
        Symbol::gensym(id)
    }

    pub fn register_val(&mut self, sym: Symbol) -> Symbol {
        let id = self.id;
        self.id += 1;
        self.values.last_mut().unwrap().insert(sym, Symbol::gensym(id));
        Symbol::gensym(id)
    }

    pub fn lookup_type(&self, sym: &Symbol) -> Symbol {
        *self.types.last().unwrap().get(sym).expect("BUG: Rename::lookup_type")
    }

    pub fn lookup_value(&self, sym: &Symbol) -> Symbol {
        *self.values.last().unwrap().get(sym).expect("BUG: Rename::lookup_type")
    }


    pub fn visit_decl(&mut self, decl: &Decl<'_>) {
        match decl {
            Decl::Val(_, Rule { pat, expr }) => {
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
    pub fn visit_expr(&mut self, expr: &Expr<'_>) {
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
