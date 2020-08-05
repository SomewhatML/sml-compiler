#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::elaborate::{Context, ElabError, ErrorKind};
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord};
use sml_util::interner::Symbol;
use sml_util::span::Span;
use sml_util::Const;
use std::{cell::Cell, collections::HashMap};

pub struct Rename {
    stack: Vec<Namespace>,
    id: u32,
}

#[derive(Default)]
pub struct Namespace {
    types: HashMap<Symbol, Symbol>,
    values: HashMap<Symbol, Symbol>,
}

impl Rename {
    // pub fn register(&mut self, name: Symbol, decl: )

    pub fn new() -> Rename {
        Rename {
            stack: vec![Namespace::default()],
            id: 0,
        }
    }

    pub fn enter(&mut self) {
        self.stack.push(Namespace::default())
    }

    pub fn leave(&mut self) {
        self.stack.pop();
    }

    pub fn register_type(&mut self, sym: Symbol) -> Symbol {
        let id = self.id;
        self.id += 1;
        self.stack
            .last_mut()
            .unwrap()
            .types
            .insert(sym, Symbol::gensym(id));
        Symbol::gensym(id)
    }

    pub fn register_val(&mut self, sym: Symbol) -> Symbol {
        let id = self.id;
        self.id += 1;
        self.stack
            .last_mut()
            .unwrap()
            .values
            .insert(sym, Symbol::gensym(id));
        Symbol::gensym(id)
    }

    pub fn swap_type(&self, sym: Symbol) -> Option<Symbol> {
        match sym {
            Symbol::Interned(_) | Symbol::Gensym(_) => {
                let mut ptr = self.stack.len().saturating_sub(1);
                while let Some(ns) = self.stack.get(ptr) {
                    match ns.types.get(&sym).copied() {
                        Some(swap) => return Some(swap),
                        None => ptr = ptr.checked_sub(1)?,
                    }
                }
                None
            }
            _ => Some(sym),
        }
    }

    pub fn swap_value(&self, sym: Symbol) -> Option<Symbol> {
        match sym {
            Symbol::Interned(_) | Symbol::Gensym(_) => {
                let mut ptr = self.stack.len().saturating_sub(1);
                while let Some(ns) = self.stack.get(ptr) {
                    match ns.values.get(&sym).copied() {
                        Some(swap) => return Some(swap),
                        None => ptr = ptr.checked_sub(1)?,
                    }
                }
                None
            }
            _ => Some(sym),
        }
    }

    pub fn visit_decl<'a>(&mut self, decl: Decl<'a>) -> Decl<'a> {
        match decl {
            Decl::Val(_, Rule { pat, expr }) => {
                self.visit_pat(&pat);
                self.visit_expr(&expr);
                decl
            }
            Decl::Fun(vars, funs) => {
                let funs = funs
                    .into_iter()
                    .map(|(sym, mut lam)| {
                        let sym = self.register_val(sym);
                        self.enter();
                        lam.arg = self.register_val(lam.arg);
                        self.visit_expr(&lam.body);
                        self.leave();
                        (sym, lam)
                    })
                    .collect();

                Decl::Fun(vars, funs)
            }
            Decl::Datatype(mut dt) => {
                dt.tycon.name = self.register_type(dt.tycon.name);
                dt.constructors = dt
                    .constructors
                    .into_iter()
                    .map(|(mut con, ty)| {
                        con.name = self.register_val(con.name);
                        (con, ty)
                    })
                    .collect();

                Decl::Datatype(dt)
            }
            Decl::Exn(mut con, ty) => {
                con.name = self.register_val(con.name);
                Decl::Exn(con, ty)
            }
            _ => decl,
        }
    }

    pub fn visit_pat(&mut self, pat: &Pat<'_>) {
        match pat.kind {
            PatKind::App(con, Some(pat)) => {
                let mut inner = con.get();
                inner.name = self
                    .swap_value(inner.name)
                    .expect("BUG: Rename::PatKind::App");
                con.set(inner);
                self.visit_pat(pat);
            }
            PatKind::App(con, None) => {
                let mut inner = con.get();
                inner.name = self
                    .swap_value(inner.name)
                    .expect("BUG: Rename::PatKind::App");
                con.set(inner);
            }
            PatKind::Const(_) => {}
            PatKind::Record(fields) => {
                for field in fields.iter() {
                    self.visit_pat(&field.data);
                }
            }
            PatKind::Var(sym) => {
                let inner = sym.get();
                self.register_val(inner);
                sym.set(self.swap_value(inner).expect("BUG"));
            }
            PatKind::Wild => {}
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
                    self.enter();
                    self.visit_pat(&rule.pat);
                    self.visit_expr(&rule.expr);
                    self.leave();
                }
            }
            ExprKind::Con(con, tys) => {}
            ExprKind::Const(c) => {}
            ExprKind::Handle(tryy, sym, handler) => {
                self.visit_expr(tryy);
                self.visit_expr(handler);
            }
            ExprKind::Lambda(lam) => {
                let mut inner = lam.get();
                self.enter();
                self.register_val(inner.arg);
                inner.arg = self.swap_value(inner.arg).expect("BUG");
                lam.set(inner);
                self.visit_expr(&inner.body);
                self.leave();
            }
            ExprKind::Let(decls, body) => {
                self.enter();
                for decl in decls {
                    // self.visit_decl(decl);
                }
                self.visit_expr(body);
                self.leave();
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
                let inner = s.get();
                s.set(self.swap_value(inner).expect("BUG"));
            }
        }
    }
}
