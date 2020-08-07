#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use crate::arenas::CoreArena;
use crate::elaborate::{Context, ElabError, ErrorKind};
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord};
use sml_util::interner::Symbol;
use sml_util::span::Span;
use sml_util::Const;
use std::{cell::Cell, collections::HashMap};

pub struct Entry {
    name: Symbol,
    tyvars: Vec<usize>,
    // usages:
}

pub struct Monomorphizer {}

pub struct Rename<'a> {
    pub decls: Vec<Decl<'a>>,
    arena: &'a CoreArena<'a>,
    stack: Vec<Namespace>,
    id: u32,
}

#[derive(Default)]
pub struct Namespace {
    types: HashMap<Symbol, Symbol>,
    values: HashMap<Symbol, Symbol>,
}

impl<'a> Rename<'a> {
    // pub fn register(&mut self, name: Symbol, decl: )

    pub fn new(arena: &'a CoreArena<'a>) -> Rename<'a> {
        Rename {
            decls: Vec::default(),
            arena,
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

    #[inline]
    pub fn fresh(&mut self) -> Symbol {
        let id = self.id;
        self.id += 1;
        Symbol::gensym(id)
    }

    pub fn register_type(&mut self, sym: Symbol) -> Symbol {
        let fresh = self.fresh();
        self.stack.last_mut().unwrap().types.insert(sym, fresh);
        fresh
    }

    pub fn register_val(&mut self, sym: Symbol) -> Symbol {
        let fresh = self.fresh();
        self.stack.last_mut().unwrap().values.insert(sym, fresh);
        fresh
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

    pub fn visit_decl(&mut self, decl: &Decl<'a>) -> Decl<'a> {
        match decl {
            Decl::Val(vars, Rule { pat, expr }) => {
                let pat = self.visit_pat(&pat);
                let expr = self.visit_expr(&expr);

                Decl::Val(vars.clone(), Rule { pat, expr })
            }
            Decl::Fun(vars, funs) => {
                let funs = funs
                    .into_iter()
                    .map(|(sym, mut lam)| {
                        let sym = self.register_val(*sym);
                        self.enter();
                        lam.arg = self.register_val(lam.arg);
                        lam.ty = self.visit_type(lam.ty);
                        lam.body = self.visit_expr(&lam.body);
                        self.leave();
                        (sym, lam)
                    })
                    .collect();

                Decl::Fun(vars.clone(), funs)
            }
            Decl::Datatype(dts) => {
                for dt in dts {
                    self.register_type(dt.tycon.name);
                }

                Decl::Datatype(
                    dts.iter()
                        .map(|dt| {
                            let mut dt = dt.clone();
                            dt.tycon.name = self.swap_type(dt.tycon.name).unwrap();
                            dt.constructors = dt
                                .constructors
                                .into_iter()
                                .map(|(mut con, ty)| {
                                    con.name = self.register_val(con.name);
                                    con.tycon =
                                        self.swap_type(con.tycon).expect("BUG: Decl::Datatype");
                                    (con, ty)
                                })
                                .collect();
                            dt
                        })
                        .collect(),
                )
            }
            Decl::Exn(con, ty) => {
                let mut con = *con;
                con.name = self.register_val(con.name);
                // con.tycon should be EXN
                let ty = ty.map(|ty| self.visit_type(ty));
                Decl::Exn(con, ty)
            }
        }
    }

    fn visit_type(&mut self, ty: &'a Type<'a>) -> &'a Type<'a> {
        match ty {
            Type::Var(tyvar) => match tyvar.ty() {
                Some(ty) => self.visit_type(ty),
                None => {
                    // emit warning for unused type variable
                    self.arena.types.unit()
                }
            },
            Type::Record(fields) => {
                let args = SortedRecord::new_unchecked(
                    fields
                        .iter()
                        .map(|row| row.fmap(|ty| self.visit_type(ty)))
                        .collect(),
                );
                self.arena.types.alloc(Type::Record(args))
            }
            Type::Flex(flex) => match flex.ty() {
                Some(ty) => self.visit_type(ty),
                None => {
                    // emit warning for unused type variable
                    self.arena.types.unit()
                }
            },
            Type::Con(mut con, args) => {
                con.name = self.swap_type(con.name).expect("BUG: Type::Con");
                self.arena.types.alloc(Type::Con(
                    con,
                    args.iter().map(|ty| self.visit_type(ty)).collect(),
                ))
            }
        }
    }

    fn visit_pat(&mut self, pat: &Pat<'a>) -> Pat<'a> {
        let kind = match pat.kind {
            PatKind::App(mut con, Some(pat)) => {
                con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
                con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
                PatKind::App(con, Some(self.visit_pat(pat)))
            }
            PatKind::App(mut con, None) => {
                con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
                con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
                PatKind::App(con, None)
            }
            PatKind::Const(c) => PatKind::Const(*c),
            PatKind::Record(fields) => PatKind::Record(SortedRecord::new_unchecked(
                fields
                    .iter()
                    .map(|row| row.fmap(|pat| self.visit_pat(pat)))
                    .collect(),
            )),
            PatKind::Var(sym) => PatKind::Var(self.register_val(*sym)),
            PatKind::Wild => PatKind::Var(self.fresh()),
        };
        Pat::new(
            self.arena.pats.alloc(kind),
            self.visit_type(pat.ty),
            pat.span,
        )
    }

    fn visit_expr(&mut self, expr: &Expr<'a>) -> Expr<'a> {
        let kind = match expr.kind {
            ExprKind::App(e1, e2) => {
                let e1 = self.visit_expr(e1);
                let e2 = self.visit_expr(e2);
                ExprKind::App(e1, e2)
            }
            ExprKind::Case(casee, rules) => {
                let (var, ty) = casee;
                let var = self.swap_value(*var).expect("BUG: ExprKind::Case");
                let ty = self.visit_type(ty);

                let rules = rules
                    .iter()
                    .map(|rule| {
                        self.enter();
                        let pat = self.visit_pat(&rule.pat);
                        let expr = self.visit_expr(&rule.expr);
                        self.leave();
                        Rule { pat, expr }
                    })
                    .collect();

                ExprKind::Case((var, ty), rules)
            }
            ExprKind::Con(mut con, tys) => {
                con.name = self.swap_value(con.name).expect("BUG: ExprKind::Con");
                con.tycon = self.swap_type(con.tycon).expect("BUG: ExprKind::Con");
                ExprKind::Con(con, tys.iter().map(|ty| self.visit_type(ty)).collect())
            }
            ExprKind::Const(c) => ExprKind::Const(*c),
            ExprKind::Handle(tryy, sym, handler) => {
                let tryy = self.visit_expr(tryy);
                let sym = self.swap_value(*sym).expect("BUG: ExprKind::Handle");
                let handler = self.visit_expr(handler);
                ExprKind::Handle(tryy, sym, handler)
            }
            ExprKind::Lambda(lam) => {
                let mut lam = *lam;
                self.enter();
                lam.arg = self.register_val(lam.arg);
                lam.ty = self.visit_type(lam.ty);
                lam.body = self.visit_expr(&lam.body);
                self.leave();
                ExprKind::Lambda(lam)
            }
            ExprKind::Let(decls, body) => {
                self.enter();
                let decls = decls.iter().map(|d| self.visit_decl(d)).collect();
                let body = self.visit_expr(body);
                self.leave();
                ExprKind::Let(decls, body)
            }
            ExprKind::List(exprs) => {
                ExprKind::List(exprs.iter().map(|e| self.visit_expr(e)).collect())
            }
            ExprKind::Primitive(sym) => ExprKind::Primitive(*sym),
            ExprKind::Raise(e) => ExprKind::Raise(self.visit_expr(e)),
            ExprKind::Record(rows) => ExprKind::Record(
                rows.iter()
                    .map(|row| row.fmap(|ex| self.visit_expr(ex)))
                    .collect(),
            ),
            ExprKind::Seq(exprs) => {
                ExprKind::Seq(exprs.iter().map(|e| self.visit_expr(e)).collect())
            }
            ExprKind::Var(s) => ExprKind::Var(self.swap_value(*s).expect("BUG")),
        };
        Expr::new(
            self.arena.exprs.alloc(kind),
            self.visit_type(expr.ty),
            expr.span,
        )
    }
}
