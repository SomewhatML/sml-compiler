//! Small pass to perform linearization of programs such that all let expressions
//! have one declaration, and all declarations are nested
//! ```sml
//! val x = 10
//! val y = 12
//! val q = (x, y)
//! ```
//! becomes
//! ```sml
//! val program = let val x = 10 in let val y = 12 in let val q = (x, y) in () end end end
//! ```

use crate::arenas::CoreArena;
use crate::{Decl, Expr, ExprKind, Rule};
use sml_util::span::Span;

pub fn run<'a>(arena: &'a CoreArena<'a>, decls: &[Decl<'a>]) -> Expr<'a> {
    let mut lin = Linearize::new(arena);
    let body = Expr::new(
        arena.exprs.alloc(ExprKind::Const(sml_util::Const::Unit)),
        arena.types.unit(),
        Span::dummy(),
    );
    decls.into_iter().rev().fold(body, |body, decl| {
        let lett = arena
            .exprs
            .alloc(ExprKind::Let(vec![lin.visit_decl(decl)], body));
        Expr::new(lett, body.ty, body.span)
    })
}

pub struct Linearize<'a> {
    arena: &'a CoreArena<'a>,
}

impl<'a> Linearize<'a> {
    pub fn new(arena: &'a CoreArena<'a>) -> Linearize<'a> {
        Linearize { arena }
    }

    pub fn visit_decl(&mut self, decl: &Decl<'a>) -> Decl<'a> {
        match decl {
            Decl::Val(vars, sym, expr) => {
                let expr = self.visit_expr(&expr);
                Decl::Val(vars.clone(), *sym, expr)
            }
            Decl::Fun(vars, funs) => {
                let funs = funs
                    .into_iter()
                    .map(|(sym, lam)| {
                        let mut lam = *lam;
                        lam.body = self.visit_expr(&lam.body);
                        (*sym, lam)
                    })
                    .collect();
                Decl::Fun(vars.clone(), funs)
            }
            Decl::Exn(con, arg) => Decl::Exn(*con, *arg),
            Decl::Datatype(dts) => Decl::Datatype(dts.clone()),
        }
    }

    pub fn visit_expr(&mut self, expr: &Expr<'a>) -> Expr<'a> {
        let kind = match expr.kind {
            ExprKind::App(e1, e2) => ExprKind::App(self.visit_expr(e1), self.visit_expr(e2)),
            ExprKind::Case(casee, rules) => {
                let rules = rules
                    .iter()
                    .map(|rule| Rule {
                        pat: rule.pat,
                        expr: self.visit_expr(&rule.expr),
                    })
                    .collect();

                ExprKind::Case(*casee, rules)
            }
            ExprKind::Handle(tryy, sym, handler) => {
                let tryy = self.visit_expr(tryy);
                let handler = self.visit_expr(handler);
                ExprKind::Handle(tryy, *sym, handler)
            }
            ExprKind::Lambda(lam) => {
                let mut lam = *lam;
                lam.body = self.visit_expr(&lam.body);
                ExprKind::Lambda(lam)
            }
            ExprKind::Let(decls, body) => {
                let decls = decls.iter().map(|d| self.visit_decl(d)).collect::<Vec<_>>();
                let body = self.visit_expr(body);
                let new = decls.into_iter().rev().fold(body, |body, decl| {
                    let lett = self.arena.exprs.alloc(ExprKind::Let(vec![decl], body));
                    Expr::new(lett, body.ty, body.span)
                });
                return new;
            }
            ExprKind::List(exprs) => {
                ExprKind::List(exprs.iter().map(|e| self.visit_expr(e)).collect())
            }
            ExprKind::Raise(e) => ExprKind::Raise(self.visit_expr(e)),
            ExprKind::Record(rows) => ExprKind::Record(
                rows.iter()
                    .map(|row| row.fmap(|ex| self.visit_expr(ex)))
                    .collect(),
            ),
            ExprKind::Selector(ex, label) => ExprKind::Selector(self.visit_expr(ex), *label),
            ExprKind::Seq(exprs) => {
                ExprKind::Seq(exprs.iter().map(|e| self.visit_expr(e)).collect())
            }
            ExprKind::Const(c) => ExprKind::Const(*c),
            ExprKind::Primitive(p) => ExprKind::Primitive(*p),
            ExprKind::Con(a, args) => ExprKind::Con(*a, args.clone()),
            ExprKind::Var(a, args) => ExprKind::Var(*a, args.clone()),
        };
        Expr::new(self.arena.exprs.alloc(kind), expr.ty, expr.span)
    }
}
