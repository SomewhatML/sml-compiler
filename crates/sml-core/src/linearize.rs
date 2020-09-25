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
use crate::{Decl, Expr, ExprKind};
use sml_util::span::Span;

pub fn run<'a>(arena: &'a CoreArena<'a>, decls: &[Decl<'a>]) -> Expr<'a> {
    let mut lin = Linearize { arena };
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

use super::visit::Visitor;

impl<'a> Visitor<'a> for Linearize<'a> {
    fn arena(&self) -> &'a crate::arenas::CoreArena<'a> {
        self.arena
    }

    fn visit_type(&mut self, ty: &'a crate::types::Type<'a>) -> &'a crate::types::Type<'a> {
        ty
    }
    fn visit_expr_let(&mut self, decls: &[Decl<'a>], body: Expr<'a>) -> ExprKind<'a> {
        let mut decls = decls
            .iter()
            .map(|d| self.visit_decl(d))
            .rev()
            .collect::<Vec<_>>();

        let last = decls.pop().unwrap();
        let body = self.visit_expr(body);
        let new = decls.into_iter().rev().fold(body, |body, decl| {
            let lett = self.arena.exprs.alloc(ExprKind::Let(vec![decl], body));
            Expr::new(lett, body.ty, body.span)
        });
        ExprKind::Let(vec![last], new)
    }
}
