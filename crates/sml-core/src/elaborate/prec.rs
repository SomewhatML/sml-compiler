use super::*;
use sml_frontend::parser::precedence::{Precedence, Query};

impl Query<ast::Pat> for &Context {
    fn fixity(&self, t: &ast::Pat) -> Fixity {
        match &t.data {
            ast::PatKind::Variable(s) => self.lookup_infix(s).unwrap_or(Fixity::Nonfix),
            _ => Fixity::Nonfix,
        }
    }

    fn infix(&self, a: ast::Pat, b: ast::Pat, c: ast::Pat) -> Result<ast::Pat, precedence::Error> {
        // We know `a` must be a symbol, since it has a Fixity!
        match a.data {
            ast::PatKind::Variable(s) => {
                let sp_bc = b.span + c.span;
                let sp = a.span + sp_bc;
                let rec = ast::Pat::new(ast::make_record_pat(vec![b, c]), sp_bc);
                Ok(ast::Pat::new(ast::PatKind::App(s, Box::new(rec)), sp))
            }
            _ => Err(precedence::Error::InvalidOperator),
        }
    }

    fn apply(&self, a: ast::Pat, b: ast::Pat) -> Result<ast::Pat, precedence::Error> {
        match a.data {
            ast::PatKind::Variable(s) => {
                let sp = a.span + b.span;
                Ok(ast::Pat::new(ast::PatKind::App(s, Box::new(b)), sp))
            }
            _ => Err(precedence::Error::InvalidOperator),
        }
    }
}

impl Query<ast::Expr> for &Context {
    fn fixity(&self, t: &ast::Expr) -> Fixity {
        match &t.data {
            ast::ExprKind::Var(s) => self.lookup_infix(s).unwrap_or(Fixity::Nonfix),
            _ => Fixity::Nonfix,
        }
    }

    fn infix(
        &self,
        a: ast::Expr,
        b: ast::Expr,
        c: ast::Expr,
    ) -> Result<ast::Expr, precedence::Error> {
        let sp_bc = b.span + c.span;
        let sp = a.span + sp_bc;
        let rec = ast::Expr::new(ast::make_record(vec![b, c]), sp_bc);
        Ok(ast::Expr::new(
            ast::ExprKind::App(Box::new(a), Box::new(rec)),
            sp,
        ))
    }
    fn apply(&self, a: ast::Expr, b: ast::Expr) -> Result<ast::Expr, precedence::Error> {
        let sp = a.span + b.span;
        Ok(ast::Expr::new(
            ast::ExprKind::App(Box::new(a), Box::new(b)),
            sp,
        ))
    }
}

impl Context {
    pub(crate) fn expr_precedence(
        &self,
        exprs: Vec<ast::Expr>,
        sp: Span,
    ) -> Result<ast::Expr, precedence::Error> {
        Precedence::run(self, exprs)
    }

    pub(crate) fn pat_precedence(
        &self,
        exprs: Vec<ast::Pat>,
        sp: Span,
    ) -> Result<ast::Pat, precedence::Error> {
        Precedence::run(self, exprs)
    }
}
