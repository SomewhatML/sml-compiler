use super::*;

impl<'s, 'sym> Parser<'s, 'sym> {
    fn record_row(&mut self) -> Result<Field, Error> {
        let mut span = self.current.span;
        let label = self.expect_id()?;
        self.expect(Token::Equals)?;
        let expr = self.once(|p| p.parse_expr(), "missing expr in record row")?;
        span += self.prev;
        Ok(Field { label, expr, span })
    }

    fn record_expr(&mut self) -> Result<ExprKind, Error> {
        self.expect(Token::LBrace)?;
        let fields = self.delimited(|p| p.record_row(), Token::Comma)?;
        self.expect(Token::RBrace)?;
        Ok(ExprKind::Record(fields))
    }

    fn let_binding(&mut self) -> Result<ExprKind, Error> {
        self.expect(Token::Let)?;
        let decls = self.plus(
            |p| {
                let d = p.parse_decl();
                p.bump_if(Token::Semi);
                d
            },
            None,
        )?;
        self.expect(Token::In)?;
        let t2 = self.once(|p| p.parse_expr(), "let body required")?;
        self.expect(Token::End)?;
        Ok(ExprKind::Let(decls, Box::new(t2)))
    }

    fn case_arm(&mut self) -> Result<Arm, Error> {
        let pat = self.once(|p| p.parse_pattern(), "missing pattern in case arm")?;
        self.expect(Token::DArrow)?;
        let expr = self.once(|p| p.parse_expr(), "missing expression in case arm")?;
        self.bump_if(Token::Comma);
        Ok(Arm {
            span: pat.span + expr.span,
            pat,
            expr,
        })
    }

    fn case_expr(&mut self) -> Result<ExprKind, Error> {
        self.expect(Token::Case)?;
        let expr = self.once(|p| p.parse_expr(), "missing case expression")?;
        self.expect(Token::Of)?;
        self.bump_if(Token::Bar);
        let arms = self.delimited(|p| p.case_arm(), Token::Bar)?;
        self.expect(Token::End)?;
        Ok(ExprKind::Case(Box::new(expr), arms))
    }

    fn lambda_expr(&mut self) -> Result<ExprKind, Error> {
        self.expect(Token::Fn)?;
        let arg = self.once(
            |p| p.parse_pattern(),
            "expected pattern binding in lambda expression!",
        )?;
        self.expect(Token::DArrow)?;
        let body = self.parse_expr()?;
        Ok(ExprKind::Abs(Box::new(arg), Box::new(body)))
    }

    pub(crate) fn constant(&mut self) -> Result<Const, Error> {
        match self.bump() {
            Token::Const(c) => Ok(c),
            _ => self.error(ErrorKind::Internal),
        }
    }

    /// atexp ::=   constant
    ///             id
    ///             { [label = exp] }
    ///             ()
    ///             ( exp, ... expN )
    ///             ( exp )
    ///             let decl in exp, ... expN end
    fn atomic_expr(&mut self) -> Result<Expr, Error> {
        let mut span = self.current.span;
        match self.current.data {
            Token::Id(_) | Token::IdS(_) => {
                self.expect_id().map(|e| Expr::new(ExprKind::Var(e), span))
            }
            Token::LBrace => self.spanned(|p| p.record_expr()),
            Token::Let => self.spanned(|p| p.let_binding()),
            Token::Const(_) => self.constant().map(|l| Expr::new(ExprKind::Const(l), span)),
            Token::LParen => {
                self.expect(Token::LParen)?;
                if self.bump_if(Token::RParen) {
                    return Ok(Expr::new(
                        ExprKind::Const(Const::Unit),
                        span + self.current.span,
                    ));
                }
                let mut exprs = self.delimited(|p| p.parse_expr(), Token::Comma)?;
                let e = match exprs.len() {
                    1 => exprs.pop().unwrap(),
                    _ => Expr::new(ExprKind::Tuple(exprs), span),
                };
                self.expect(Token::RParen)?;
                span += self.prev;
                Ok(e)
            }
            _ => self.error(ErrorKind::ExpectedExpr),
        }
    }

    fn projection_expr(&mut self) -> Result<Expr, Error> {
        let mut span = self.current.span;
        let mut expr = self.atomic_expr()?;
        while self.bump_if(Token::Dot) {
            span += self.prev;
            let p = self.once(|p| p.atomic_expr(), "expected expr after Dot")?;
            expr = Expr::new(ExprKind::Projection(Box::new(expr), Box::new(p)), span);
        }
        Ok(expr)
    }

    /// appexp ::=      atexp
    ///                 appexp atexp
    fn application_expr(&mut self) -> Result<Expr, Error> {
        let span = self.current.span;
        let mut exprs = self.plus(|p| p.projection_expr(), None)?;
        match exprs.len() {
            1 => Ok(exprs.pop().unwrap()),
            _ => Ok(Expr::new(ExprKind::FlatApp(exprs), span + self.prev)),
        }
    }

    /// exp ::=     if exp then exp2 else exp3
    ///             case exp of casearm end
    ///             fn x
    ///             infix
    pub fn parse_expr(&mut self) -> Result<Expr, Error> {
        let expr = match self.current() {
            Token::Case => self.spanned(|p| p.case_expr()),
            Token::Fn => self.spanned(|p| p.lambda_expr()),
            _ => self.application_expr(),
        }?;

        if self.bump_if(Token::Colon) {
            let ty = self.once(|p| p.parse_type(), "expected type annotation!")?;
            let sp = expr.span + self.prev;
            Ok(Expr::new(ExprKind::Ann(Box::new(expr), Box::new(ty)), sp))
        } else {
            Ok(expr)
        }
    }
}
