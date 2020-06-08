use super::*;

impl<'s, 'sym> Parser<'s, 'sym> {
    fn type_binding(&mut self) -> Result<Typebind, Error> {
        let tyvars = self.type_var_seq()?;
        let tycon = self.expect_id()?;
        self.expect(Token::Equals)?;
        let ty = self.parse_type()?;
        Ok(Typebind { tycon, tyvars, ty })
    }

    pub fn parse_decl_type(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Type)?;
        let bindings = self.delimited(|p| p.type_binding(), Token::And)?;
        Ok(DeclKind::Type(bindings))
    }

    // /// Parse a datatype Constructor [A-Z]+
    fn variant(&mut self) -> Result<Variant, Error> {
        let mut span = self.current.span;
        let label = self.expect_id()?;
        let data = match self.bump_if(Token::Of) {
            true => Some(self.parse_type()?),
            false => None,
        };
        span += self.prev;
        Ok(Variant { label, data, span })
    }

    fn datatype(&mut self) -> Result<Datatype, Error> {
        let tyvars = self.type_var_seq()?;
        let tycon = self.expect_id()?;
        self.expect(Token::Equals)?;
        let constructors = self.delimited(|p| p.variant(), Token::Bar)?;
        Ok(Datatype {
            tycon,
            tyvars,
            constructors,
        })
    }

    pub fn parse_decl_datatype(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Datatype)?;
        let bindings = self.delimited(|p| p.datatype(), Token::And)?;
        Ok(DeclKind::Datatype(bindings))
    }

    pub fn parse_decl_val(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Val)?;
        let pat = self.parse_pattern()?;
        self.expect(Token::Equals)?;
        let expr = self.parse_expr()?;
        Ok(DeclKind::Value(pat, expr))
    }

    pub fn parse_fun_binding(&mut self) -> Result<FnBinding, Error> {
        let pats = self.plus(|p| p.atomic_pattern(), None)?;
        self.expect(Token::Equals)?;
        let expr = self.once(|p| p.parse_expr(), "missing expression in function!")?;
        Ok(FnBinding { pats, expr })
    }

    pub fn parse_decl_fun(&mut self) -> Result<DeclKind, Error> {
        let mut span = self.current.span;
        self.expect(Token::Fun)?;
        let name = self.expect_id()?;
        let ty = if self.bump_if(Token::Colon) {
            let ty = self.once(|p| p.parse_type(), "type annotation required after `:`")?;
            self.expect(Token::Bar)?;
            Some(ty)
        } else {
            self.bump_if(Token::Bar);
            None
        };
        let body = self.delimited(|p| p.parse_fun_binding(), Token::Bar)?;
        span += self.prev;
        Ok(DeclKind::Function(name, Function { ty, body, span }))
    }

    pub fn parse_decl_exn(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Exception)?;
        let bindings = self.delimited(|p| p.variant(), Token::And)?;
        Ok(DeclKind::Exception(bindings))
    }

    pub fn parse_decl(&mut self) -> Result<Decl, Error> {
        match self.current() {
            Token::Fun => self.spanned(|p| p.parse_decl_fun()),
            Token::Val => self.spanned(|p| p.parse_decl_val()),
            Token::Type => self.spanned(|p| p.parse_decl_type()),
            Token::Datatype => self.spanned(|p| p.parse_decl_datatype()),
            Token::Exception => self.spanned(|p| p.parse_decl_exn()),
            Token::Infix => self.spanned(|p| {
                p.expect(Token::Infix)?;
                let num = match p.current() {
                    Token::Const(Const::Int(i)) => {
                        p.bump();
                        i as u8
                    }
                    _ => 0,
                };
                let sym = p.expect_id()?;
                Ok(DeclKind::Infix(num, sym))
            }),
            Token::Infixr => self.spanned(|p| {
                p.expect(Token::Infixr)?;
                let num = match p.current() {
                    Token::Const(Const::Int(i)) => {
                        p.bump();
                        i as u8
                    }
                    _ => 0,
                };
                let sym = p.expect_id()?;
                Ok(DeclKind::Infixr(num, sym))
            }),
            _ => {
                self.diags.push(Diagnostic::error(
                    self.current.span,
                    format!(
                        "expected a top-level declaration, found token {:?}",
                        self.current()
                    ),
                ));
                self.error(ErrorKind::ExpectedDecl)
            }
        }
    }
}
