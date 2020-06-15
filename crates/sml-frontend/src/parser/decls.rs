use super::*;

impl<'s, 'sym> Parser<'s, 'sym> {
    fn type_binding(&mut self) -> Result<Typebind, Error> {
        let tyvars = self.type_var_seq()?;
        let tycon = self.expect_id()?;
        self.expect(Token::Equals)?;
        let ty = self.parse_type()?;
        Ok(Typebind { tycon, tyvars, ty })
    }

    fn parse_decl_type(&mut self) -> Result<DeclKind, Error> {
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

    fn parse_decl_datatype(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Datatype)?;
        let bindings = self.delimited(|p| p.datatype(), Token::And)?;
        Ok(DeclKind::Datatype(bindings))
    }

    fn parse_decl_val(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Val)?;
        let pat = self.parse_pattern()?;
        self.expect(Token::Equals)?;
        let expr = self.parse_expr()?;
        Ok(DeclKind::Value(pat, expr))
    }

    fn parse_fun_binding(&mut self) -> Result<FnBinding, Error> {
        let name = self.once(|p| p.expect_id(), "id required for function binding")?;
        let pats = self.plus(|p| p.atomic_pattern(), None)?;
        let res_ty = if self.bump_if(Token::Colon) {
            let ty = self.once(|p| p.parse_type(), "result type expected after `:`")?;
            Some(ty)
        } else {
            None
        };
        self.expect(Token::Equals)?;
        let expr = self.once(|p| p.parse_expr(), "missing expression in function!")?;
        Ok(FnBinding {
            name,
            pats,
            expr,
            res_ty,
        })
    }

    fn parse_fun(&mut self) -> Result<Fun, Error> {
        self.spanned(|p| p.delimited(|j| j.parse_fun_binding(), Token::Bar))
    }

    fn parse_decl_fun(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Fun)?;
        let tyvars = self.type_var_seq()?;
        let funs = self.delimited(|p| p.parse_fun(), Token::And)?;
        Ok(DeclKind::Function(tyvars, funs))
    }

    pub fn parse_decl_exn(&mut self) -> Result<DeclKind, Error> {
        self.expect(Token::Exception)?;
        let bindings = self.delimited(|p| p.variant(), Token::And)?;
        Ok(DeclKind::Exception(bindings))
    }

    fn fixity(&mut self) -> Result<DeclKind, Error> {
        let fixity = match self.bump() {
            Token::Infix => Fixity::Infix,
            Token::Infixr => Fixity::Infixr,
            Token::Nonfix => Fixity::Nonfix,
            _ => unreachable!(),
        };

        let num = match self.current() {
            Token::Const(Const::Int(i)) => {
                self.bump();
                i as u8
            }
            _ => 0,
        };
        let sym = self.once(
            |p| p.expect_id(),
            "symbol required after fixity declaration",
        )?;
        Ok(DeclKind::Fixity(fixity, num, sym))
    }

    fn parse_decl_atom(&mut self) -> Result<Decl, Error> {
        match self.current() {
            Token::Fun => self.spanned(|p| p.parse_decl_fun()),
            Token::Val => self.spanned(|p| p.parse_decl_val()),
            Token::Type => self.spanned(|p| p.parse_decl_type()),
            Token::Datatype => self.spanned(|p| p.parse_decl_datatype()),
            Token::Exception => self.spanned(|p| p.parse_decl_exn()),
            Token::Infix | Token::Infixr | Token::Nonfix => self.spanned(|p| p.fixity()),
            Token::EOF => self.error(ErrorKind::EOF),
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

    pub fn parse_decl(&mut self) -> Result<Decl, Error> {
        let mut seq = Vec::new();
        let span = self.current.span;
        self.bump_if(Token::Semi);
        while let Ok(decl) = self.parse_decl_atom() {
            seq.push(decl);
            self.bump_if(Token::Semi);
        }
        match seq.len() {
            0 => self.error(ErrorKind::ExpectedDecl),
            1 => Ok(seq.pop().unwrap()),
            _ => Ok(Decl::new(DeclKind::Seq(seq), span + self.prev)),
        }
    }
}
