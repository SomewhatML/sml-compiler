use super::*;

// use PatKind::*;

impl<'s, 'sym> Parser<'s, 'sym> {
    fn tuple_pattern(&mut self) -> Result<PatKind, Error> {
        self.expect(Token::LParen)?;
        if self.bump_if(Token::RParen) {
            return Ok(PatKind::Const(Const::Unit));
        }
        let mut v = self.star(|p| p.parse_pattern(), Some(Token::Comma));
        self.expect(Token::RParen)?;
        match v.len() {
            1 => Ok(v.pop().unwrap().data),
            _ => Ok(make_record_pat(v)),
        }
    }

    fn row_pattern(&mut self) -> Result<Row<Pat>, Error> {
        let span = self.current.span;
        let label = self.expect_id()?;
        // If we have lab = pat, then return that, otherwise we desugar into label=label
        if self.bump_if(Token::Equals) {
            let data = self.once(|p| p.parse_pattern(), "expected pattern in `label = ...`")?;
            Ok(Row {
                label,
                data,
                span: span + self.prev,
            })
        } else {
            Ok(Row {
                label,
                data: Pat::new(PatKind::Variable(label), span),
                span,
            })
        }
    }

    fn record_pattern(&mut self) -> Result<PatKind, Error> {
        self.expect(Token::LBrace)?;
        if self.bump_if(Token::RParen) {
            return Ok(PatKind::Const(Const::Unit));
        }
        let v = self.delimited(|p| p.row_pattern(), Token::Comma)?;
        self.expect(Token::RBrace)?;
        Ok(PatKind::Record(v))
    }

    fn list_pattern(&mut self) -> Result<PatKind, Error> {
        self.expect(Token::LBracket)?;
        if self.bump_if(Token::RBracket) {
            return Ok(PatKind::Const(Const::Unit));
        }
        let v = self.delimited(|p| p.parse_pattern(), Token::Comma)?;
        self.expect(Token::RBracket)?;
        Ok(PatKind::List(v))
    }

    /// atpat ::=   constant
    ///             id
    ///             wildcard
    ///             ( pat )
    ///             ( pat, ... patN )
    ///             { [patrow] }
    pub(crate) fn atomic_pattern(&mut self) -> Result<Pat, Error> {
        let span = self.current.span;
        match self.current.data {
            Token::Wildcard => {
                self.bump();
                Ok(Pat::new(PatKind::Wild, span))
            }
            Token::Id(_) | Token::IdS(_) => self
                .expect_id()
                .map(|s| Pat::new(PatKind::Variable(s), span)),
            Token::Const(_) => self.constant().map(|l| Pat::new(PatKind::Const(l), span)),
            Token::LParen => self.spanned(|p| p.tuple_pattern()),
            Token::LBrace => self.spanned(|p| p.record_pattern()),
            Token::LBracket => self.spanned(|p| p.list_pattern()),
            _ => self.error(ErrorKind::ExpectedPat),
        }
    }

    /// app_pat ::=     atpat
    ///                 app_pat atpat
    fn application_pattern(&mut self) -> Result<Pat, Error> {
        let span = self.current.span;
        let mut pats = self.plus(|p| p.atomic_pattern(), None)?;
        match pats.len() {
            1 => Ok(pats.pop().unwrap()),
            _ => Ok(Pat::new(PatKind::FlatApp(pats), span + self.prev)),
        }
    }

    pub fn parse_pattern(&mut self) -> Result<Pat, Error> {
        let mut span = self.current.span;
        let pat = self.application_pattern()?;
        if self.bump_if(Token::Colon) {
            let ty = self.once(|p| p.parse_type(), "expected type annotation after `pat :`")?;
            span += self.prev;
            return Ok(Pat::new(
                PatKind::Ascribe(Box::new(pat), Box::new(ty)),
                span,
            ));
        }
        Ok(pat)
    }
}
