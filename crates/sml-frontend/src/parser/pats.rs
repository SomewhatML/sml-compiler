use super::*;

// use PatKind::*;

impl<'s, 'sym> Parser<'s, 'sym> {
    fn tuple_pattern(&mut self) -> Result<Pat, Error> {
        let mut span = self.current.span;
        self.expect(Token::LParen)?;
        if self.bump_if(Token::RParen) {
            return Ok(Pat::new(
                PatKind::Lit(Literal::Unit),
                span + self.current.span,
            ));
        }
        let mut v = self.star(|p| p.parse_pattern(), Some(Token::Comma));
        self.expect(Token::RParen)?;
        span += self.prev;
        match v.len() {
            0 => Ok(Pat::new(PatKind::Lit(Literal::Unit), span)),
            1 => Ok(v.pop().unwrap()),
            _ => Ok(Pat::new(PatKind::Product(v), span)),
        }
    }

    fn record_pattern(&mut self) -> Result<Pat, Error> {
        let mut span = self.current.span;
        self.expect(Token::LBrace)?;
        let v = self.delimited(|p| p.parse_pattern(), Token::Comma)?;
        self.expect(Token::RBrace)?;
        span += self.prev;
        Ok(Pat::new(PatKind::Record(v), span))
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
                Ok(Pat::new(PatKind::Any, span))
            }
            Token::Id(_) | Token::IdS(_) => self
                .expect_id()
                .map(|s| Pat::new(PatKind::Variable(s), span)),
            Token::Literal(_) => self.literal().map(|l| Pat::new(PatKind::Lit(l), span)),
            Token::LParen => self.tuple_pattern(),
            Token::LBrace => self.record_pattern(),
            _ => self.error(ErrorKind::ExpectedPat),
        }
    }

    /// app_pat ::=     atpat
    ///                 app_pat atpat
    fn application_pattern(&mut self) -> Result<Pat, Error> {
        let span = self.current.span;
        let pat = self.atomic_pattern()?;
        if let PatKind::Variable(_) = pat.data {
            let mut v = Vec::new();
            v.push(pat);
            while let Ok(arg) = self.atomic_pattern() {
                v.push(arg);
            }
            return Ok(Pat::new(PatKind::FlatApp(v), span + self.prev));
        }
        Ok(pat)
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
