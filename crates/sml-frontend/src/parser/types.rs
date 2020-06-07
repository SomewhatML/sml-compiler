use super::*;

use TypeKind::*;

impl<'s, 'sym> Parser<'s, 'sym> {
    // /// Parse a datatype Constructor [A-Z]+
    pub(crate) fn variant(&mut self) -> Result<Variant, Error> {
        let mut span = self.current.span;
        let label = self.expect_id()?;
        let ty = self.star(|p| p.type_atom(), None);
        span += self.prev;
        Ok(Variant { label, ty, span })
    }

    pub(crate) fn type_var_seq(&mut self) -> Result<Vec<Symbol>, Error> {
        if self.bump_if(Token::LParen) {
            let ret = self.delimited(|p| p.type_var(), Token::Comma)?;
            self.expect(Token::RParen)?;
            return Ok(ret);
        }
        self.type_var().map(|x| vec![x])
    }

    pub(crate) fn type_var(&mut self) -> Result<Symbol, Error> {
        self.expect(Token::Apostrophe)?;
        self.expect_id_alpha()
    }

    /// Parse a universal type of form `forall ('tv :: K) of ty`
    fn universal(&mut self) -> Result<Type, Error> {
        let mut span = self.current.span;
        self.expect(Token::Forall)?;
        let arg = self.once(|p| p.type_var(), "universal type requires an argument")?;
        self.expect(Token::Dot)?;
        let body = self.once(|p| p.type_atom(), "universal type requires a body")?;
        span += self.prev;
        Ok(Type::new(Univ(arg, Box::new(body)), span))
    }

    /// Parse a type row of form `label: ty`
    fn row(&mut self) -> Result<Row, Error> {
        let mut span = self.current.span;
        let label = self.expect_id()?;
        self.expect(Token::Colon)?;
        let ty = self.once(
            |p| p.parse_type(),
            "record type row requires a type {label: ty, ...}",
        )?;
        span += self.prev;

        Ok(Row { label, ty, span })
    }

    /// Parse a type of form `{ label: ty, label2: ty2, ...}`
    fn record(&mut self) -> Result<Type, Error> {
        let mut span = self.current.span;
        self.expect(Token::LBrace)?;
        let rows = self.delimited(|p| p.row(), Token::Comma)?;
        self.expect(Token::RBrace)?;
        span += self.prev;
        Ok(Type::new(Record(rows), span))
    }

    /// Parse a type of form:
    /// ty ::=  'var
    ///         id
    ///         ( ty )
    ///         ( ty1, ... tyN) ty
    ///         fn (var :: kind) => ty
    ///         exists (var :: kind) of ty
    ///         forall (var :: kind) of ty
    ///         rec ty
    ///         { label: ty, ...}
    pub(crate) fn type_atom(&mut self) -> Result<Type, Error> {
        let span = self.current.span;
        match self.current.data {
            Token::Apostrophe => {
                self.bump();
                let sp = span + self.current.span;
                self.expect_id_alpha().map(|p| Type::new(Var(p), sp))
            }
            Token::Id(_) | Token::IdS(_) => self
                .expect_id()
                .map(|p| Type::new(Con(p, Vec::new()), span)),
            Token::Forall => self.universal(),
            Token::LBrace => self.record(),
            Token::LParen => {
                self.bump();
                let mut v = self.delimited(|p| p.parse_type(), Token::Comma)?;
                self.expect(Token::RParen)?;

                if v.len() == 1 {
                    Ok(v.pop().unwrap())
                } else {
                    Ok(Type::new(TypeKind::Product(v), span + self.current.span))
                }
            }
            _ => self.error(ErrorKind::ExpectedType),
        }
    }

    /// Parse an application of form:
    ///     (ty1, ty2) tycon
    ///     ty         tycon
    fn application(&mut self) -> Result<Type, Error> {
        let mut fst = self.type_atom()?;
        while self.is_id() && self.current() != Token::IdS(S_MUL) {
            let con = self.expect_id()?;
            let sp = fst.span;
            let k = match fst.data {
                TypeKind::Product(v) => TypeKind::Con(con, v),
                _ => TypeKind::Con(con, vec![fst]),
            };
            fst = Type::new(k, sp + self.prev);
        }
        Ok(fst)
    }

    /// Parse a type of form: `ty` | `ty * ty2 * ...`
    fn product(&mut self) -> Result<Type, Error> {
        let mut span = self.current.span;
        let mut v = vec![self.application()?];
        while self.bump_if(Token::IdS(S_MUL)) {
            v.push(self.application()?);
        }
        span += self.prev;
        match v.len() {
            1 => Ok(v.pop().unwrap()),
            _ => Ok(Type::new(Product(v), span)),
        }
    }

    /// Parse a type of form: `ty * ty` | `ty -> ty`
    pub fn parse_type(&mut self) -> Result<Type, Error> {
        let mut span = self.current.span;
        let ty = self.product()?;
        if self.bump_if(Token::Arrow) {
            let ty2 = self.parse_type()?;
            span += ty2.span;
            return Ok(Type::new(Con(S_ARROW, vec![ty, ty2]), span));
        }
        Ok(ty)
    }
}
