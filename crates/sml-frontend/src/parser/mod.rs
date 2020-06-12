use super::ast::*;
use super::lexer::Lexer;
use super::tokens::*;
use sml_util::diagnostics::Diagnostic;
use sml_util::interner::*;
use sml_util::span::{Span, Spanned};
use std::iter::Peekable;
mod decls;
mod exprs;
mod pats;
pub mod precedence;
mod types;

pub struct Parser<'s, 'sym> {
    tokens: Peekable<Lexer<'s, 'sym>>,
    current: Spanned<Token>,
    prev: Span,
    pub diags: Vec<Diagnostic>,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum ErrorKind {
    ExpectedToken(Token),
    ExpectedIdentifier,
    ExpectedType,
    ExpectedPat,
    ExpectedExpr,
    ExpectedDecl,
    Internal,
    EOF,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Error {
    pub span: Span,
    pub token: Token,
    pub kind: ErrorKind,
}

impl Error {
    pub fn to_diagnostic(self) -> Diagnostic {
        use ErrorKind::*;
        let message = match self.kind {
            ExpectedToken(kind) => format!(
                "expected a token of kind {:?}, but encountered {:?}",
                kind, self.token
            ),
            ExpectedIdentifier => format!("expected identifier, but encountered {:?}", self.token),
            ExpectedType => format!("expected type, but encountered {:?}", self.token),
            ExpectedPat => format!("expected pattern, but encountered {:?}", self.token),
            ExpectedExpr => format!("expected expression, but encountered {:?}", self.token),
            ExpectedDecl => format!("expected declaration, but encountered {:?}", self.token),
            Internal => format!("internal parser error! last token was {:?}", self.token),
            EOF => format!("EOF?"),
        };
        Diagnostic::error(self.span, message)
    }
}

#[macro_export]
macro_rules! diag {
    ($sp:expr, $msg:expr, $($t:expr),+) => { Diagnostic::error($sp, format!($msg, $($t),+)) };
}

impl<'s, 'sym> Parser<'s, 'sym> {
    pub fn new(input: &'s str, interner: &'sym mut Interner) -> Parser<'s, 'sym> {
        let mut p = Parser {
            tokens: Lexer::new(input.chars(), interner).peekable(),
            current: Spanned::new(Token::EOF, Span::zero()),
            prev: Span::zero(),
            diags: Vec::new(),
        };
        p.bump();
        p
    }

    /// Generate a parsing error. These are not necessarily fatal
    fn error<T>(&self, k: ErrorKind) -> Result<T, Error> {
        Err(Error {
            span: self.current.span,
            token: self.current.data,
            kind: k,
        })
    }

    fn current(&self) -> Token {
        self.current.data
    }

    /// Bump the current token, returning it, and pull a new token
    /// from the lexer
    fn bump(&mut self) -> Token {
        match self.tokens.next() {
            Some(t) => {
                self.prev = self.current.span;
                std::mem::replace(&mut self.current, t).data()
            }
            None => std::mem::replace(&mut self.current.data, Token::EOF),
        }
    }

    /// Ignore a token matching `kind`
    fn bump_if(&mut self, kind: Token) -> bool {
        if self.current.data == kind {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: Token) -> Result<(), Error> {
        if self.current() == kind {
            self.bump();
            Ok(())
        } else {
            self.diags.push(diag!(
                self.current.span,
                "expected token {:?}, but found {:?}",
                kind,
                self.current()
            ));
            self.error(ErrorKind::ExpectedToken(kind))
        }
    }

    fn expect_id(&mut self) -> Result<Symbol, Error> {
        match self.current() {
            Token::Id(s) | Token::IdS(s) => {
                self.bump();
                Ok(s)
            }
            _ => self.error(ErrorKind::ExpectedIdentifier),
        }
    }

    fn is_id(&self) -> bool {
        match self.current() {
            Token::Id(_) | Token::IdS(_) => true,
            _ => false,
        }
    }

    fn expect_id_alpha(&mut self) -> Result<Symbol, Error> {
        match self.current() {
            Token::Id(s) => {
                self.bump();
                Ok(s)
            }
            _ => self.error(ErrorKind::ExpectedIdentifier),
        }
    }

    fn spanned<T, F: Fn(&mut Parser) -> Result<T, Error>>(
        &mut self,
        f: F,
    ) -> Result<Spanned<T>, Error> {
        let sp = self.current.span;
        f(self).map(|inner| Spanned::new(inner, sp + self.current.span))
    }

    /// Call `func` once, returning the `Result<T,E>` of the function.
    /// A failure of `func` may have side effects, including emitting
    /// diagnostics containing `message`
    ///
    /// Generally, this is just used to give better error messages
    fn once<T, E, F>(&mut self, func: F, message: &str) -> Result<T, E>
    where
        F: Fn(&mut Parser) -> Result<T, E>,
    {
        match func(self) {
            Ok(t) => Ok(t),
            Err(e) => {
                self.diags.push(diag!(self.current.span, "{}", message));
                Err(e)
            }
        }
    }

    /// Collect the result of `func` into a `Vec<T>` as long as `func` returns
    /// an `Ok(T)`. A call to `func` must succeed on the first try, or an error
    /// is immediately returned. Subsequent calls to `func` may fail, in which
    /// case the error is discarded, and the results are returned. If `delimit`
    /// is supplied, the parser will discard matching tokens between each call
    /// to `func`
    fn plus<T, E, F>(&mut self, func: F, delimit: Option<Token>) -> Result<Vec<T>, E>
    where
        F: Fn(&mut Parser) -> Result<T, E>,
    {
        let mut v = vec![func(self)?];
        if let Some(t) = delimit {
            if !self.bump_if(t) {
                return Ok(v);
            }
        }
        while let Ok(x) = func(self) {
            v.push(x);
            if let Some(t) = delimit {
                if !self.bump_if(t) {
                    break;
                }
            }
        }
        Ok(v)
    }

    /// Collect the result of `func` into a `Vec<T>` as long as `func` returns
    /// an `Ok(T)`. If an error is encountered, it is discarded and the results
    /// are immediately returned. If `delimit` is supplied, the parser will
    /// discard matching tokens between each call to `func`
    fn star<T, E, F>(&mut self, func: F, delimit: Option<Token>) -> Vec<T>
    where
        F: Fn(&mut Parser) -> Result<T, E>,
    {
        let mut v = Vec::new();
        while let Ok(x) = func(self) {
            v.push(x);
            if let Some(t) = delimit {
                if !self.bump_if(t) {
                    break;
                }
            }
        }
        v
    }

    /// Identical semantics to `Parser::plus`, except `delimit` must be supplied
    fn delimited<T, F>(&mut self, func: F, delimit: Token) -> Result<Vec<T>, Error>
    where
        F: Fn(&mut Parser) -> Result<T, Error>,
    {
        let mut v = vec![func(self)?];
        if !self.bump_if(delimit) {
            return Ok(v);
        }
        while let Ok(x) = func(self) {
            v.push(x);
            if !self.bump_if(delimit) {
                break;
            }
        }

        Ok(v)
    }
}
