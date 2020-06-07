use super::ast::Literal;
use sml_util::interner::Symbol;

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub enum Token {
    /// Reserved symbols
    Apostrophe,
    Wildcard,
    Dot,
    Flex,
    Bar,
    Comma,
    Colon,
    Semi,
    Arrow,
    DArrow,
    Equals,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    /// Reserved keywords
    Abstype,
    And,
    Andalso,
    As,
    Case,
    Datatype,
    Do,
    Else,
    End,
    Exception,
    Fn,
    Fun,
    Handle,
    If,
    In,
    Infix,
    Infixr,
    Let,
    Local,
    Nonfix,
    Of,
    Op,
    Open,
    Orelse,
    Raise,
    Rec,
    Then,
    Type,
    Val,
    With,
    Withtype,
    While,

    Forall,
    /// Alphabetic identifier
    Id(Symbol),
    /// Symbolic identifier
    IdS(Symbol),
    /// Literal value
    Literal(Literal),

    /// Errors
    Invalid(char),
    EOF,
}

impl Token {
    pub fn extract_string(self) -> Symbol {
        match self {
            Token::Id(s) | Token::IdS(s) => s,
            _ => panic!("Invalid token {:?}", self),
        }
    }
}
