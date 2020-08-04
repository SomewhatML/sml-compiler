use sml_util::interner::Symbol;
use sml_util::Const;

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub enum Token {
    /// Reserved symbols, see sml-util/interner.rs for defs
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
    Selector,

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
    Functor,
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
    Primitive,
    Raise,
    Rec,
    Then,
    Type,
    Val,
    With,
    Withtype,
    While,
    Sig,
    Signature,
    Struct,
    Structure,

    Forall,
    /// Alphabetic identifier
    Id(Symbol),
    /// Symbolic identifier
    IdS(Symbol),
    /// Literal value
    Const(Const),

    /// Errors
    Invalid(char),
    MissingDelimiter(char),
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
