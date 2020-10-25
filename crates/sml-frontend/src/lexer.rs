use super::tokens::*;
use sml_util::interner::*;
use sml_util::span::{Location, Span, Spanned};
use sml_util::Const;
use std::char;
use std::iter::Peekable;
use std::str::Chars;

pub struct Lexer<'s, 'sym> {
    source: &'s str,
    interner: &'sym mut Interner,
    input: Peekable<Chars<'s>>,
    current: Location,
    abs: usize,
}

impl<'s, 'sym> Lexer<'s, 'sym> {
    pub fn new(input: Chars<'s>, interner: &'sym mut Interner) -> Lexer<'s, 'sym> {
        Lexer {
            source: input.as_str(),
            input: input.peekable(),
            current: Location {
                line: 0,
                col: 0,
                // abs: 0,
            },
            abs: 0,
            interner,
        }
    }

    /// Peek at the next [`char`] in the input stream
    #[inline]
    fn peek(&mut self) -> Option<char> {
        self.input.peek().copied()
    }

    /// Consume the next [`char`] and advance internal source position
    #[inline]
    fn consume(&mut self) -> Option<char> {
        match self.input.next() {
            Some('\n') => {
                self.current.line += 1;
                self.current.col = 0;
                self.abs += 1;
                // self.current.abs += 1;
                Some('\n')
            }
            Some(ch) => {
                self.current.col += 1;
                self.abs += 1;
                // self.current.abs += 1;
                Some(ch)
            }
            None => None,
        }
    }

    /// Consume characters from the input stream while pred(peek()) is true,
    /// collecting the characters into a string.
    #[inline]
    fn consume_while<F: Fn(char) -> bool>(&mut self, pred: F) -> (&'s str, Span) {
        let abs = self.abs;
        let start = self.current;
        while let Some(n) = self.peek() {
            if pred(n) {
                match self.consume() {
                    Some(_) => continue,
                    None => break,
                }
            } else {
                break;
            }
        }
        (&self.source[abs..self.abs], Span::new(start, self.current))
    }

    /// Eat whitespace
    #[inline]
    fn consume_delimiter(&mut self) {
        let _ = self.consume_while(char::is_whitespace);
    }

    #[inline]
    fn valid_symbolic(c: char) -> bool {
        match c {
            '!' | '%' | '&' | '$' | '#' | '+' | '-' | '/' | ':' | '<' | '=' | '>' | '?' | '@'
            | '~' | '`' | '^' | '|' | '*' | '\\' | '.' => true,
            _ => false,
        }
    }

    fn symbolic(&mut self) -> Spanned<Token> {
        let (s, sp) = self.consume_while(Self::valid_symbolic);
        // Take care of reserved symbols
        let kind = match self.interner.intern(s) {
            S_ARROW => Token::Arrow,
            S_DARROW => Token::DArrow,
            S_COLON => Token::Colon,
            S_BAR => Token::Bar,
            S_EQUAL => Token::Equals,
            S_DOT => Token::Dot,
            S_FLEX => Token::Flex,
            x => Token::IdS(x),
        };
        Spanned::new(kind, sp)
    }

    #[inline]
    fn valid_id_char(c: char) -> bool {
        match c {
            x if x.is_alphanumeric() => true,
            '_' | '\'' => true,
            _ => false,
        }
    }

    /// Lex a reserved keyword or identifier
    fn keyword(&mut self) -> Spanned<Token> {
        let (word, sp) = self.consume_while(Self::valid_id_char);
        let word = self.interner.intern(word);
        let kind = match word {
            S_ABSTYPE => Token::Abstype,
            S_AND => Token::And,
            S_ANDALSO => Token::Andalso,
            S_AS => Token::As,
            S_CASE => Token::Case,
            S_DATATYPE => Token::Datatype,
            S_DO => Token::Do,
            S_ELSE => Token::Else,
            S_END => Token::End,
            S_EXCEPTION => Token::Exception,
            S_FN => Token::Fn,
            S_FUN => Token::Fun,
            S_FUNCTOR => Token::Functor,
            S_HANDLE => Token::Handle,
            S_IF => Token::If,
            S_IN => Token::In,
            S_INFIX => Token::Infix,
            S_INFIXR => Token::Infixr,
            S_LET => Token::Let,
            S_LOCAL => Token::Local,
            S_NONFIX => Token::Nonfix,
            S_OF => Token::Of,
            S_OP => Token::Op,
            S_OPEN => Token::Open,
            S_ORELSE => Token::Orelse,
            S_PRIM => Token::Primitive,
            S_RAISE => Token::Raise,
            S_REC => Token::Rec,
            S_THEN => Token::Then,
            S_TYPE => Token::Type,
            S_VAL => Token::Val,
            S_WITH => Token::With,
            S_WITHTYPE => Token::Withtype,
            S_WHILE => Token::While,
            S_SIG => Token::Sig,
            S_SIGNATURE => Token::Signature,
            S_STRUCT => Token::Struct,
            S_STRUCTURE => Token::Structure,
            _ => Token::Id(word),
        };
        Spanned::new(kind, sp)
    }

    fn string_lit(&mut self) -> Option<Spanned<Token>> {
        self.consume()?;
        let (s, sp) = self.consume_while(|c| c != '"');
        if self.consume().is_none() {
            return Some(Spanned::new(Token::MissingDelimiter('"'), sp));
        }
        Some(Spanned::new(
            Token::Const(Const::String(self.interner.intern(s))),
            sp,
        ))
    }

    /// Lex a natural number
    fn number(&mut self) -> Option<Spanned<Token>> {
        // Since we peeked at least one numeric char, we should always
        // have a string containing at least 1 single digit, as such
        // it is safe to call unwrap() on str::parse<u32>
        let (data, span) = self.consume_while(char::is_numeric);
        let n = data.parse::<usize>().ok()?;
        Some(Spanned::new(Token::Const(Const::Int(n)), span))
    }

    fn char_lit(&mut self) -> Option<Spanned<Token>> {
        let sp = self.current;
        match self.consume()? {
            '"' => {}
            c => return Some(Spanned::new(Token::Invalid(c), Span::new(sp, self.current))),
        }
        // TODO: return invalid on fail
        let ch = self.consume()?;
        match self.consume() {
            Some('"') => Some(Spanned::new(
                Token::Const(Const::Char(ch)),
                Span::new(sp, self.current),
            )),
            Some(c) => Some(Spanned::new(Token::Invalid(c), Span::new(sp, self.current))),
            None => Some(Spanned::new(
                Token::MissingDelimiter('\''),
                Span::new(sp, self.current),
            )),
        }
    }

    fn comment(&mut self) -> Option<Spanned<Token>> {
        let (_, sp) = self.consume_while(|ch| ch != '*');
        self.consume()?;
        match self.peek() {
            Some(')') => {
                self.consume();
                self.lex()
            }
            Some(_) => self.comment(),
            None => Some(Spanned::new(Token::MissingDelimiter('*'), sp)),
        }
    }

    pub fn lex(&mut self) -> Option<Spanned<Token>> {
        self.consume_delimiter();
        let sp = self.current;

        macro_rules! eat {
            ($kind:expr) => {{
                self.consume().unwrap();
                Some(Spanned::new($kind, Span::new(sp, self.current)))
            }};
        }

        match self.peek()? {
            ';' => eat!(Token::Semi),
            ',' => eat!(Token::Comma),
            '\'' => eat!(Token::Apostrophe),
            '_' => eat!(Token::Wildcard),
            '(' => {
                let alt = eat!(Token::LParen);
                if let Some('*') = self.peek() {
                    self.comment()
                } else {
                    alt
                }
            }
            ')' => eat!(Token::RParen),
            '{' => eat!(Token::LBrace),
            '}' => eat!(Token::RBrace),
            '[' => eat!(Token::LBracket),
            ']' => eat!(Token::RBracket),
            'λ' => eat!(Token::Fn),
            '∀' => eat!(Token::Forall),
            '#' => {
                self.consume();
                match self.peek() {
                    Some('"') => self.char_lit(),
                    Some(_) => Some(Spanned::new(Token::Selector, Span::new(sp, self.current))),
                    _ => None,
                }
            }
            '"' => self.string_lit(),
            x if x.is_ascii_alphabetic() => Some(self.keyword()),
            x if x.is_numeric() => self.number(),
            x if Self::valid_symbolic(x) => Some(self.symbolic()),
            ch => {
                self.consume();
                Some(Spanned::new(
                    Token::Invalid(ch),
                    Span::new(self.current, self.current),
                ))
            }
        }
    }
}

impl<'s, 'sym> Iterator for Lexer<'s, 'sym> {
    type Item = Spanned<Token>;
    fn next(&mut self) -> Option<Self::Item> {
        self.lex()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn _span(a: u32, b: u32) -> Span {
        Span::new(Location::new(0, a as u16, a), Location::new(0, b as u16, b))
    }

    #[test]
    fn keywords() {
        let mut int = Interner::with_capacity(64);
        let lex = Lexer::new("andalso and fn ...".chars(), &mut int);

        let tks = lex.collect::<Vec<Spanned<Token>>>();
        assert_eq!(
            tks,
            vec![
                Spanned::new(Token::Andalso, _span(0, 7)),
                Spanned::new(Token::And, _span(8, 11)),
                Spanned::new(Token::Fn, _span(12, 14)),
                Spanned::new(Token::Flex, _span(15, 18)),
            ]
        );
        assert_eq!(
            tks.into_iter().map(|s| s.span).collect::<Vec<_>>(),
            vec![_span(0, 7), _span(8, 11), _span(12, 14), _span(15, 18),]
        )
    }
}
