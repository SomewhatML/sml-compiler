use std::cell::RefCell;
use std::collections::HashMap;

thread_local! {
    pub static INTERNER: RefCell<Interner> = RefCell::new(Interner::with_capacity(512));
}

macro_rules! globals {
    (@step $idx:expr, ) => {
        pub const S_TOTAL_GLOBALS: u32 = $idx - 1;
    };
    (@step $idx:expr, $it:ident, $($rest:ident,)*) => {
        pub const $it: Symbol = Symbol($idx);
        globals!(@step $idx+1u32, $($rest,)*);
    };
    ($($name:ident),+) => {
       globals!(@step 0u32, $($name,)*);
    };
}

globals!(
    S_ABSTYPE,
    S_AND,
    S_ANDALSO,
    S_AS,
    S_CASE,
    S_DATATYPE,
    S_DO,
    S_ELSE,
    S_END,
    S_EXCEPTION,
    S_FN,
    S_FUN,
    S_HANDLE,
    S_IF,
    S_IN,
    S_INFIX,
    S_INFIXR,
    S_LET,
    S_LOCAL,
    S_NONFIX,
    S_OF,
    S_OP,
    S_OPEN,
    S_ORELSE,
    S_RAISE,
    S_REC,
    S_THEN,
    S_TYPE,
    S_VAL,
    S_WITH,
    S_WITHTYPE,
    S_WHILE,
    S_FLEX,
    S_ARROW,
    S_DARROW,
    S_COLON,
    S_BAR,
    S_EQUAL,
    S_MUL,
    S_DIV,
    S_PLUS,
    S_MINUS,
    S_INT,
    S_CHAR,
    S_STRING,
    S_UNIT
);

#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Hash)]
pub struct Symbol(u32);

impl Symbol {
    pub const fn dummy() -> Self {
        Symbol(std::u32::MAX)
    }

    pub const fn builtin(self) -> bool {
        self.0 <= S_TOTAL_GLOBALS
    }

    pub const fn tuple_field(idx: u32) -> Self {
        // Hopefully we never are close to this many unique symbols...
        Self(idx | 0x8000_0000)
    }
}

#[derive(Clone, PartialEq)]
pub struct Interner {
    symbols: HashMap<String, Symbol>,
    strings: Vec<String>,
}

impl Interner {
    pub fn with_capacity(n: usize) -> Interner {
        let mut i = Interner {
            symbols: HashMap::with_capacity(n),
            strings: Vec::with_capacity(n),
        };

        assert_eq!(S_ABSTYPE, i.intern("abstype".into()));
        assert_eq!(S_AND, i.intern("and".into()));
        assert_eq!(S_ANDALSO, i.intern("andalso".into()));
        assert_eq!(S_AS, i.intern("as".into()));
        assert_eq!(S_CASE, i.intern("case".into()));
        assert_eq!(S_DATATYPE, i.intern("datatype".into()));
        assert_eq!(S_DO, i.intern("do".into()));
        assert_eq!(S_ELSE, i.intern("else".into()));
        assert_eq!(S_END, i.intern("end".into()));
        assert_eq!(S_EXCEPTION, i.intern("exception".into()));
        assert_eq!(S_FN, i.intern("fn".into()));
        assert_eq!(S_FUN, i.intern("fun".into()));
        assert_eq!(S_HANDLE, i.intern("handle".into()));
        assert_eq!(S_IF, i.intern("if".into()));
        assert_eq!(S_IN, i.intern("in".into()));
        assert_eq!(S_INFIX, i.intern("infix".into()));
        assert_eq!(S_INFIXR, i.intern("infixr".into()));
        assert_eq!(S_LET, i.intern("let".into()));
        assert_eq!(S_LOCAL, i.intern("local".into()));
        assert_eq!(S_NONFIX, i.intern("nonfix".into()));
        assert_eq!(S_OF, i.intern("of".into()));
        assert_eq!(S_OP, i.intern("op".into()));
        assert_eq!(S_OPEN, i.intern("open".into()));
        assert_eq!(S_ORELSE, i.intern("orelse".into()));
        assert_eq!(S_RAISE, i.intern("raise".into()));
        assert_eq!(S_REC, i.intern("rec".into()));
        assert_eq!(S_THEN, i.intern("then".into()));
        assert_eq!(S_TYPE, i.intern("type".into()));
        assert_eq!(S_VAL, i.intern("val".into()));
        assert_eq!(S_WITH, i.intern("with".into()));
        assert_eq!(S_WITHTYPE, i.intern("withtype".into()));
        assert_eq!(S_WHILE, i.intern("while".into()));
        assert_eq!(S_FLEX, i.intern("...".into()));
        assert_eq!(S_ARROW, i.intern("->".into()));
        assert_eq!(S_DARROW, i.intern("=>".into()));
        assert_eq!(S_COLON, i.intern(":".into()));
        assert_eq!(S_BAR, i.intern("|".into()));
        assert_eq!(S_EQUAL, i.intern("=".into()));
        assert_eq!(S_MUL, i.intern("*".into()));
        assert_eq!(S_DIV, i.intern("\\".into()));
        assert_eq!(S_PLUS, i.intern("+".into()));
        assert_eq!(S_MINUS, i.intern("-".into()));
        assert_eq!(S_INT, i.intern("int".into()));
        assert_eq!(S_CHAR, i.intern("char".into()));
        assert_eq!(S_STRING, i.intern("string".into()));
        assert_eq!(S_UNIT, i.intern("unit".into()));
        assert_eq!(S_TOTAL_GLOBALS, S_UNIT.0);
        i
    }

    pub fn intern(&mut self, s: String) -> Symbol {
        if let Some(sym) = self.symbols.get(&s) {
            return *sym;
        }

        let sym = Symbol(self.strings.len() as u32);
        self.strings.push(s.clone());
        self.symbols.insert(s, sym);
        sym
    }

    pub fn get(&self, symbol: Symbol) -> Option<&str> {
        self.strings.get(symbol.0 as usize).map(|s| s.as_ref())
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if (self.0 & 0x8000_0000) != 0 {
            return write!(f, "{}", self.0 & !0x8000_0000);
        }
        INTERNER.with(|i| match i.try_borrow() {
            Ok(b) => match b.get(*self) {
                Some(s) => write!(f, "{}", s),
                None => write!(f, "?"),
            },
            Err(_) => write!(f, "{}", self.0),
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn smoke() {
        let mut interner = Interner::with_capacity(10);
        let h = interner.intern("hello".into());
        let j = interner.intern("fn".into());
        let i = interner.intern("lambda".into());
        assert_eq!(interner.get(h), Some("hello"));
        assert_eq!(interner.get(j), Some("fn"));
        assert_eq!(interner.get(i), Some("lambda"));
    }
}
