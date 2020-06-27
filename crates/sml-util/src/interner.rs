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
        pub const $it: Symbol = Symbol::Interned($idx);
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
    S_FUNCTOR,
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
    S_SIG,
    S_SIGNATURE,
    S_STRUCT,
    S_STRUCTURE,
    S_DOT,
    S_FLEX,
    S_ARROW,
    S_DARROW,
    S_COLON,
    S_BAR,
    S_EQUAL,
    S_OPAQUE,
    S_MUL,
    S_DIV,
    S_PLUS,
    S_MINUS,
    S_INT,
    S_CHAR,
    S_STRING,
    S_REF,
    S_LIST,
    S_BOOL,
    S_EXN,
    S_NIL,
    S_CONS,
    S_TRUE,
    S_FALSE,
    S_UNIT
);

#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Symbol {
    Interned(u32),
    Gensym(u32),
    Tuple(u32),
}

impl Symbol {
    pub const fn dummy() -> Self {
        Symbol::Gensym(std::u32::MAX)
    }

    pub const fn gensym(n: u32) -> Symbol {
        Symbol::Gensym(n)
    }

    pub fn builtin(self) -> bool {
        match self {
            Symbol::Interned(n) if n <= S_TOTAL_GLOBALS => true,
            _ => false,
        }
    }

    pub const fn tuple_field(idx: u32) -> Symbol {
        Symbol::Tuple(idx)
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
        assert_eq!(S_FUNCTOR, i.intern("functor".into()));
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
        assert_eq!(S_SIG, i.intern("sig".into()));
        assert_eq!(S_SIGNATURE, i.intern("signature".into()));
        assert_eq!(S_STRUCT, i.intern("struct".into()));
        assert_eq!(S_STRUCTURE, i.intern("structure".into()));
        assert_eq!(S_DOT, i.intern(".".into()));
        assert_eq!(S_FLEX, i.intern("...".into()));
        assert_eq!(S_ARROW, i.intern("->".into()));
        assert_eq!(S_DARROW, i.intern("=>".into()));
        assert_eq!(S_COLON, i.intern(":".into()));
        assert_eq!(S_BAR, i.intern("|".into()));
        assert_eq!(S_EQUAL, i.intern("=".into()));
        assert_eq!(S_OPAQUE, i.intern(":>".into()));
        assert_eq!(S_MUL, i.intern("*".into()));
        assert_eq!(S_DIV, i.intern("\\".into()));
        assert_eq!(S_PLUS, i.intern("+".into()));
        assert_eq!(S_MINUS, i.intern("-".into()));
        assert_eq!(S_INT, i.intern("int".into()));
        assert_eq!(S_CHAR, i.intern("char".into()));
        assert_eq!(S_STRING, i.intern("string".into()));
        assert_eq!(S_REF, i.intern("ref".into()));
        assert_eq!(S_LIST, i.intern("list".into()));
        assert_eq!(S_BOOL, i.intern("bool".into()));
        assert_eq!(S_EXN, i.intern("exn".into()));
        assert_eq!(S_NIL, i.intern("nil".into()));
        assert_eq!(S_CONS, i.intern("::".into()));
        assert_eq!(S_TRUE, i.intern("true".into()));
        assert_eq!(S_FALSE, i.intern("false".into()));
        assert_eq!(S_UNIT, i.intern("unit".into()));
        // assert_eq!(S_TOTAL_GLOBALS, S_UNIT.0);
        i
    }

    pub fn intern(&mut self, s: String) -> Symbol {
        if let Some(sym) = self.symbols.get(&s) {
            return *sym;
        }

        let sym = Symbol::Interned(self.strings.len() as u32);
        self.strings.push(s.clone());
        self.symbols.insert(s, sym);
        sym
    }

    pub fn get(&self, symbol: Symbol) -> Option<&str> {
        match symbol {
            Symbol::Interned(n) => self.strings.get(n as usize).map(|s| s.as_ref()),
            _ => None,
        }
    }
}

fn fresh_name(x: u32) -> String {
    let last = ((x % 26) as u8 + 'a' as u8) as char;
    (0..x / 26)
        .map(|_| 'z')
        .chain(std::iter::once(last))
        .collect::<String>()
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Symbol::Gensym(n) => return write!(f, "{}", fresh_name(*n)),
            Symbol::Tuple(n) => return write!(f, "{}", n),
            Symbol::Interned(n) => INTERNER.with(|i| match i.try_borrow() {
                Ok(b) => match b.get(*self) {
                    Some(s) => write!(f, "{}", s),
                    None => write!(f, "?"),
                },
                Err(_) => write!(f, "{}", n),
            }),
        }
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
