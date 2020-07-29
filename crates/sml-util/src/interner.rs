use std::cell::RefCell;
use std::collections::HashMap;
use std::pin::Pin;

thread_local! {
    pub static INTERNER: RefCell<Interner> = RefCell::new(Interner::with_capacity(512));
}

macro_rules! globals {
    (@step $idx:expr, ) => {
        pub const S_TOTAL_GLOBALS: usize = $idx;
    };
    (@step $idx:expr, $it:ident, $($rest:ident,)*) => {
        pub const $it: Symbol = Symbol::Builtin($idx as u32);
        globals!(@step $idx+1usize, $($rest,)*);
    };
    ($($name:ident),+) => {
       globals!(@step 0usize, $($name,)*);
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
    S_PRIM,
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
    S_UNIT,
    S_MATCH
);

const BUILTIN_STRS: [&'static str; S_TOTAL_GLOBALS as usize] = [
    "abstype",
    "and",
    "andalso",
    "as",
    "case",
    "datatype",
    "do",
    "else",
    "end",
    "exception",
    "fn",
    "fun",
    "functor",
    "handle",
    "if",
    "in",
    "infix",
    "infixr",
    "let",
    "local",
    "nonfix",
    "of",
    "op",
    "open",
    "orelse",
    "primitive",
    "raise",
    "rec",
    "then",
    "type",
    "val",
    "with",
    "withtype",
    "while",
    "sig",
    "signature",
    "struct",
    "structure",
    ".",
    "...",
    "->",
    "=>",
    ":",
    "|",
    "=",
    ":>",
    "*",
    "\\",
    "+",
    "-",
    "int",
    "char",
    "string",
    "ref",
    "list",
    "bool",
    "exn",
    "nil",
    "::",
    "true",
    "false",
    "unit",
    "Match",
];

#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub enum Symbol {
    Builtin(u32),
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
            Symbol::Builtin(_) => true,
            _ => false,
        }
    }

    pub const fn tuple_field(idx: u32) -> Symbol {
        Symbol::Tuple(idx)
    }
}

#[derive(Clone, PartialEq)]
pub struct Interner {
    symbols: HashMap<&'static str, Symbol>,
    strings: Vec<Pin<Box<str>>>,
}

impl Interner {
    pub fn with_capacity(n: usize) -> Interner {
        let mut i = Interner {
            symbols: HashMap::with_capacity(n),
            strings: Vec::with_capacity(n),
        };
        for (idx, builtin) in BUILTIN_STRS.iter().enumerate() {
            i.symbols.insert(builtin, Symbol::Builtin(idx as u32));
        }
        i
    }

    pub fn intern(&mut self, s: &str) -> Symbol {
        if let Some(sym) = self.symbols.get(s.as_ref() as &str) {
            return *sym;
        }

        let sym = Symbol::Interned(self.strings.len() as u32);
        let pinned = Pin::new(String::into_boxed_str(s.into()));
        let ptr: &'static str = unsafe { std::mem::transmute(Pin::get_ref(pinned.as_ref())) };

        self.strings.push(pinned);
        self.symbols.insert(ptr, sym);
        sym
    }

    pub fn get(&self, symbol: Symbol) -> Option<&str> {
        match symbol {
            Symbol::Interned(n) => self
                .strings
                .get(n as usize)
                .map(|s| Pin::get_ref(s.as_ref())),
            Symbol::Builtin(n) => BUILTIN_STRS.get(n as usize).copied(),
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
            Symbol::Builtin(n) => write!(f, "{}", BUILTIN_STRS[*n as usize]),
            Symbol::Gensym(n) => write!(f, "{}", fresh_name(*n)),
            Symbol::Tuple(n) => write!(f, "{}", n),
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
