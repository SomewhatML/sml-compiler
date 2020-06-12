use sml_util::interner::Symbol;
use sml_util::span::Span;
pub mod builtin;
pub mod elaborate;

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

pub enum Type {}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct Tycon {
    name: Symbol,
    arity: usize,
    span: Span,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct Constructor {
    type_id: TypeId,
    tag: u32,
}

pub enum ExprKind {
    App(Box<Exp>, Box<Exp>),
    Con(Constructor, Vec<Type>),
}

pub struct Exp {
    pub expr: ExprKind,
    pub ty: Type,
    pub span: Span,
}

impl Tycon {
    pub const fn new(name: Symbol, arity: usize, span: Span) -> Tycon {
        Tycon { name, arity, span }
    }
}
