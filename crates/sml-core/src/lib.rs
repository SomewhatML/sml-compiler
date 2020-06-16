use sml_frontend::ast::Const;
use sml_util::interner::Symbol;
pub mod builtin;
pub mod elaborate;

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct Local {
    name: Symbol,
    idx: usize,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Type {
    Var(Local),
    Con(Tycon, Vec<Type>),
    Record(Vec<Row<Type>>),
    Exist(usize),
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct Tycon {
    name: Symbol,
    arity: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub struct Constructor {
    name: Symbol,
    type_id: TypeId,
    tag: u32,
}

#[derive(Clone, Debug)]
pub enum Scheme {
    Mono(Type),
    Poly(Type, Vec<Symbol>),
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    App(Box<Expr>, Box<Expr>),
    Con(Constructor, Vec<Type>),
    Case(Box<Expr>),
    Const(Const),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub expr: ExprKind,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub enum Decl {}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Row<T> {
    pub label: Symbol,
    pub data: T,
}

impl Tycon {
    pub const fn new(name: Symbol, arity: usize) -> Tycon {
        Tycon { name, arity }
    }
}

impl Scheme {
    pub fn arity(&self) -> usize {
        match self {
            Scheme::Mono(_) => 0,
            Scheme::Poly(_, tyvars) => tyvars.len(),
        }
    }

    pub fn apply(&self, args: Vec<Type>) -> Type {
        unimplemented!()
    }

    pub fn new(ty: Type, tyvars: Vec<Symbol>) -> Scheme {
        match tyvars.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(ty, tyvars),
        }
    }
}

impl Type {
    pub fn fresh_tyvars(arity: usize) -> Vec<Type> {
        (0..arity)
            .rev()
            .map(|idx| {
                Type::Var(Local {
                    name: Symbol::dummy(),
                    idx,
                })
            })
            .collect()
    }

    pub fn arrow(a: Type, b: Type) -> Type {
        Type::Con(builtin::tycons::T_ARROW, vec![a, b])
    }
}
