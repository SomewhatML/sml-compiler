use sml_frontend::ast::Const;
use sml_util::interner::Symbol;
use sml_util::span::Span;
pub mod builtin;
pub mod elaborate;
pub mod inference;

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeVar(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct Local {
    name: Symbol,
    idx: usize,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Type {
    Var(TypeVar),
    Con(Tycon, Vec<Type>),
    Record(Vec<Row<Type>>),
    // Exist(usize),
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq)]
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
    Poly(Type, Vec<TypeVar>),
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    App(Box<Expr>, Box<Expr>),
    Case(Box<Expr>, Vec<Rule>),
    Con(Constructor, Vec<Type>),
    Const(Const),
    Handle(Box<Expr>, Vec<Rule>),
    Lambda(Symbol, Box<Expr>),
    Let(Vec<Decl>, Box<Expr>),
    List(Vec<Expr>),
    Raise(Box<Expr>),
    Record(Vec<Row<Expr>>),
    Seq(Vec<Expr>),
    Var(Symbol),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub expr: ExprKind,
    pub ty: Type,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    /// Constructor application
    App(Constructor, Option<Box<Pat>>),
    /// Constant
    Const(Const),
    /// Literal list
    List(Vec<Pat>),
    /// Record
    Record(Vec<Row<Pat>>),
    /// Variable binding
    Var(Symbol),
    /// Wildcard
    Wild,
}

#[derive(Clone, Debug)]
pub struct Pat {
    pub pat: PatKind,
    pub ty: Type,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Rule {
    pub pat: Pat,
    pub exp: Expr,
}

#[derive(Clone, Debug)]
pub enum Decl {}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Row<T> {
    pub label: Symbol,
    pub data: T,
    pub span: Span,
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

    pub fn instantiate(&self) -> Type {
        match self {
            Scheme::Mono(ty) => ty.clone(),
            Scheme::Poly(ty, _) => ty.clone(),
        }
    }

    pub fn new(ty: Type, tyvars: Vec<TypeVar>) -> Scheme {
        match tyvars.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(ty, tyvars),
        }
    }
}

impl Type {
    // pub fn fresh_tyvars(arity: usize) -> Vec<Type> {
    //     (0..arity)
    //         .rev()
    //         .map(|idx| {
    //             Type::Var(Local {
    //                 name: Symbol::dummy(),
    //                 idx,
    //             })
    //         })
    //         .collect()
    // }

    pub fn arrow(a: Type, b: Type) -> Type {
        Type::Con(builtin::tycons::T_ARROW, vec![a, b])
    }

    pub fn de_arrow(self) -> Option<(Type, Type)> {
        match self {
            Type::Con(builtin::tycons::T_ARROW, mut v) => {
                let a = v.remove(0);
                let r = v.remove(0);
                Some((a, r))
            }
            _ => None,
        }
    }

    fn ftv(&self, set: &mut Vec<TypeVar>) {
        match self {
            Type::Var(x) => {
                set.push(*x);
            }
            Type::Record(rows) => {
                for row in rows {
                    row.data.ftv(set);
                }
            }
            Type::Con(_, tys) => {
                for ty in tys {
                    ty.ftv(set);
                }
            }
        }
    }
}

impl Pat {
    pub fn new(pat: PatKind, ty: Type, span: Span) -> Pat {
        Pat { pat, ty, span }
    }
}

impl<T> Row<T> {
    pub fn fmap<S, F: FnOnce(T) -> S>(self, f: F) -> Row<S> {
        Row {
            label: self.label,
            span: self.span,
            data: f(self.data),
        }
    }
}

impl<T, E> Row<Result<T, E>> {
    pub fn flatten(self) -> Result<Row<T>, E> {
        Ok(Row {
            label: self.label,
            span: self.span,
            data: self.data?,
        })
    }
}
