use sml_frontend::ast::Const;
use sml_util::interner::Symbol;
use sml_util::span::Span;
use std::collections::HashMap;

pub mod builtin;
pub mod elaborate;
pub mod inference;
pub mod types;
use types::{Constructor, Scheme, Tycon, Type, TypeVar};

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct Local {
    name: Symbol,
    idx: usize,
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
    pub expr: Expr,
}

#[derive(Clone, Debug)]
pub enum Decl {}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Row<T> {
    pub label: Symbol,
    pub data: T,
    pub span: Span,
}

impl Expr {
    pub fn new(expr: ExprKind, ty: Type, span: Span) -> Expr {
        Expr { expr, ty, span }
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
