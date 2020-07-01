use sml_frontend::ast::Const;
use sml_util::interner::Symbol;
use sml_util::span::Span;
use std::collections::HashMap;
use std::fmt;

pub mod builtin;
pub mod check;
pub mod elaborate;
pub mod types;
use types::{Constructor, Scheme, Tycon, Type, TypeVar};

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Clone)]
pub enum ExprKind {
    App(Box<Expr>, Box<Expr>),
    Case(Box<Expr>, Vec<Rule>),
    Con(Constructor, Vec<Type>),
    Const(Const),
    Handle(Box<Expr>, Vec<Rule>),
    Lambda(Box<Lambda>),
    Let(Vec<Decl>, Box<Expr>),
    List(Vec<Expr>),
    Primitive(Symbol),
    Raise(Box<Expr>),
    Record(Vec<Row<Expr>>),
    Seq(Vec<Expr>),
    Var(Symbol),
}

#[derive(Clone)]
pub struct Expr {
    pub expr: ExprKind,
    pub ty: Type,
    pub span: Span,
}

#[derive(Clone)]
pub struct Lambda {
    pub arg: Symbol,
    pub ty: Type,
    pub body: Expr,
}

#[derive(Clone)]
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
pub struct Datatype {
    tycon: Tycon,
    tyvars: Vec<usize>,
    constructors: Vec<(Constructor, Option<Type>)>,
}

// #[derive(Clone, Debug)]
// pub struct ValueBinding {
//     tyvars: Vec<usize>,
//     vbs: Vec<Rule>,
//     rvbs: Vec<Lambda>,
// }

#[derive(Clone, Debug)]
pub enum Decl {
    Datatype(Datatype),
    Fun(Vec<usize>, Vec<Lambda>),
    Val(Rule),
    Exn(Constructor, Option<Type>),
}

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

    pub fn non_expansive(&self) -> bool {
        match &self.expr {
            ExprKind::Con(builtin::constructors::C_REF, _) => false,
            ExprKind::Con(_, _) => true,
            ExprKind::Const(_) => true,
            ExprKind::Lambda(_) => true,
            ExprKind::Var(_) => true,
            ExprKind::Primitive(_) => true,
            ExprKind::Record(rows) => rows.iter().all(|r| r.data.non_expansive()),
            ExprKind::List(exprs) => exprs.iter().all(|r| r.non_expansive()),
            _ => false,
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

impl fmt::Debug for ExprKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExprKind::*;
        match self {
            App(e1, e2) => write!(f, "{:?} {:?}", e1, e2),
            Case(casee, rules) => write!(
                f,
                "case {:?} of\n{}",
                casee,
                rules
                    .into_iter()
                    .map(|r| format!("| {:?} => {:?}\n", r.pat.pat, r.expr))
                    .collect::<String>()
            ),
            Con(con, tys) => write!(f, "{:?} [{:?}]", con, tys),
            Const(c) => write!(f, "{:?}", c),
            Handle(expr, rules) => write!(
                f,
                "{:?} handle {:?}",
                expr,
                rules
                    .into_iter()
                    .map(|r| format!("| {:?} => {:?}\n", r.pat, r.expr))
                    .collect::<String>()
            ),
            Lambda(lam) => write!(f, "{:?}", lam),
            Let(decls, body) => write!(f, "let {:?} in {:?} end", decls, body),
            List(exprs) => write!(f, "{:?}", exprs),
            Primitive(sym) => write!(f, "primitive {:?}", sym),
            Raise(e) => write!(f, "raise {:?}", e),
            Record(rows) => write!(
                f,
                "{{ {} }}",
                rows.into_iter()
                    .map(|r| format!("{:?}={:?}", r.label, r.data))
                    .collect::<Vec<String>>()
                    .join(",")
            ),
            Seq(exprs) => write!(f, "{:?}", exprs),
            Var(s) => write!(f, "{:?}", s),
        }
    }
}

impl fmt::Debug for PatKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use PatKind::*;
        match self {
            App(e1, e2) => write!(f, "{:?} {:?}", e1, e2),
            // Con(con, tys) => write!(f, "{:?} [{:?}]", con, tys),
            Const(c) => write!(f, "{:?}", c),
            Record(rows) => write!(
                f,
                "{{ {} }}",
                rows.into_iter()
                    .map(|r| format!("{:?}={:?}", r.label, r.data))
                    .collect::<Vec<String>>()
                    .join(",")
            ),
            List(exprs) => write!(f, "{:?}", exprs),
            Var(s) => write!(f, "{:?}", s),
            Wild => write!(f, "_"),
        }
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?} : {:?}]", self.expr, self.ty)
    }
}

impl fmt::Debug for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn {:?} => {:?}", self.arg, self.body)
    }
}
