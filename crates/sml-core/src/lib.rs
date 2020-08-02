use sml_frontend::ast::Const;
use sml_util::interner::Symbol;
use sml_util::span::Span;
use std::collections::HashMap;
use std::fmt;

pub mod arenas;
pub mod builtin;
pub mod check;
pub mod elaborate;
pub mod match_compile;
pub mod monomorphize;
pub mod pretty_print;
pub mod types;
use types::{Constructor, Scheme, Tycon, Type, TypeVar};

pub use arenas::CoreArena;

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

pub enum ExprKind<'ar> {
    App(Expr<'ar>, Expr<'ar>),
    Case(Expr<'ar>, Vec<Rule<'ar>>),
    Con(Constructor, Vec<&'ar Type<'ar>>),
    Const(Const),
    /// Handle: try, bound var, case expr
    Handle(Expr<'ar>, Symbol, Expr<'ar>),
    Lambda(Lambda<'ar>),
    Let(Vec<Decl<'ar>>, Expr<'ar>),
    List(Vec<Expr<'ar>>),
    Primitive(Symbol),
    Raise(Expr<'ar>),
    Record(Vec<Row<Expr<'ar>>>),
    Seq(Vec<Expr<'ar>>),
    Var(Symbol),
}

#[derive(Copy, Clone)]
pub struct Expr<'ar> {
    pub expr: &'ar ExprKind<'ar>,
    pub ty: &'ar Type<'ar>,
    pub span: Span,
}

#[derive(Copy, Clone)]
pub struct Lambda<'ar> {
    pub arg: Symbol,
    pub ty: &'ar Type<'ar>,
    pub body: Expr<'ar>,
}

pub enum PatKind<'ar> {
    /// Constructor application
    App(Constructor, Option<Pat<'ar>>),
    /// Constant
    Const(Const),
    /// Literal list
    // List(Vec<Pat<'ar>>),
    /// Record
    Record(SortedRecord<Pat<'ar>>),
    /// Variable binding
    Var(Symbol),
    /// Wildcard
    Wild,
}

#[derive(Copy, Clone)]
pub struct Pat<'ar> {
    pub pat: &'ar PatKind<'ar>,
    pub ty: &'ar Type<'ar>,
    pub span: Span,
}

#[derive(Copy, Clone)]
pub struct Rule<'ar> {
    pub pat: Pat<'ar>,
    pub expr: Expr<'ar>,
}

#[derive(Clone, Debug)]
pub struct Datatype<'ar> {
    pub tycon: Tycon,
    pub tyvars: Vec<usize>,
    pub constructors: Vec<(Constructor, Option<&'ar Type<'ar>>)>,
}

pub enum Decl<'ar> {
    Datatype(Datatype<'ar>),
    Fun(Vec<usize>, Vec<(Symbol, Lambda<'ar>)>),
    Val(Rule<'ar>),
    Exn(Constructor, Option<&'ar Type<'ar>>),
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct Row<T> {
    pub label: Symbol,
    pub data: T,
    pub span: Span,
}

#[derive(Clone)]
pub struct SortedRecord<T> {
    pub rows: Vec<Row<T>>,
}

impl<'ar> Expr<'ar> {
    pub fn new(expr: &'ar ExprKind<'ar>, ty: &'ar Type<'ar>, span: Span) -> Expr<'ar> {
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
            ExprKind::Record(rec) => rec.iter().all(|r| r.data.non_expansive()),
            ExprKind::List(exprs) => exprs.iter().all(|r| r.non_expansive()),
            _ => false,
        }
    }
}

impl<'ar> Pat<'ar> {
    pub fn new(pat: &'ar PatKind<'ar>, ty: &'ar Type<'ar>, span: Span) -> Pat<'ar> {
        Pat { pat, ty, span }
    }
}

impl<T> Row<T> {
    pub fn fmap<S, F: FnOnce(&T) -> S>(&self, f: F) -> Row<S> {
        Row {
            label: self.label,
            span: self.span,
            data: f(&self.data),
        }
    }
}

impl<T> SortedRecord<T> {
    pub fn new(mut rows: Vec<Row<T>>) -> SortedRecord<T> {
        rows.sort_by(|a, b| a.label.cmp(&b.label));
        SortedRecord { rows }
    }

    pub fn new_unchecked(rows: Vec<Row<T>>) -> SortedRecord<T> {
        SortedRecord { rows }
    }

    pub fn fmap<S, F: Fn(&T) -> S>(&self, f: F) -> SortedRecord<S> {
        let mut v = Vec::with_capacity(self.rows.len());
        for row in self.iter() {
            v.push(Row {
                label: row.label,
                span: row.span,
                data: f(&row.data),
            });
        }
        SortedRecord { rows: v }
    }

    pub fn iter(&self) -> std::slice::Iter<Row<T>> {
        self.rows.iter()
    }
}

impl<T> std::iter::IntoIterator for SortedRecord<T> {
    type Item = Row<T>;
    type IntoIter = std::vec::IntoIter<Row<T>>;
    fn into_iter(self) -> Self::IntoIter {
        self.rows.into_iter()
    }
}

impl<T> std::ops::Deref for SortedRecord<T> {
    type Target = Vec<Row<T>>;
    fn deref(&self) -> &Self::Target {
        &self.rows
    }
}
