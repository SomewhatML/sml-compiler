//! CoreML - explicitly typed Standard ML
//!
//! After elaboration from the (probably untyped) AST, the following invariants
//! should hold, assuming that no errors were reported:
//!
//! *   Type safety: all expressions, patterns, and declarations are well-typed
//!
//! *   Annotaton: all expressions and patterns are explicitly annotated with
//!     either a concrete type, or a type variabel
//!
//! *   Decision tree optimization: all `case`, `fn`, and `handle` expressions,
//!     as well as `fun` declarations, have undergone a source -> source
//!     rewrite to transform them into optimal decision trees, such that each
//!     scrutinized expression is tested only once. Furthermore, match arm
//!     bodies have been abstracted into functions taking any pattern-bound
//!     variables as arguments, and lifted into an enclosing scope to prevent
//!     code blow-up.

use sml_util::interner::Symbol;
use sml_util::span::Span;
use sml_util::Const;
use std::collections::HashMap;
use types::{Constructor, Scheme, Tycon, Type, TypeVar};

pub mod alpha;
pub mod arenas;
pub mod builtin;
pub mod check;
pub mod core_pp;
pub mod elaborate;
pub mod match_compile;
pub mod types;

pub type Var<'a> = (Symbol, &'a Type<'a>);

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypeId(pub u32);

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExprId(pub u32);

pub enum ExprKind<'ar> {
    App(Expr<'ar>, Expr<'ar>),
    Case(Var<'ar>, Vec<Rule<'ar>>),
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
    Var(Symbol, Vec<&'ar Type<'ar>>),
}

#[derive(Copy, Clone)]
pub struct Expr<'ar> {
    pub kind: &'ar ExprKind<'ar>,
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
    /// Record
    Record(SortedRecord<Pat<'ar>>),
    /// Variable binding
    Var(Symbol),
    /// Wildcard
    Wild,
}

#[derive(Copy, Clone)]
pub struct Pat<'ar> {
    pub kind: &'ar PatKind<'ar>,
    pub ty: &'ar Type<'ar>,
    pub span: Span,
}

#[derive(Copy, Clone)]
pub struct Rule<'ar> {
    pub pat: Pat<'ar>,
    pub expr: Expr<'ar>,
}

#[derive(Clone)]
pub struct Datatype<'ar> {
    pub tycon: Tycon,
    pub tyvars: Vec<usize>,
    pub constructors: Vec<(Constructor, Option<&'ar Type<'ar>>)>,
}

pub enum Decl<'ar> {
    Datatype(Vec<Datatype<'ar>>),
    Fun(Vec<usize>, Vec<(Symbol, Lambda<'ar>)>),
    Val(Vec<usize>, Rule<'ar>),
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
    pub fn new(kind: &'ar ExprKind<'ar>, ty: &'ar Type<'ar>, span: Span) -> Expr<'ar> {
        Expr { kind, ty, span }
    }

    pub fn non_expansive(&self) -> bool {
        match &self.kind {
            ExprKind::Con(builtin::constructors::C_REF, _) => false,
            ExprKind::Con(_, _) => true,
            ExprKind::Const(_) => true,
            ExprKind::Lambda(_) => true,
            ExprKind::Var(_, _) => true,
            ExprKind::Primitive(_) => true,
            ExprKind::Record(rec) => rec.iter().all(|r| r.data.non_expansive()),
            ExprKind::List(exprs) => exprs.iter().all(|r| r.non_expansive()),
            _ => false,
        }
    }

    pub fn as_symbol(&self) -> Symbol {
        match &self.kind {
            ExprKind::Var(s, _) => *s,
            _ => panic!("BUG: Expr::as_symbol()"),
        }
    }
}

impl<'ar> Pat<'ar> {
    pub fn new(kind: &'ar PatKind<'ar>, ty: &'ar Type<'ar>, span: Span) -> Pat<'ar> {
        Pat { kind, ty, span }
    }

    pub fn flexible(&self) -> bool {
        if self.ty.unresolved_flex() {
            true
        } else {
            match &self.kind {
                PatKind::App(_, Some(p)) => p.flexible(),
                PatKind::Record(rows) => rows.iter().any(|r| r.data.flexible()),
                _ => false,
            }
        }
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

    pub fn contains(&self, lab: &Symbol) -> Option<&Row<T>> {
        for row in self.iter() {
            if &row.label == lab {
                return Some(row);
            }
        }
        None
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
