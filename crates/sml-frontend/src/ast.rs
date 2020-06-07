use sml_util::interner::Symbol;
use sml_util::span::{Span, Spanned};

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub enum Literal {
    Unit,
    Int(usize),
    Char(char),
    String(Symbol),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum DeclKind {
    Datatype(Symbol, Vec<Symbol>, Spanned<Vec<Variant>>),
    Type(Symbol, Vec<Symbol>, Type),
    Function(Symbol, Function),
    Value(Pat, Expr),
    Infix(u8, Symbol),
    Infixr(u8, Symbol),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum TypeKind {
    /// Type variable
    Var(Symbol),
    /// Constructor, with applied arguments
    Con(Symbol, Vec<Type>),
    /// Tuple type
    Product(Vec<Type>),
    /// Record type
    Record(Vec<Row>),
    /// Universally quantified type
    Univ(Symbol, Box<Type>),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum ExprKind {
    Lit(Literal),
    Var(Symbol),
    Abs(Box<Pat>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    FlatApp(Vec<Expr>),
    Ann(Box<Expr>, Box<Type>),
    Record(Vec<Field>),
    Tuple(Vec<Expr>),
    Projection(Box<Expr>, Box<Expr>),
    Case(Box<Expr>, Vec<Arm>),
    Let(Vec<Decl>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum PatKind {
    /// Wildcard
    Any,
    /// Literal
    Lit(Literal),
    /// Type ascription
    Ascribe(Box<Pat>, Box<Type>),
    /// Variable binding
    Variable(Symbol),
    /// Tuple of pattern bindings (_, x)
    Product(Vec<Pat>),
    /// Record pattern { label1, label2 }
    Record(Vec<Pat>),
    /// A collection of pat applications, possibly including infix constructors
    FlatApp(Vec<Pat>),
    /// Algebraic datatype constructor, along with binding pattern
    App(Box<Pat>, Box<Pat>),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Function {
    pub ty: Option<Type>,
    pub body: Vec<FnBinding>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct FnBinding {
    pub pats: Vec<Pat>,
    pub expr: Expr,
}

/// Arm of a case expression
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Arm {
    pub pat: Pat,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Field {
    pub label: Symbol,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Variant {
    pub label: Symbol,
    pub ty: Vec<Type>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Row {
    pub label: Symbol,
    pub ty: Type,
    pub span: Span,
}

pub type Decl = Spanned<DeclKind>;
pub type Type = Spanned<TypeKind>;
pub type Expr = Spanned<ExprKind>;
pub type Pat = Spanned<PatKind>;
