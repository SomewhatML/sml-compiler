use sml_util::interner::Symbol;
use sml_util::span::{Span, Spanned};

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub enum Const {
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
    Andalso(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Case(Box<Expr>, Vec<Arm>),
    Const(Const),
    Constraint(Box<Expr>, Box<Type>),
    FlatApp(Vec<Expr>),
    Fn(Vec<Arm>),
    Handle(Box<Expr>, Vec<Arm>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(Vec<Decl>, Box<Expr>),
    List(Vec<Expr>),
    Orelse(Box<Expr>, Box<Expr>),
    Raise(Box<Expr>),
    Record(Vec<Field>),
    Selector(Symbol),
    Seq(Vec<Expr>),
    Var(Symbol),
    While(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum PatKind {
    /// Wildcard
    Any,
    /// Constant
    Const(Const),
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

/// Interestingly, MLton immediately desugars tuples during parsing, rather than during elaboration.
/// We do the same
pub fn make_record(v: Vec<Expr>) -> ExprKind {
    ExprKind::Record(
        v.into_iter()
            .enumerate()
            .map(|(idx, ex)| Field {
                label: Symbol::tuple_field(idx as u32),
                span: ex.span,
                expr: ex,
            })
            .collect(),
    )
}
