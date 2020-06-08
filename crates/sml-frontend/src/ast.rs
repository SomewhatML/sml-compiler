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
pub struct Datatype {
    pub tycon: Symbol,
    pub tyvars: Vec<Symbol>,
    pub constructors: Vec<Variant>,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Typebind {
    pub tycon: Symbol,
    pub tyvars: Vec<Symbol>,
    pub ty: Type,
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub enum Fixity {
    Infix,
    Infixr,
    Nonfix,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum DeclKind {
    Datatype(Vec<Datatype>),
    Type(Vec<Typebind>),
    Function(Symbol, Function),
    Value(Pat, Expr),
    Exception(Vec<Variant>),
    Fixity(Fixity, u8, Symbol),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum TypeKind {
    /// Type variable
    Var(Symbol),
    /// Constructor, with applied arguments
    Con(Symbol, Vec<Type>),
    /// Record type
    Record(Vec<Row<Type>>),
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
    Record(Vec<Row<Expr>>),
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
    /// Record pattern { label1, label2 }
    Record(Vec<Row<Pat>>),
    /// List pattern [pat1, ... patN]
    List(Vec<Pat>),
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
pub struct Row<T> {
    pub label: Symbol,
    pub data: T,
    pub span: Span,
}

pub type Decl = Spanned<DeclKind>;
pub type Type = Spanned<TypeKind>;
pub type Expr = Spanned<ExprKind>;
pub type Pat = Spanned<PatKind>;
pub type Variant = Row<Option<Type>>;

/// Interestingly, MLton immediately desugars tuples during parsing, rather than during elaboration.
/// We do the same
pub fn make_record(v: Vec<Expr>) -> ExprKind {
    ExprKind::Record(
        v.into_iter()
            .enumerate()
            .map(|(idx, ex)| Row {
                label: Symbol::tuple_field(idx as u32),
                span: ex.span,
                data: ex,
            })
            .collect(),
    )
}

pub fn make_record_type(v: Vec<Type>) -> TypeKind {
    TypeKind::Record(
        v.into_iter()
            .enumerate()
            .map(|(idx, ex)| Row {
                label: Symbol::tuple_field(idx as u32),
                span: ex.span,
                data: ex,
            })
            .collect(),
    )
}

pub fn make_record_pat(v: Vec<Pat>) -> PatKind {
    PatKind::Record(
        v.into_iter()
            .enumerate()
            .map(|(idx, ex)| Row {
                label: Symbol::tuple_field(idx as u32),
                span: ex.span,
                data: ex,
            })
            .collect(),
    )
}
