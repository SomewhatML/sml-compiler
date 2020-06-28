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
pub struct Primitive {
    pub sym: Symbol,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum DeclKind {
    /// If `N` > 1, then we have potentially mutually recursive datatype
    /// definitions
    Datatype(Vec<Datatype>),
    /// If `N` > 1, then we have mutually rec. type defs
    Type(Vec<Typebind>),
    /// Allow for mutually recursive function defs:
    /// fun 'tyvars fnbindings1
    ///             ...
    ///      and    fnbindingsN
    Function(Vec<Symbol>, Vec<Fun>),
    Value(Pat, Expr),
    Exception(Vec<Variant>),
    Fixity(Fixity, u8, Symbol),
    Local(Box<Decl>, Box<Decl>),
    Seq(Vec<Decl>),
    Do(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum TypeKind {
    /// Type variable
    Var(Symbol),
    /// Constructor, with applied arguments
    Con(Symbol, Vec<Type>),
    /// Record type
    Record(Vec<Row<Type>>),
    /* Universally quantified type
     * Univ(Symbol, Box<Type>), */
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum ExprKind {
    Andalso(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Case(Box<Expr>, Vec<Rule>),
    Const(Const),
    Constraint(Box<Expr>, Box<Type>),
    FlatApp(Vec<Expr>),
    Fn(Vec<Rule>),
    Handle(Box<Expr>, Vec<Rule>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Let(Vec<Decl>, Box<Expr>),
    List(Vec<Expr>),
    Orelse(Box<Expr>, Box<Expr>),
    Primitive(Primitive),
    Raise(Box<Expr>),
    Record(Vec<Row<Expr>>),
    Selector(Symbol),
    Seq(Vec<Expr>),
    Var(Symbol),
    While(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum PatKind {
    /// Algebraic datatype constructor, along with binding pattern
    App(Symbol, Box<Pat>),
    /// Type ascription
    Ascribe(Box<Pat>, Box<Type>),
    /// Constant
    Const(Const),
    /// A collection of pat applications, possibly including infix constructors
    FlatApp(Vec<Pat>),
    /// List pattern [pat1, ... patN]
    List(Vec<Pat>),
    /// Record pattern { label1, label2 }
    Record(Vec<Row<Pat>>),

    /// Variable binding
    Variable(Symbol),
    /// Wildcard
    Wild,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct FnBinding {
    pub name: Symbol,
    pub pats: Vec<Pat>,
    pub res_ty: Option<Type>,
    pub expr: Expr,
}

/// Rule of a case expression
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Rule {
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
pub type Fun = Spanned<Vec<FnBinding>>;

/// Interestingly, MLton immediately desugars tuples during parsing, rather than
/// during elaboration. We do the same
pub fn make_record(v: Vec<Expr>) -> ExprKind {
    ExprKind::Record(
        v.into_iter()
            .enumerate()
            .map(|(idx, ex)| Row {
                label: Symbol::tuple_field(1 + idx as u32),
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
                label: Symbol::tuple_field(1 + idx as u32),
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
                label: Symbol::tuple_field(1 + idx as u32),
                span: ex.span,
                data: ex,
            })
            .collect(),
    )
}
