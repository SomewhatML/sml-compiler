use sml_util::interner::Symbol;
use sml_util::Const;

pub struct Var(pub Symbol, pub Type);

pub enum Expr {
    App(Var, Var),
    Case(Var, Vec<Rule>),
    Con(Constructor, Vec<Type>, Option<Var>),
    Const(Const),
    Handle(Block, Var, Block),
    Lambda(Lambda),
    PrimApp(Prim, Vec<Var>),
    Raise(Var),
    Tuple(Vec<Var>),
    Select(Var, usize),
    Var(Var),
}

pub struct Block {
    pub decls: Vec<Decl>,
    pub ret: Var,
}

impl Block {}

pub enum Tycon {
    Unit,
    Bool,
    Char,
    Int,
    String,
    List,
    Arrow,
    Ref,
    Exn,
    Tuple,
    Datatype(Symbol),
}

pub enum Type {
    Con(Tycon, Vec<Type>),
    Var(usize),
}

pub struct Lambda {
    pub arg: Var,
    pub body: Block,
}

pub enum Decl {
    Exn(Constructor, Option<Type>),
    Fun(Vec<(Symbol, Lambda)>),
    Mono(Var, Expr),
}

pub struct Constructor {
    pub name: Symbol,
    pub tycon: Tycon,
    pub tag: u8,
}

pub struct Rule;

pub struct Prim;
