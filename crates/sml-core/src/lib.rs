use sml_util::span::Span;
pub mod elaborate;

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct TypId(pub u32);
#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct ExpId(pub u32);

pub enum Type {}

#[derive(Copy, Clone, Debug, Default, PartialEq, PartialOrd, Eq, Hash)]
pub struct Constructor {
    type_id: TypId,
    tag: u32,
}

pub enum ExpKind {
    App(Box<Exp>, Box<Exp>),
    Con(Constructor, Vec<Type>),
}

pub struct Exp {
    pub kind: ExpKind,
    pub ty: Type,
    pub span: Span,
}
