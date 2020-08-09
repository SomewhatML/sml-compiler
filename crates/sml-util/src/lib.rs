pub mod diagnostics;
pub mod hasher;
pub mod interner;
pub mod pretty_print;
pub mod span;

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash, Ord)]
pub enum Const {
    Unit,
    Int(usize),
    Char(char),
    String(interner::Symbol),
}
