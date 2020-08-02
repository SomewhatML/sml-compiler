use sml_util::interner::{Interner, Symbol};

pub struct PrettyPrinter<'i> {
    indent: usize,
    spaces: usize,
    interner: &'i Interner,
}
