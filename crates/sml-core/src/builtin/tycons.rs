use crate::*;
use sml_util::interner::*;

pub const T_ARROW: Tycon = Tycon::new(S_ARROW, 2, Span::zero());
pub const T_UNIT: Tycon = Tycon::new(S_UNIT, 0, Span::zero());
pub const T_CHAR: Tycon = Tycon::new(S_CHAR, 0, Span::zero());
pub const T_INT: Tycon = Tycon::new(S_INT, 0, Span::zero());
pub const T_STRING: Tycon = Tycon::new(S_STRING, 0, Span::zero());
