use crate::*;
use sml_util::interner::*;

pub const T_ARROW: Tycon = Tycon::new(S_ARROW, 2);
pub const T_UNIT: Tycon = Tycon::new(S_UNIT, 0);
pub const T_CHAR: Tycon = Tycon::new(S_CHAR, 0);
pub const T_INT: Tycon = Tycon::new(S_INT, 0);
pub const T_STRING: Tycon = Tycon::new(S_STRING, 0);
pub const T_REF: Tycon = Tycon::new(S_REF, 1);

pub const T_BUILTINS: [Tycon; 6] = [T_ARROW, T_UNIT, T_CHAR, T_INT, T_STRING, T_REF];
