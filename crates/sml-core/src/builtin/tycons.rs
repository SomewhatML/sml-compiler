use crate::*;
use sml_util::interner::*;

pub const T_ARROW: Tycon = Tycon::new(S_ARROW, 2, 0);
pub const T_UNIT: Tycon = Tycon::new(S_UNIT, 0, 0);
pub const T_CHAR: Tycon = Tycon::new(S_CHAR, 0, 0);
pub const T_INT: Tycon = Tycon::new(S_INT, 0, 0);
pub const T_STRING: Tycon = Tycon::new(S_STRING, 0, 0);
pub const T_REF: Tycon = Tycon::new(S_REF, 1, 0);
pub const T_LIST: Tycon = Tycon::new(S_LIST, 1, 0);
pub const T_BOOL: Tycon = Tycon::new(S_BOOL, 0, 0);
pub const T_EXN: Tycon = Tycon::new(S_EXN, 0, 0);

pub const T_BUILTINS: [Tycon; 9] = [
    T_ARROW, T_UNIT, T_CHAR, T_INT, T_STRING, T_REF, T_LIST, T_BOOL, T_EXN,
];
