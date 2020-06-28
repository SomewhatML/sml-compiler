//! Beware that type_ids are hardcoded in this file, corresponding to the order
//! of the builtin type constructors defined in `tycons.rs`. Changing the order
//! there, or the order in which the constructors are defined in the environment
//! may have disastrous effects.
use crate::*;
use sml_util::interner::*;

// datatype 'a list = nil | :: of 'a * 'a list
pub const C_NIL: Constructor = Constructor {
    name: S_NIL,
    type_id: TypeId(6),
    tag: 0,
};
pub const C_CONS: Constructor = Constructor {
    name: S_CONS,
    type_id: TypeId(6),
    tag: 1,
};

// datatype bool = true | false
pub const C_TRUE: Constructor = Constructor {
    name: S_TRUE,
    type_id: TypeId(7),
    tag: 0,
};
pub const C_FALSE: Constructor = Constructor {
    name: S_FALSE,
    type_id: TypeId(7),
    tag: 1,
};

pub const C_REF: Constructor = Constructor {
    name: S_REF,
    type_id: TypeId(5),
    tag: 0,
};
