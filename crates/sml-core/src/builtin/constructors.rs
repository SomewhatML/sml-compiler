//! Beware that type_ids are hardcoded in this file, corresponding to the order
//! of the builtin type constructors defined in `tycons.rs`. Changing the order
//! there, or the order in which the constructors are defined in the environment
//! may have disastrous effects.
use crate::*;
use sml_util::interner::*;

// datatype 'a list = nil | :: of 'a * 'a list
pub const C_NIL: Constructor = Constructor {
    name: S_NIL,
    tycon: S_LIST,
    type_id: TypeId(6),
    tag: 0,
    arity: 0,
    type_arity: 2,
};
pub const C_CONS: Constructor = Constructor {
    name: S_CONS,
    tycon: S_LIST,
    type_id: TypeId(6),
    tag: 1,
    arity: 1,
    type_arity: 2,
};

// datatype bool = true | false
pub const C_TRUE: Constructor = Constructor {
    name: S_TRUE,
    tycon: S_BOOL,
    type_id: TypeId(7),
    tag: 0,
    arity: 0,
    type_arity: 2,
};
pub const C_FALSE: Constructor = Constructor {
    name: S_FALSE,
    tycon: S_BOOL,
    type_id: TypeId(7),
    tag: 1,
    arity: 0,
    type_arity: 2,
};

pub const C_REF: Constructor = Constructor {
    name: S_REF,
    tycon: S_REF,
    type_id: TypeId(5),
    tag: 0,
    arity: 1,
    type_arity: 1,
};

pub const C_MATCH: Constructor = Constructor {
    name: S_MATCH,
    tycon: S_EXN,
    type_id: TypeId(8),
    tag: 0,
    arity: 0,
    type_arity: 0,
};

pub const C_BIND: Constructor = Constructor {
    name: S_BIND,
    tycon: S_EXN,
    type_id: TypeId(8),
    tag: 0,
    arity: 0,
    type_arity: 0,
};

pub const C_BUILTINS: [Constructor; 7] = [C_NIL, C_CONS, C_TRUE, C_FALSE, C_REF, C_MATCH, C_BIND];
