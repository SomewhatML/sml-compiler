use super::arenas::TypeArena;
use super::*;
use rustc_hash::FxHashSet;
use std::cell::Cell;
use std::collections::VecDeque;

/// A type variable
///
/// Each type variable has a unique identifier by which it is referred to.
/// Type vars also have a rank, indicating the lexical scope at which they
/// are introduced, which allows for optimal generalization (polymorphization)
/// of introduced type variables.
///
/// Each type variable also contains an interior-mutable `Cell`. If the cell
/// contains a `Some(Type)`, then that indicates that this type variable
/// has been unified to some other type (or type var, etc). We allocate type
/// variables in an arena, so that [`Type`]s may store a reference to a type
/// variable. When combined with the interior mutability aspect, we get
/// maximal sharing of type unification information.
///
/// Invariants: it is important that `data` is set at *most* one time.
pub struct TypeVar<'a> {
    pub id: usize,
    rank: Cell<usize>,
    pub data: Cell<Option<&'a Type<'a>>>,
}

/// A flexible record type.
///
/// Flexible records cannot be generalized, so they behave like something
/// with the value restriction. We allow the maximum possible scope to resolve
/// flex records. Similar to [`TypeVar`], it is critical that `unified` is set
/// at *most* once. We impose an additional restriction that the unified type
/// must always be a Record type
pub struct Flex<'a> {
    pub constraints: SortedRecord<&'a Type<'a>>,
    pub unified: Cell<Option<&'a Type<'a>>>,
}

pub enum Type<'a> {
    /// Type variable
    Var(&'a TypeVar<'a>),
    /// An n-ary type constructor, like `int`, `bool`, `list`, etc
    Con(Tycon, Vec<&'a Type<'a>>),
    /// A record, or tuple type
    Record(SortedRecord<&'a Type<'a>>),
    /// A flexible record type
    Flex(Flex<'a>),
}

/// A type constructor
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub struct Tycon {
    pub name: Symbol,
    pub arity: usize,
    pub scope_depth: usize,
}

/// A data constructor
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub struct Constructor {
    pub name: Symbol,
    pub type_id: TypeId,
    pub tycon: Symbol,
    pub tag: u8,
    pub arity: u8,
    pub type_arity: u8,
}

/// A Hindley-Milner type scheme
#[derive(Clone)]
pub enum Scheme<'a> {
    Mono(&'a Type<'a>),
    Poly(Vec<usize>, &'a Type<'a>),
}

impl<'a> Type<'a> {
    pub fn as_tyvar(&self) -> &TypeVar<'a> {
        match self {
            Type::Var(tv) => tv,
            _ => panic!("internal compiler error: Type::as_tyvar"),
        }
    }

    /// 'de-arrow' an arrow type, returning the argument and result type
    pub fn de_arrow(&self) -> Option<(&'_ Type<'a>, &'_ Type<'a>)> {
        match self {
            Type::Con(builtin::tycons::T_ARROW, v) => Some((v[0], v[1])),
            Type::Var(tv) => {
                if let Some(ty) = tv.ty() {
                    ty.de_arrow()
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Return true if the type-graph contains any unresolved flex variables
    pub fn unresolved_flex(&self) -> bool {
        let mut unres = false;
        self.visit(|ty| {
            if let Type::Flex(flex) = ty {
                if flex.ty().is_none() {
                    unres = true;
                }
            }
        });
        unres
    }

    pub fn resolved(&self) -> bool {
        match &self {
            Type::Var(tv) => tv.ty().map(|ty| ty.resolved()).unwrap_or(false),
            Type::Flex(tv) => tv.ty().map(|ty| ty.resolved()).unwrap_or(false),
            Type::Con(_, vars) => vars.iter().all(|ty| ty.resolved()),
            Type::Record(fields) => fields.iter().all(|f| f.data.resolved()),
        }
    }

    /// Pre-order BFS
    pub fn visit<F: FnMut(&Type<'a>)>(&self, mut f: F) {
        let mut queue = VecDeque::new();
        queue.push_back(self);

        while let Some(ty) = queue.pop_front() {
            f(ty);
            match ty {
                Type::Var(x) => {
                    if let Some(link) = x.ty() {
                        queue.push_back(link);
                    }
                }
                Type::Con(_, tys) => {
                    for ty in tys {
                        queue.push_back(ty);
                    }
                }
                Type::Record(rows) => {
                    for row in rows.iter() {
                        queue.push_back(&row.data);
                    }
                }
                Type::Flex(flex) => {
                    if let Some(link) = flex.ty() {
                        queue.push_back(link);
                    } else {
                        for row in flex.constraints.iter() {
                            queue.push_back(&row.data);
                        }
                    }
                }
            }
        }
    }

    /// Perform a breadth-first traversal of a type, collecting it's
    /// associated type variables that have a rank greater than `rank`
    pub fn ftv_rank(&self, rank: usize) -> Vec<usize> {
        let mut vars = Vec::new();
        let mut uniq = FxHashSet::default();
        let mut queue = VecDeque::new();
        queue.push_back(self);

        while let Some(ty) = queue.pop_front() {
            match ty {
                Type::Var(x) => match x.ty() {
                    None => {
                        if x.rank() > rank && uniq.insert(x.id) {
                            vars.push(x.id);
                        }
                    }
                    Some(link) => {
                        queue.push_back(link);
                    }
                },
                Type::Con(_, tys) => {
                    for ty in tys {
                        queue.push_back(ty);
                    }
                }
                Type::Record(rows) => {
                    for row in rows.iter() {
                        queue.push_back(&row.data);
                    }
                }
                Type::Flex(flex) => {
                    if let Some(link) = flex.ty() {
                        queue.push_back(link)
                    } else {
                        // Do nothing, we don't want to cause flexible record
                        // types to become generalized
                    }
                }
            }
        }
        vars
    }

    pub fn ftv_rank_init(rank: usize, start: Vec<&'a Type<'a>>) -> Vec<usize> {
        let mut vars = Vec::new();
        let mut uniq = FxHashSet::default();
        let mut queue = VecDeque::from(start);
        while let Some(ty) = queue.pop_front() {
            match ty {
                Type::Var(x) => match x.ty() {
                    None => {
                        if x.rank() > rank && uniq.insert(x.id) {
                            vars.push(x.id);
                        }
                    }
                    Some(link) => {
                        queue.push_back(link);
                    }
                },
                Type::Con(_, tys) => {
                    for ty in tys {
                        queue.push_back(ty);
                    }
                }
                Type::Record(rows) => {
                    for row in rows.iter() {
                        queue.push_back(&row.data);
                    }
                }
                Type::Flex(flex) => {
                    if let Some(link) = flex.ty() {
                        queue.push_back(link)
                    } else {
                        // Do nothing, we don't want to cause flexible record
                        // types to become generalized
                    }
                }
            }
        }
        vars
    }

    /// Apply a substitution to a type
    pub fn apply(
        &'a self,
        arena: &'a TypeArena<'a>,
        map: &HashMap<usize, &'a Type<'a>>,
    ) -> &'a Type<'a> {
        match self {
            Type::Var(x) => match x.ty() {
                Some(ty) => ty.apply(arena, map),
                None => {
                    match map.get(&x.id) {
                        Some(ty) => ty,
                        None => self,
                    }
                    // map.get(&x.id).copied().unwrap_or(self),
                }
            },
            Type::Con(tc, vars) => arena.alloc(Type::Con(
                *tc,
                vars.iter().map(|ty| ty.apply(arena, map)).collect(),
            )),
            Type::Record(rows) => arena.alloc(Type::Record(rows.fmap(|ty| ty.apply(arena, map)))),
            Type::Flex(flex) => {
                match flex.ty() {
                    Some(ty) => ty.apply(arena, map),
                    None => {
                        // TODO: Do we need to do anything here?
                        self
                    }
                }
            }
        }
    }

    /// Check for potential cyclic occurences of `tyvar` in `self`.
    /// N.B. This function has potential side effects, in that it may promote
    /// the associated rank of `tyvar` to the rank of `self`, if `self` is also
    /// a type variable
    pub fn occurs_check(&self, tyvar: &TypeVar) -> bool {
        match &self {
            Type::Var(x) => {
                if let Some(info) = x.ty() {
                    info.occurs_check(tyvar)
                } else {
                    let curr = x.rank();
                    let min_rank = curr.min(tyvar.rank());
                    if min_rank < curr {
                        // println!("promoting type var {} {}->{}", fresh_name(x.id), x.rank(),
                        // min_rank);
                        x.rank.set(min_rank);
                    }
                    x.id == tyvar.id
                }
            }
            Type::Con(_, tys) => tys.iter().any(|ty| ty.occurs_check(tyvar)),
            Type::Record(rows) => rows.iter().any(|r| r.data.occurs_check(tyvar)),
            Type::Flex(flex) => match flex.ty() {
                Some(ty) => ty.occurs_check(tyvar),
                None => flex.constraints.iter().any(|r| r.data.occurs_check(tyvar)),
            },
        }
    }
}

pub fn fresh_name(x: usize) -> String {
    let last = ((x % 26) as u8 + b'a' as u8) as char;
    (0..x / 26)
        .map(|_| 'z')
        .chain(std::iter::once(last))
        .collect::<String>()
}

impl Tycon {
    pub const fn new(name: Symbol, arity: usize, scope_depth: usize) -> Tycon {
        Tycon {
            name,
            arity,
            scope_depth,
        }
    }
}

impl<'a> Scheme<'a> {
    pub fn arity(&self) -> usize {
        match self {
            Scheme::Mono(_) => 0,
            Scheme::Poly(tyvars, _) => tyvars.len(),
        }
    }

    pub fn apply(&self, arena: &'a TypeArena<'a>, args: Vec<&'a Type<'a>>) -> &'a Type<'a> {
        match self {
            Scheme::Mono(ty) => ty,
            Scheme::Poly(vars, ty) => {
                if vars.len() > args.len() {
                    unimplemented!()
                } else if vars.len() == args.len() {
                    let map = vars
                        .iter()
                        .copied()
                        .zip(args.into_iter())
                        .collect::<HashMap<usize, &'a Type<'a>>>();
                    ty.apply(arena, &map)
                } else {
                    panic!("internal compiler error, not checking scheme arity")
                }
            }
        }
    }

    pub fn new(ty: &'a Type<'a>, tyvars: Vec<usize>) -> Scheme<'a> {
        match tyvars.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(tyvars, ty),
        }
    }
}

impl<'a> TypeVar<'a> {
    pub fn new(id: usize, rank: usize) -> TypeVar<'a> {
        let data = Cell::new(None);
        TypeVar {
            id,
            rank: Cell::new(rank),
            data,
        }
    }

    pub fn ty(&self) -> Option<&'a Type<'a>> {
        self.data.get()
    }

    fn rank(&self) -> usize {
        self.rank.get()
    }
}

impl<'a> Flex<'a> {
    pub fn new(constraints: SortedRecord<&'a Type<'a>>) -> Flex<'a> {
        Flex {
            constraints,
            unified: Cell::new(None),
        }
    }

    pub fn ty(&self) -> Option<&'a Type<'a>> {
        self.unified.get()
    }
}
