use super::arenas::TypeArena;
use super::*;
use std::cell::Cell;
use std::collections::{HashSet, VecDeque};
use std::rc::Rc;

pub struct TypeVar<'ar> {
    pub id: usize,
    pub data: Cell<Option<&'ar Type<'ar>>>,
}

pub enum Type<'ar> {
    Var(&'ar TypeVar<'ar>),
    Con(Tycon, Vec<&'ar Type<'ar>>),
    Record(Vec<Row<&'ar Type<'ar>>>),
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq)]
pub struct Tycon {
    pub name: Symbol,
    pub arity: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub struct Constructor {
    pub name: Symbol,
    pub type_id: TypeId,
    pub tag: u32,
}

#[derive(Clone)]
pub enum Scheme<'ar> {
    Mono(&'ar Type<'ar>),
    Poly(Vec<usize>, &'ar Type<'ar>),
}

impl<'ar> Type<'ar> {
    pub fn as_tyvar(&self) -> &TypeVar<'ar> {
        match self {
            Type::Var(tv) => tv,
            _ => panic!("internal compiler error: Type::as_tyvar"),
        }
    }

    /// 'de-arrow' an arrow type, returning the argument and result type
    pub fn de_arrow(&self) -> Option<(&'_ Type<'ar>, &'_ Type<'ar>)> {
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

    /// Pre-order BFS
    pub fn visit<F: FnMut(&Type<'ar>)>(&self, mut f: F) {
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
                    for row in rows {
                        queue.push_back(&row.data);
                    }
                }
            }
        }
    }

    /// Perform a breadth-first traversal of a type, collecting it's
    /// associated type variables that have a rank greater than `rank`
    pub fn ftv(&self) -> Vec<usize> {
        let mut set = Vec::new();
        let mut uniq = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(self);

        while let Some(ty) = queue.pop_front() {
            match ty {
                Type::Var(x) => match x.ty() {
                    None => {
                        if uniq.insert(x.id) {
                            set.push(x.id);
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
                    for row in rows {
                        queue.push_back(&row.data);
                    }
                }
            }
        }
        set
    }

    /// Apply a substitution to a type
    pub fn apply(
        &'ar self,
        arena: &'ar TypeArena<'ar>,
        map: &HashMap<usize, &'ar Type<'ar>>,
    ) -> &'ar Type<'ar> {
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
                vars.into_iter().map(|ty| ty.apply(arena, map)).collect(),
            )),
            Type::Record(rows) => arena.alloc(Type::Record(
                rows.into_iter()
                    .map(|r| r.fmap(|ty| ty.apply(arena, map)))
                    .collect(),
            )),
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
                    // let curr = x.rank();
                    // let min_rank = curr.min(tyvar.rank());
                    // if min_rank < curr {
                    //     // println!("promoting type var {:?} {}->{}", x, x.rank(), min_rank);
                    //     x.data.set_rank(min_rank);
                    // }
                    x.id == tyvar.id
                }
            }
            Type::Con(_, tys) => tys.iter().any(|ty| ty.occurs_check(tyvar)),
            Type::Record(rows) => rows.iter().any(|r| r.data.occurs_check(tyvar)),
        }
    }
}

fn fresh_name(x: usize) -> String {
    let last = ((x % 26) as u8 + 'a' as u8) as char;
    (0..x / 26)
        .map(|_| 'z')
        .chain(std::iter::once(last))
        .collect::<String>()
}

impl<'ar> fmt::Debug for Type<'ar> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Type::*;
        match self {
            Var(tv) => match tv.ty() {
                Some(ty) => write!(f, "{:?}", ty),
                None => write!(f, "'{}", fresh_name(tv.id)),
            },
            Con(tc, args) => match tc {
                &crate::builtin::tycons::T_ARROW => write!(f, "{:?} -> {:?}", args[0], args[1]),
                _ => write!(
                    f,
                    "{} {:?}",
                    args.into_iter()
                        .map(|x| format!("{:?}", x))
                        .collect::<String>(),
                    tc.name
                ),
            },
            Record(rows) => write!(
                f,
                "{{{}}}",
                rows.into_iter()
                    .map(|r| format!("{:?}:{:?}", r.label, r.data))
                    .collect::<Vec<String>>()
                    .join(",")
            ),
        }
    }
}

impl Tycon {
    pub const fn new(name: Symbol, arity: usize) -> Tycon {
        Tycon { name, arity }
    }
}

impl<'ar> Scheme<'ar> {
    pub fn arity(&self) -> usize {
        match self {
            Scheme::Mono(_) => 0,
            Scheme::Poly(tyvars, _) => tyvars.len(),
        }
    }

    pub fn apply(&self, arena: &'ar TypeArena<'ar>, args: Vec<&'ar Type<'ar>>) -> &'ar Type<'ar> {
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
                        .collect::<HashMap<usize, &'ar Type<'ar>>>();
                    ty.apply(arena, &map)
                } else {
                    panic!("internal compiler error, not checking scheme arity")
                }
            }
        }
    }

    pub fn new(ty: &'ar Type<'ar>, tyvars: Vec<usize>) -> Scheme<'ar> {
        match tyvars.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(tyvars, ty),
        }
    }
}

impl<'ar> TypeVar<'ar> {
    pub fn new(id: usize) -> TypeVar<'ar> {
        let data = Cell::new(None);
        TypeVar { id, data }
    }

    pub fn ty(&self) -> Option<&'ar Type<'ar>> {
        self.data.get()
    }
}

impl<'ar> fmt::Debug for Scheme<'ar> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Scheme::Poly(tys, ty) => write!(
                f,
                "∀{}. ({:?})",
                tys.into_iter()
                    .map(|x| fresh_name(*x))
                    .collect::<Vec<String>>()
                    .join(","),
                ty
            ),
            Scheme::Mono(ty) => write!(f, "{:?}", ty),
        }
    }
}
