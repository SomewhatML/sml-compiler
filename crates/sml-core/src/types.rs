use super::*;
use std::cell::{Cell, UnsafeCell};
use std::collections::{HashSet, VecDeque};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};

#[derive(Clone, Debug, Default, PartialEq)]
pub struct TypeVar {
    pub id: usize,
    pub data: Rc<TyVarInner<Type>>,
}

#[derive(Clone, PartialEq)]
pub enum Type {
    Var(TypeVar),
    Con(Tycon, Vec<Type>),
    Record(Vec<Row<Type>>),
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

#[derive(Clone, Debug)]
pub enum Scheme {
    Mono(Type),
    Poly(Vec<usize>, Type),
}

impl Type {
    /// Create a new 'arrow' type
    pub fn arrow(a: Type, b: Type) -> Type {
        Type::Con(builtin::tycons::T_ARROW, vec![a, b])
    }

    /// 'de-arrow' an arrow type, returning the argument and result type
    pub fn de_arrow(&self) -> Option<(&Type, &Type)> {
        match self {
            Type::Con(builtin::tycons::T_ARROW, v) => Some((&v[0], &v[1])),
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

    /// Create a boolean type
    pub fn bool() -> Type {
        Type::Con(builtin::tycons::T_BOOL, vec![])
    }

    /// Create an exception type
    pub fn exn() -> Type {
        Type::Con(builtin::tycons::T_EXN, vec![])
    }
    /// Create a unit type
    pub fn unit() -> Type {
        Type::Con(builtin::tycons::T_UNIT, vec![])
    }

    /// Perform a breadth-first traversal of a type, collecting it's
    /// associated type variables that have a rank greater than `rank`
    pub fn ftv(&self, rank: usize) -> Vec<usize> {
        let mut set = Vec::new();
        let mut uniq = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(self);

        while let Some(ty) = queue.pop_front() {
            match ty {
                Type::Var(x) => match x.ty() {
                    None => {
                        if x.rank() > rank && uniq.insert(x.id) {
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

    /// Perform a breadth-first traversal of a type, collecting it's
    /// associated type variables that have a rank greater than `rank`
    pub fn ftv_no_rank(&self) -> Vec<usize> {
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
    pub fn apply(self, map: &HashMap<usize, Type>) -> Type {
        match self {
            Type::Var(x) => match x.ty() {
                Some(ty) => ty.clone().apply(map),
                None => map.get(&x.id).cloned().unwrap_or(Type::Var(x)),
            },
            Type::Con(tc, vars) => {
                Type::Con(tc, vars.into_iter().map(|ty| ty.apply(map)).collect())
            }
            Type::Record(rows) => Type::Record(
                rows.into_iter()
                    .map(|r| r.fmap(|ty| ty.apply(map)))
                    .collect(),
            ),
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
                    info.occurs_check(x)
                } else {
                    let curr = x.rank();
                    let min_rank = curr.min(tyvar.rank());
                    if min_rank < curr {
                        // println!("promoting type var {:?} {}->{}", x, x.rank(), min_rank);
                        x.data.set_rank(min_rank);
                    }

                    x.id == tyvar.id
                }
            }
            Type::Con(tc, tys) => tys.iter().any(|ty| ty.occurs_check(tyvar)),
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

impl fmt::Debug for Type {
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

impl Scheme {
    pub fn arity(&self) -> usize {
        match self {
            Scheme::Mono(_) => 0,
            Scheme::Poly(tyvars, _) => tyvars.len(),
        }
    }

    pub fn apply(&self, args: Vec<Type>) -> Type {
        match self {
            Scheme::Mono(ty) => ty.clone(),
            Scheme::Poly(vars, ty) => {
                if vars.len() > args.len() {
                    unimplemented!()
                } else if vars.len() == args.len() {
                    let map = vars
                        .iter()
                        .copied()
                        .zip(args.into_iter())
                        .collect::<HashMap<usize, Type>>();
                    ty.clone().apply(&map)
                } else {
                    panic!("internal compiler error, not checking scheme arity")
                }
            }
        }
    }

    pub fn new(ty: Type, tyvars: Vec<usize>) -> Scheme {
        match tyvars.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(tyvars, ty),
        }
    }
}

impl TypeVar {
    pub fn new(id: usize, rank: usize) -> TypeVar {
        let data = Rc::new(TyVarInner::with_rank(rank));
        TypeVar { id, data }
    }

    pub fn ty(&self) -> Option<&Type> {
        self.data.get()
    }

    pub fn rank(&self) -> usize {
        self.data.rank.get()
    }
}

// #[derive(PartialOrd, Eq, Hash)]
pub struct TyVarInner<T> {
    inner: UnsafeCell<Option<T>>,
    rank: Cell<usize>,
    init: AtomicBool,
}

impl<T> Default for TyVarInner<T> {
    fn default() -> Self {
        TyVarInner {
            inner: UnsafeCell::new(None),
            rank: Cell::new(0),
            init: false.into(),
        }
    }
}

impl<T: PartialEq> PartialEq for TyVarInner<T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for TyVarInner<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}#{}", self.get(), self.get_rank())
    }
}

impl<T> TyVarInner<T> {
    pub fn with_rank(rank: usize) -> Self {
        TyVarInner {
            inner: UnsafeCell::new(None),
            rank: Cell::new(rank),
            init: false.into(),
        }
    }

    pub fn set(&self, data: T) -> Result<(), T> {
        if !self.init.compare_and_swap(false, true, Ordering::Acquire) {
            unsafe {
                let ptr = &mut *self.inner.get();
                *ptr = Some(data);
            }
            Ok(())
        } else {
            Err(data)
        }
    }

    pub fn get(&self) -> Option<&T> {
        if !self.init.compare_and_swap(false, false, Ordering::Release) {
            None
        } else {
            unsafe { &*self.inner.get() }.as_ref()
        }
    }

    pub fn set_rank(&self, rank: usize) {
        self.rank.set(rank)
    }

    pub fn get_rank(&self) -> usize {
        self.rank.get()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn smoke() {
        let cell = TyVarInner::default();
        assert_eq!(cell.get(), None);
        assert_eq!(cell.set(10), Ok(()));
        assert_eq!(cell.set(12), Err(12));
        assert_eq!(cell.get(), Some(&10));
    }

    #[test]
    fn smoke_shared() {
        let cell = Rc::new(TyVarInner::default());
        let rc1 = cell.clone();
        let rc2 = cell.clone();

        assert_eq!(rc2.get(), None);
        rc1.set(12).unwrap();
        assert_eq!(rc2.get(), Some(&12));
        assert_eq!(rc2.set(10), Err(10));
    }
}
