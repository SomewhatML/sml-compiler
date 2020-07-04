use std::cell::RefCell;
use std::mem;

const PAGE_SIZE: usize = 8192 * 8;

pub struct Arena<T> {
    chunks: RefCell<Chunks<T>>,
}

pub struct Chunks<T> {
    current: Vec<T>,
    rest: Vec<Vec<T>>,
}

impl<T> Arena<T> {
    pub fn new() -> Arena<T> {
        let sz = PAGE_SIZE / mem::size_of::<T>().max(1);
        let n = sz.max(1);
        Arena {
            chunks: RefCell::new(Chunks {
                current: Vec::with_capacity(n),
                rest: Vec::new(),
            }),
        }
    }

    pub fn capacity(&self) -> usize {
        let chunks = self.chunks.borrow();
        chunks.current.capacity()
    }

    #[inline]
    fn alloc_fast(&self, value: T) -> Result<&mut T, T> {
        let mut chunks = self.chunks.borrow_mut();
        let len = chunks.current.len();
        if len < chunks.current.capacity() {
            chunks.current.push(value);
            Ok(unsafe { &mut *chunks.current.as_mut_ptr().add(len) })
        } else {
            Err(value)
        }
    }

    fn alloc_slow(&self, value: T) -> &mut T {
        let mut chunks = self.chunks.borrow_mut();
        chunks.reserve();
        debug_assert!(chunks.current.len() < chunks.current.capacity());
        chunks.current.push(value);
        unsafe { &mut *chunks.current.as_mut_ptr().add(1) }
    }

    pub fn alloc(&self, value: T) -> &mut T {
        self.alloc_fast(value)
            .unwrap_or_else(|v| self.alloc_slow(v))
    }
}

impl<T> Chunks<T> {
    fn reserve(&mut self) {
        let cap = self.current.capacity();
        let chunk = mem::replace(&mut self.current, Vec::with_capacity(cap));
        self.rest.push(chunk);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    enum Expr<'a> {
        Var(usize),
        Abs(&'a Expr<'a>),
        App(&'a Expr<'a>, &'a Expr<'a>),
    }

    enum Type<'a> {
        Con(usize, Vec<&'a Type<'a>>),
        Var(std::cell::Cell<Option<&'a Type<'a>>>),
    }

    #[test]
    fn alloc_expr() {
        let a = Arena::new();
        assert_eq!(mem::size_of::<Expr>(), 24);
        assert_eq!(a.capacity(), PAGE_SIZE / 24);
        let e1 = a.alloc(Expr::Var(0));
        let e2 = a.alloc(Expr::Abs(e1));
        let e3 = a.alloc(Expr::App(e2, e2));
    }
}
