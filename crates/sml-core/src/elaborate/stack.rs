use super::*;

#[derive(Default, Debug, Clone)]
pub struct TyVarStack {
    inner: Vec<(Symbol, TypeVar)>,
}

impl TyVarStack {
    #[inline]
    pub fn push(&mut self, sym: Symbol, tv: TypeVar) {
        self.inner.push((sym, tv));
    }

    #[inline]
    pub fn pop(&mut self) -> Option<(Symbol, TypeVar)> {
        self.inner.pop()
    }

    #[inline]
    pub fn popn(&mut self, n: usize) {
        for _ in 0..n {
            let _ = self.pop();
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn iter(&self) -> std::slice::Iter<(Symbol, TypeVar)> {
        self.inner.iter()
    }

    pub fn lookup(&self, key: &Symbol) -> Option<TypeVar> {
        for (s, tv) in self.inner.iter().rev() {
            if key == s {
                return Some(*tv);
            }
        }
        None
    }
}

impl Extend<(Symbol, TypeVar)> for TyVarStack {
    fn extend<I: IntoIterator<Item = (Symbol, TypeVar)>>(&mut self, iter: I) {
        for elem in iter {
            self.inner.push(elem);
        }
    }
}
