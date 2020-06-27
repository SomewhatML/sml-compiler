use super::*;

#[derive(Default, Debug, Clone)]
pub struct Stack<T> {
    inner: Vec<(Symbol, T)>,
}

impl<T> Stack<T> {
    #[inline]
    pub fn push(&mut self, sym: Symbol, tv: T) {
        self.inner.push((sym, tv));
    }

    #[inline]
    pub fn pop(&mut self) -> Option<(Symbol, T)> {
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

    pub fn iter(&self) -> std::slice::Iter<(Symbol, T)> {
        self.inner.iter()
    }

    pub fn lookup(&self, key: &Symbol) -> Option<&T> {
        for (s, tv) in self.inner.iter().rev() {
            if key == s {
                return Some(tv);
            }
        }
        None
    }
}

impl<T> Extend<(Symbol, T)> for Stack<T> {
    fn extend<I: IntoIterator<Item = (Symbol, T)>>(&mut self, iter: I) {
        for elem in iter {
            self.inner.push(elem);
        }
    }
}
