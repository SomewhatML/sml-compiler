//! Source code locations and spans
use std::fmt;

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Default)]
/// Struct representing a single location in a source string
pub struct Location {
    pub line: u16,
    pub col: u16,
    // pub abs: u32,
}

impl Location {
    pub const fn new(line: u16, col: u16, abs: u32) -> Location {
        Location { line, col }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Default)]
/// A span in the source, with a start and end location
pub struct Span {
    pub start: Location,
    pub end: Location,
}

/// Data with associated code span
pub struct Spanned<T> {
    pub span: Span,
    pub data: T,
}

impl<T> Spanned<T> {
    pub fn new(data: T, span: Span) -> Self {
        Spanned { data, span }
    }

    pub fn data(self) -> T {
        self.data
    }

    pub fn fmap<S, F: FnMut(T) -> S>(self, mut f: F) -> Spanned<S> {
        Spanned {
            span: self.span,
            data: f(self.data),
        }
    }

    pub fn smap<S, F: FnMut(T, Span) -> S>(self, mut f: F) -> Spanned<S> {
        Spanned {
            span: self.span,
            data: f(self.data, self.span),
        }
    }

    pub const fn zero(data: T) -> Self {
        Spanned {
            span: Span::zero(),
            data,
        }
    }
}

impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T: PartialOrd> PartialOrd for Spanned<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.data.partial_cmp(&other.data)
    }
}

impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T, E> Spanned<Result<T, E>> {
    pub fn flatten(self) -> Result<Spanned<T>, E> {
        match self.data {
            Ok(t) => Ok(Spanned::new(t, self.span)),
            Err(e) => Err(e),
        }
    }
}

impl<T> Spanned<Option<T>> {
    pub fn flatten(self) -> Option<Spanned<T>> {
        match self.data {
            Some(t) => Some(Spanned::new(t, self.span)),
            None => None,
        }
    }
}

impl<T: Copy> Copy for Spanned<T> {}
impl<T: Clone> Clone for Spanned<T> {
    fn clone(&self) -> Self {
        Spanned::new(self.data.clone(), self.span)
    }
}

impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.data.fmt(f)
    }
}

impl<T: fmt::Display> fmt::Display for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.data.fmt(f)
    }
}

impl Span {
    pub fn new(start: Location, end: Location) -> Span {
        Span { start, end }
    }

    pub const fn zero() -> Span {
        let max = Location {
            line: 0,
            col: 0,
            // abs: 0,
        };
        Span {
            start: max,
            end: max,
        }
    }

    pub const fn dummy() -> Span {
        let max = Location::new(std::u16::MAX, std::u16::MAX, 0);
        Span {
            start: max,
            end: max,
        }
    }
}

impl std::ops::Add<Span> for Span {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Span {
            start: self.start,
            end: rhs.end,
        }
    }
}

impl std::ops::Add<Location> for Span {
    type Output = Self;
    fn add(self, rhs: Location) -> Self::Output {
        Span {
            start: self.start,
            end: rhs,
        }
    }
}

impl std::ops::AddAssign<Span> for Span {
    fn add_assign(&mut self, rhs: Self) {
        self.end = rhs.end;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn spanned_size() {
        assert_eq!(std::mem::size_of::<Span>(), 8);
    }
}
