use std::fmt::{self, Debug, Display};
use std::ops::{Deref, Index, Range};

#[derive(PartialEq, Eq, Clone, Copy, Default, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl Index<Span> for str {
    type Output = str;
    fn index(&self, index: Span) -> &Self::Output {
        &self[Range::from(index)]
    }
}

impl Span {
    pub const ZERO: Span = Span::new(0, 0);
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }
    pub const fn inner(self) -> Self {
        Self {
            start: self.start + 1,
            end: self.end - 1,
        }
    }
}

impl From<Span> for Range<usize> {
    fn from(value: Span) -> Self {
        value.start as usize..value.end as usize
    }
}

pub trait HasSpan {
    fn span(&self) -> Span;
}

impl<T> HasSpan for Box<T>
where
    T: HasSpan,
{
    fn span(&self) -> Span {
        self.deref().span()
    }
}

impl HasSpan for Span {
    fn span(&self) -> Span {
        *self
    }
}
