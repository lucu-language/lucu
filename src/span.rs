use std::{
    fmt::{self, Debug, Display},
    ops::{Deref, Index, Range},
};

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
    pub const START: Span = Span::new(0, 0);
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

impl<T> HasSpan for Spanned<T> {
    fn span(&self) -> Span {
        self.1
    }
}

impl HasSpan for Span {
    fn span(&self) -> Span {
        *self
    }
}

#[derive(Clone, Copy, Eq)]
pub struct Spanned<T>(pub T, pub Span);

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// equality if the inner value is equal
impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T> Debug for Spanned<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> Display for Spanned<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
