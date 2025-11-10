#![no_std]

#[cfg(feature = "anstyle")]
pub mod anstyle;

use core::cell::RefCell;
use core::cmp::Ordering;
use core::fmt;
use core::iter::Peekable;
use core::ops::Range;

use itertools::{Either, Itertools};

pub trait Mark {
    fn fmt_before(&self, segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result;
    fn fmt_after(&self, segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    fn at(self, span: impl Into<Range<usize>>) -> Annotation<Self>
    where
        Self: Sized,
    {
        let range = span.into();
        Annotation {
            start: range.start,
            end: range.end,
            mark: self,
        }
    }
}

impl<T> Mark for &'_ T
where
    T: Mark,
{
    fn fmt_before(&self, segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).fmt_before(segment, f)
    }
    fn fmt_after(&self, segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).fmt_after(segment, f)
    }
}

impl<L, R> Mark for Either<L, R>
where
    L: Mark,
    R: Mark,
{
    fn fmt_before(&self, segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(l) => l.fmt_before(segment, f),
            Either::Right(r) => r.fmt_before(segment, f),
        }
    }
    fn fmt_after(&self, segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(l) => l.fmt_after(segment, f),
            Either::Right(r) => r.fmt_after(segment, f),
        }
    }
}

#[derive(Clone, Copy)]
pub struct Annotation<T> {
    start: usize,
    end: usize,
    mark: T,
}

impl<T> PartialOrd for Annotation<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Annotation<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.start.cmp(&other.start).then(other.end.cmp(&self.end))
    }
}

impl<T> PartialEq for Annotation<T> {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end
    }
}

impl<T> Eq for Annotation<T> {}

impl<T> Annotation<T> {
    fn left<U>(self) -> Annotation<Either<T, U>> {
        Annotation {
            start: self.start,
            end: self.end,
            mark: Either::Left(self.mark),
        }
    }
    fn right<U>(self) -> Annotation<Either<U, T>> {
        Annotation {
            start: self.start,
            end: self.end,
            mark: Either::Right(self.mark),
        }
    }
}

pub struct Annotated<'a, I> {
    src: &'a str,
    annotations: RefCell<I>,
    range: Range<usize>,
}

pub trait Annotate<'a> {
    fn annotate(
        self,
        iter: impl IntoIterator<Item = Annotation<impl Mark>>,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>>;
}

impl<'a, I, T> Annotate<'a> for Annotated<'a, I>
where
    I: Iterator<Item = Annotation<T>>,
    T: Mark,
{
    fn annotate(
        self,
        iter: impl IntoIterator<Item = Annotation<impl Mark>>,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        Annotated {
            src: self.src,
            annotations: RefCell::new(Itertools::merge(
                self.annotations.into_inner().map(Annotation::left),
                iter.into_iter().map(Annotation::right),
            )),
            range: self.range,
        }
    }
}

impl<'a> Annotate<'a> for &'a str {
    fn annotate(
        self,
        iter: impl IntoIterator<Item = Annotation<impl Mark>>,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        Annotated {
            src: self,
            annotations: RefCell::new(iter.into_iter()),
            range: 0..self.len(),
        }
    }
}

impl<I, T> fmt::Display for Annotated<'_, I>
where
    I: Iterator<Item = Annotation<T>>,
    T: Mark,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_mut<I, T>(
            src: &str,
            range: Range<usize>,
            iter: &mut Peekable<I>,
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result
        where
            I: Iterator<Item = Annotation<T>>,
            T: Mark,
        {
            let mut current = range.start;

            while let Some(annotation) = iter.next_if(|annotation| annotation.end <= range.end) {
                let segment = &src[annotation.start..annotation.end];

                // print up until annotation
                write!(f, "{}", &src[current..annotation.start])?;

                // print annotation
                annotation.mark.fmt_before(segment, f)?;
                fmt_mut(src, annotation.start..annotation.end, iter, f)?;
                annotation.mark.fmt_after(segment, f)?;

                current = annotation.end;
            }

            // print rest
            write!(f, "{}", &src[current..range.end])
        }

        fmt_mut(
            self.src,
            self.range.clone(),
            &mut (&mut *self.annotations.borrow_mut()).peekable(),
            f,
        )
    }
}
