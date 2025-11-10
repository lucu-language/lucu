#![no_std]

#[cfg(feature = "anstyle")]
pub mod ansi;

use core::cell::RefCell;
use core::cmp::Ordering;
use core::fmt;
use core::iter::Peekable;
use core::ops::Range;

use itertools::{Either, Itertools};

pub trait Mark {
    #[cfg(feature = "anstyle")]
    fn style(&self) -> ansi::MarkStyle {
        ansi::MarkStyle::default()
    }
    #[expect(unused)]
    fn fmt_before(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
    #[expect(unused)]
    fn fmt_after(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
    fn ignore_nested(&self) -> bool {
        false
    }

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
    #[cfg(feature = "anstyle")]
    fn style(&self) -> ansi::MarkStyle {
        (*self).style()
    }
    fn fmt_before(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).fmt_before(f)
    }
    fn fmt_after(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).fmt_after(f)
    }
    fn ignore_nested(&self) -> bool {
        (*self).ignore_nested()
    }
}

impl<L, R> Mark for Either<L, R>
where
    L: Mark,
    R: Mark,
{
    #[cfg(feature = "anstyle")]
    fn style(&self) -> ansi::MarkStyle {
        match self {
            Either::Left(l) => l.style(),
            Either::Right(r) => r.style(),
        }
    }
    fn fmt_before(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(l) => l.fmt_before(f),
            Either::Right(r) => r.fmt_before(f),
        }
    }
    fn fmt_after(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(l) => l.fmt_after(f),
            Either::Right(r) => r.fmt_after(f),
        }
    }
    fn ignore_nested(&self) -> bool {
        match self {
            Either::Left(l) => l.ignore_nested(),
            Either::Right(r) => r.ignore_nested(),
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
        if self.start == self.end && self.end == other.start && other.start < other.end {
            return Ordering::Less;
        }
        if other.start == other.end && other.end == self.start && self.start < self.end {
            return Ordering::Greater;
        }
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

#[derive(Clone, Copy)]
pub struct Snippet<'a> {
    src: &'a str,
    start: usize,
    end: usize,
}

impl<'a> Snippet<'a> {
    pub fn source(&self) -> &'a str {
        self.src
    }
    pub fn range(&self) -> Range<usize> {
        self.start..self.end
    }
    pub fn bytes(mut self, bytes: Range<usize>) -> Self {
        self.start = bytes.start;
        self.end = bytes.end;
        self
    }
    pub fn lines(self, lines: Range<usize>) -> Self {
        let start = self
            .src
            .split_inclusive('\n')
            .take(lines.start)
            .map(str::len)
            .sum();
        let end = start
            + self
                .src
                .split_inclusive('\n')
                .skip(lines.start)
                .take(lines.end - lines.start)
                .map(str::len)
                .sum::<usize>();
        self.bytes(start..end)
    }
    pub fn lines_containing(self, span: impl Into<Range<usize>>) -> Self {
        let range = span.into();
        let start = self.src[..range.start]
            .bytes()
            .rposition(|b| b == b'\n')
            .map(|n| n + 1)
            .unwrap_or(0);
        let end = self.src[range.end..]
            .bytes()
            .position(|b| b == b'\n')
            .map(|n| n + range.end)
            .unwrap_or(self.src.len());
        self.bytes(start..end)
    }
    pub fn outer(self) -> Self {
        self.lines_containing(self.start.saturating_sub(1)..(self.end + 1).min(self.src.len()))
    }
}

pub struct Annotated<'a, I> {
    snippet: Snippet<'a>,
    annotations: RefCell<I>,
}

pub trait Annotate<'a> {
    fn snippet(&self) -> Snippet<'a>;
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
    fn snippet(&self) -> Snippet<'a> {
        self.snippet
    }
    fn annotate(
        self,
        iter: impl IntoIterator<Item = Annotation<impl Mark>>,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        Annotated {
            snippet: self.snippet(),
            annotations: RefCell::new(Itertools::merge(
                self.annotations.into_inner().map(Annotation::left),
                iter.into_iter().map(Annotation::right),
            )),
        }
    }
}

impl<'a> Annotate<'a> for &'a str {
    fn snippet(&self) -> Snippet<'a> {
        Snippet {
            src: self,
            start: 0,
            end: self.len(),
        }
    }
    fn annotate(
        self,
        iter: impl IntoIterator<Item = Annotation<impl Mark>>,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        Annotated {
            snippet: self.snippet(),
            annotations: RefCell::new(iter.into_iter()),
        }
    }
}

impl<'a> Annotate<'a> for Snippet<'a> {
    fn snippet(&self) -> Snippet<'a> {
        *self
    }
    fn annotate(
        self,
        iter: impl IntoIterator<Item = Annotation<impl Mark>>,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        Annotated {
            snippet: self.snippet(),
            annotations: RefCell::new(iter.into_iter()),
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
            #[cfg(feature = "anstyle")] style: &mut anstyle::Style,
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result
        where
            I: Iterator<Item = Annotation<T>>,
            T: Mark,
        {
            let mut current = range.start;

            #[cfg(feature = "anstyle")]
            let unstyled = *style;

            while let Some(annotation) = iter.next_if(|annotation| annotation.end <= range.end) {
                if annotation.start < current {
                    continue;
                }

                #[cfg(feature = "anstyle")]
                let mark_style = annotation.mark.style();

                // print up until annotation
                #[cfg(feature = "anstyle")]
                ansi::apply(unstyled, style, f)?;
                write!(f, "{}", &src[current..annotation.start])?;

                // print annotation
                #[cfg(feature = "anstyle")]
                ansi::apply(mark_style.before.unwrap_or(unstyled), style, f)?;
                annotation.mark.fmt_before(f)?;

                #[cfg(feature = "anstyle")]
                ansi::apply(mark_style.content.unwrap_or(unstyled), style, f)?;
                if annotation.mark.ignore_nested() {
                    let segment = &src[annotation.start..annotation.end];
                    write!(f, "{}", segment)?;
                } else {
                    fmt_mut(
                        src,
                        annotation.start..annotation.end,
                        iter,
                        #[cfg(feature = "anstyle")]
                        style,
                        f,
                    )?;
                }

                #[cfg(feature = "anstyle")]
                ansi::apply(mark_style.after.unwrap_or(unstyled), style, f)?;
                annotation.mark.fmt_after(f)?;

                current = annotation.end;
            }

            // print rest
            #[cfg(feature = "anstyle")]
            ansi::apply(unstyled, style, f)?;
            write!(f, "{}", &src[current..range.end])
        }

        fmt_mut(
            self.snippet.src,
            self.snippet.start..self.snippet.end,
            &mut (&mut *self.annotations.borrow_mut()).peekable(),
            #[cfg(feature = "anstyle")]
            &mut anstyle::Style::new(),
            f,
        )
    }
}
