use std::borrow::Cow;
use std::cell::OnceCell;
use std::ops::Deref;

use annotate_snippets::{
    Annotation, AnnotationKind, Element, Level, Origin, Renderer, Report, Snippet, Title
};
use anstyle::{AnsiColor, Color, Style};
use compact_str::CompactString;
use do_notation::Lift;
use lucu_annotate::ansi::MarkStyle;
use lucu_annotate::{Annotate, Mark};

use crate::annotate::{AnnotateExt, LINE_STYLE};
use crate::module::{Module, ModuleResolver};
use crate::span::{HasSpan, Span};
use crate::stage::ast::visit::Combine;
use crate::stage::token::lexer::Lexer;

pub trait HasProblems {
    fn problems(&self) -> impl Iterator<Item = &Problem>;
    fn print_problems(&self, resolver: &impl ModuleResolver, renderer: &Renderer) {
        for problem in self.problems() {
            problem.print(resolver, renderer);
        }
    }
    fn print_problems2(&self, resolver: &impl ModuleResolver) {
        for problem in self.problems() {
            problem.print2(resolver);
        }
    }
}

#[must_use = "this `Result` may have problems, which should be handled"]
#[derive(Clone, Debug)]
pub struct Result<T> {
    value: Option<T>,
    problems: im::Vector<Problem>,
}

#[must_use = "`Problems` may not be empty, which should be handled"]
#[derive(Clone, Debug, Default)]
pub struct Problems {
    problems: im::Vector<Problem>,
}

impl From<Problem> for Problems {
    fn from(value: Problem) -> Self {
        Self::new(value)
    }
}

impl From<Problems> for Result<()> {
    fn from(value: Problems) -> Self {
        Self {
            value: Some(()),
            problems: value.problems,
        }
    }
}

impl<T> Default for Result<T>
where
    T: Default,
{
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl Problems {
    pub fn ok() -> Self {
        Self {
            problems: im::Vector::new(),
        }
    }
    pub fn new(problem: Problem) -> Self {
        Self {
            problems: im::Vector::unit(problem),
        }
    }
    pub fn with<T>(self, value: T) -> Result<T> {
        Result {
            value: Some(value),
            problems: self.problems,
        }
    }
    pub fn error<T>(self) -> Result<T> {
        assert!(
            self.problems
                .iter()
                .any(|d| d.header().level == ProblemLevel::Error)
        );
        Result {
            value: None,
            problems: self.problems,
        }
    }
    pub fn require(cond: bool, f: impl FnOnce() -> Problem) -> Self {
        if cond { Self::ok() } else { Self::new(f()) }
    }
    pub fn append<T>(&mut self, rhs: impl Into<Result<T>>) -> Option<T> {
        let rhs = rhs.into();
        self.problems.append(rhs.problems);
        rhs.value
    }
}

impl HasProblems for Problems {
    fn problems(&self) -> impl Iterator<Item = &Problem> {
        self.problems.iter()
    }
}

impl FromIterator<Problems> for Problems {
    fn from_iter<T: IntoIterator<Item = Problems>>(iter: T) -> Self {
        let mut problems = im::Vector::new();

        for item in iter {
            problems.append(item.problems);
        }

        Self { problems }
    }
}

impl<A, V: FromIterator<A>> FromIterator<Result<A>> for Result<V> {
    fn from_iter<T: IntoIterator<Item = Result<A>>>(iter: T) -> Self {
        let mut problems = im::Vector::new();

        let values = V::from_iter(iter.into_iter().filter_map(|r| {
            problems.append(r.problems);
            r.value
        }));

        Self {
            value: Some(values),
            problems,
        }
    }
}

impl Combine for Problems {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        Self::from_iter(iter)
    }
}

impl<V: Combine> Combine for Result<V> {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        let mut problems = im::Vector::new();

        let values = V::combine(iter.into_iter().filter_map(|r| {
            problems.append(r.problems);
            r.value
        }));

        Self {
            value: Some(values),
            problems,
        }
    }
}

impl<T> Result<T> {
    pub fn new(t: T) -> Self {
        Self {
            value: Some(t),
            problems: im::Vector::new(),
        }
    }
    pub fn error(problem: Problem) -> Self {
        assert_eq!(problem.header().level, ProblemLevel::Error);
        Self {
            value: None,
            problems: im::Vector::unit(problem),
        }
    }
    pub fn tap_none(self, f: impl FnOnce()) -> Result<T> {
        if self.value.is_none() {
            f();
        }
        self
    }
    pub fn recover(self) -> Result<Option<T>> {
        Result {
            value: Some(self.value),
            problems: self.problems,
        }
    }
    pub fn recover_default(self) -> Self
    where
        T: Default,
    {
        match self.value {
            Some(_) => self,
            None => Result {
                value: Some(T::default()),
                problems: self.problems,
            },
        }
    }
    pub fn and_then<U>(self, f: impl FnOnce(T) -> Result<U>) -> Result<U> {
        match self.value {
            Some(t) => {
                let u = f(t);
                Result {
                    value: u.value,
                    problems: self.problems + u.problems,
                }
            }
            None => Result {
                value: None,
                problems: self.problems,
            },
        }
    }
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Result<U> {
        Result {
            value: self.value.map(f),
            problems: self.problems,
        }
    }
    pub fn value(&self) -> Option<&T> {
        self.value.as_ref()
    }
}

impl<T> HasProblems for Result<T> {
    fn problems(&self) -> impl Iterator<Item = &Problem> {
        self.problems.iter()
    }
}

impl<T> HasProblems for OnceCell<Result<T>> {
    fn problems(&self) -> impl Iterator<Item = &Problem> {
        self.get().into_iter().flat_map(Result::problems)
    }
}

impl<T> Lift<T> for Result<T> {
    fn lift(a: T) -> Self {
        Self::new(a)
    }
}

impl Module {
    pub fn snippet<'a>(
        &'a self,
        resolver: &impl ModuleResolver,
        annotations: impl IntoIterator<Item = Annotation<'a>>,
    ) -> Element<'a> {
        let path = resolver.readable_path(self);
        match resolver.contents(self) {
            Some(source) => Snippet::<Annotation>::source(source)
                .path(path)
                .annotations(annotations)
                .into(),
            None => Origin::path(path).into(),
        }
    }
}

pub type Owned<T> = <<T as Deref>::Target as ToOwned>::Owned;
pub type OwnedReport<'a> = Owned<Report<'a>>;

pub trait Diagnostic {
    fn label(&self) -> Option<Cow<'_, str>>;
    fn report<'a>(
        &'a self,
        title: Title<'a>,
        module: &'a Module,
        span: Span,
        resolver: &impl ModuleResolver,
    ) -> OwnedReport<'a> {
        std::vec![
            title.element(
                module.snippet(
                    resolver,
                    [AnnotationKind::Primary
                        .span(span.into())
                        .label(self.label())]
                )
            )
        ]
    }
}
impl Diagnostic for () {
    fn label(&self) -> Option<Cow<'_, str>> {
        None
    }
}
impl Diagnostic for CompactString {
    fn label(&self) -> Option<Cow<'_, str>> {
        Some(self.as_str().into())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProblemLevel {
    Error,
    Warning,
}

impl From<ProblemLevel> for Level<'static> {
    fn from(value: ProblemLevel) -> Self {
        match value {
            ProblemLevel::Error => Self::ERROR,
            ProblemLevel::Warning => Self::WARNING,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Problem {
    module: Module,
    span: Span,
    kind: ProblemKind,
}

pub const ERROR_COLOR: Color = Color::Ansi(AnsiColor::Red);
pub const WARNING_COLOR: Color = Color::Ansi(AnsiColor::Yellow);

const HIGHLIGHT_BG: Color = Color::Ansi(AnsiColor::Black);
pub const ERROR_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(ERROR_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));
pub const WARNING_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(WARNING_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));

impl Problem {
    pub fn header(&self) -> ProblemHeader {
        self.kind.header()
    }
    pub fn label(&self) -> Option<Cow<'_, str>> {
        self.kind.label()
    }
    pub fn print2(&self, resolver: &impl ModuleResolver) {
        let header = self.header();
        let title = header.title;
        let id = header.id;
        let (name, color, highlight) = match header.level {
            ProblemLevel::Error => ("error", ERROR_COLOR, ERROR_HIGHLIGHT),
            ProblemLevel::Warning => ("warning", WARNING_COLOR, WARNING_HIGHLIGHT),
        };

        let title_kind_style = color.on_default().bold();
        let title_style = Style::new().bold();

        anstream::print!(
            "{title_kind_style}{name} {id:03}{title_kind_style:#}{title_style}: {title}"
        );
        if let Some(label) = self.label() {
            anstream::println!(":{title_style:#} {label}");
        } else {
            anstream::println!("{title_style:#}");
        }

        if let Some(contents) = resolver.contents(&self.module) {
            let snippet = contents.as_str().snippet().lines_containing(self.span);
            let tokens = Lexer::new(&contents)
                .for_range(snippet.range())
                .collect::<Box<_>>();

            struct Error(Style);
            impl Mark for Error {
                fn ignore_nested(&self) -> bool {
                    true
                }
                fn style(&self) -> MarkStyle {
                    self.0.into()
                }
                fn fmt_before(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    write!(f, " ")
                }
                fn fmt_after(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    write!(f, " ")
                }
            }

            anstream::println!(
                "{LINE_STYLE}   /->{LINE_STYLE:#} {}",
                resolver.readable_path(&self.module)
            );
            anstream::println!("{LINE_STYLE}    | {LINE_STYLE:#}");
            anstream::println!(
                "{}",
                snippet
                    .mark_line_numbers()
                    .mark_syntax(&tokens)
                    .mark_semicolons(&tokens)
                    .annotate(std::iter::once(Error(highlight).at(self.span)))
            );
            anstream::println!("{LINE_STYLE}    | {LINE_STYLE:#}");
        }
    }
    pub fn print(&self, resolver: &impl ModuleResolver, renderer: &Renderer) {
        let header = self.header();
        let title =
            Level::from(header.level).primary_title(format!("[{}] {}", header.id, header.title));
        let report = self.kind.report(title, &self.module, self.span, resolver);
        anstream::println!("{}", renderer.render(&report));
    }
}

#[derive(Clone, Copy)]
pub struct ProblemHeader {
    pub id: u32,
    pub level: ProblemLevel,
    pub title: &'static str,
}

macro_rules! diagnostics {
    ($(($variant:ident($value:ty), $id:literal, $level:ident, $title:literal $(,)?)),*$(,)?) => {
        #[derive(Clone, Debug)]
        pub enum ProblemKind {
            $($variant($value)),*
        }
        impl ProblemKind {
            pub fn header(&self) -> ProblemHeader {
                match self {
                    $(Self::$variant(_) => ProblemHeader {
                        id: $id,
                        level: ProblemLevel::$level,
                        title: $title,
                    }),*
                }
            }
            pub fn at(self, module: impl Into<Module>, span: &impl HasSpan) -> Problem {
                Problem {
                    module: module.into(),
                    span: span.span(),
                    kind: self,
                }
            }
        }
        impl Diagnostic for ProblemKind {
            fn label(&self) -> Option<Cow<'_, str>> {
                match self {
                    $(Self::$variant(v) => Diagnostic::label(v)),*
                }
            }
            fn report<'a>(
                &'a self,
                title: Title<'a>,
                module: &'a Module,
                span: Span,
                resolver: &impl ModuleResolver,
            ) -> OwnedReport<'a> {
                match self {
                    $(Self::$variant(v) => Diagnostic::report(v, title, module, span, resolver)),*
                }
            }
        }
    };
}

#[rustfmt::skip]
diagnostics!(

    (UnexpectedToken  (CompactString), 100, Error, "Unexpected token"),
    (UnexpectedNewline(CompactString), 101, Error, "Unexpected newline"),
    (UnexpectedEOF    (CompactString), 102, Error, "Unexpected end of file"),

    (UnknownFile      (CompactString), 103, Error, "Could not access module file"),
    (UnknownLibrary   (CompactString), 104, Error, "Unknown library"),
    (InvalidIdentifier(()),            105, Error, "File name is not a valid identifier"),
);
