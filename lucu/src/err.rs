use std::borrow::Cow;
use std::ops::Add;

use anstyle::{AnsiColor, Color, Style};
use compact_str::CompactString;
use do_notation::Lift;
use line_column::line_column;
use lucu_annotate::ansi::MarkStyle;
use lucu_annotate::{Annotate, Mark};

use crate::annotate::{AnnotateExt, LINE_STYLE};
use crate::module::{Module, ModuleResolver};
use crate::span::{HasSpan, Span};
use crate::stage::ast::err::Expected;
use crate::stage::ast::visit::Combine;
use crate::stage::defs::err::MultipleDefinitions;
use crate::stage::token::lexer::Lexer;

pub trait HasProblems {
    fn problems(&self) -> impl Iterator<Item = &Problem>;
    fn print_problems(&self, resolver: &impl ModuleResolver, compact: bool) {
        for (i, problem) in self.problems().enumerate() {
            if i > 0 && compact {
                println!();
            }
            problem.print(resolver, compact);
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

impl Add for Problems {
    type Output = Problems;

    fn add(self, rhs: Self) -> Self::Output {
        Problems {
            problems: self.problems + rhs.problems,
        }
    }
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
        assert!(self.has_error());
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
    pub fn has_error(&self) -> bool {
        self.problems
            .iter()
            .any(|d| d.header().level == ProblemLevel::Error)
    }
    pub fn and_then<T>(self, f: impl FnOnce(()) -> Result<T>) -> Result<T> {
        self.with(()).and_then(f)
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

impl<T> Lift<T> for Result<T> {
    fn lift(a: T) -> Self {
        Self::new(a)
    }
}

pub type Label<'a> = Cow<'a, str>;

pub struct Context<'a> {
    pub module: Option<Module>,
    pub span: Span,
    pub label: Option<Label<'a>>,
    pub level: ContextLevel,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ContextLevel {
    Same,
    Info,
}

pub trait Diagnostic {
    fn label(&self) -> Option<Label<'_>>;
    #[expect(unused_variables)]
    fn context(&self, f: &mut dyn FnMut(Context<'_>)) {}
}
impl Diagnostic for () {
    fn label(&self) -> Option<Label<'_>> {
        None
    }
}
impl Diagnostic for CompactString {
    fn label(&self) -> Option<Label<'_>> {
        Some(self.as_str().into())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProblemLevel {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct Problem {
    module: Module,
    span: Span,
    kind: ProblemKind,
}

pub const ERROR_COLOR: Color = Color::Ansi(AnsiColor::Red);
pub const WARNING_COLOR: Color = Color::Ansi(AnsiColor::Yellow);
pub const INFO_COLOR: Color = Color::Ansi(AnsiColor::Green);

const HIGHLIGHT_BG: Color = Color::Ansi(AnsiColor::Black);
pub const ERROR_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(ERROR_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));
pub const WARNING_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(WARNING_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));
pub const INFO_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(INFO_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));

pub const TITLE_STYLE: Style = Style::new().bold();
pub const CONTEXT_STYLE: Style = Style::new()
    .italic()
    .fg_color(Some(Color::Ansi(AnsiColor::BrightWhite)));
pub const LABEL_STYLE: Style = Style::new();
pub const PATH_STYLE: Style = LINE_STYLE;

impl Problem {
    pub fn header(&self) -> ProblemHeader {
        self.kind.header()
    }
    pub fn label(&self) -> Option<Cow<'_, str>> {
        self.kind.label()
    }
    pub fn print(&self, resolver: &impl ModuleResolver, compact: bool) {
        let header = self.header();
        let title = header.title;
        let id = header.id;
        let (name, color, highlight) = match header.level {
            ProblemLevel::Error => ("error", ERROR_COLOR, ERROR_HIGHLIGHT),
            ProblemLevel::Warning => ("warning", WARNING_COLOR, WARNING_HIGHLIGHT),
        };

        let title_kind_style = TITLE_STYLE.fg_color(Some(color));
        anstream::print!(
            "{title_kind_style}{name} {id:03}{title_kind_style:#}{TITLE_STYLE}: {title}"
        );
        if let Some(label) = self.label() {
            anstream::println!(":{TITLE_STYLE:#} {LABEL_STYLE}{label}{LABEL_STYLE:#}");
        } else {
            anstream::println!("{TITLE_STYLE:#}");
        }

        // Problem location
        let contents = resolver.contents(&self.module);
        let path = resolver.readable_path(&self.module);

        if let Some(contents) = contents.as_deref() {
            print_highlight(highlight, self.span, Some(&path), contents, compact);
        }

        // Context locations
        self.kind.context(&mut |ctx| {
            let (contents, path) = if let Some(module) = ctx.module {
                (
                    resolver.contents(&module).map(Cow::Owned),
                    Some(resolver.readable_path(&module)),
                )
            } else {
                (contents.as_deref().map(Cow::Borrowed), None)
            };

            if let Some(contents) = contents.as_deref() {
                let (name, color, highlight) = match ctx.level {
                    ContextLevel::Same => (name, color, highlight),
                    ContextLevel::Info => ("info", INFO_COLOR, INFO_HIGHLIGHT),
                };
                let context_kind_style = CONTEXT_STYLE.fg_color(Some(color));

                if let Some(label) = ctx.label {
                    anstream::println!("{context_kind_style}{name}{context_kind_style:#}{CONTEXT_STYLE}: {label}{CONTEXT_STYLE:#}");
                } else if path.is_none() {
                    anstream::println!("{LINE_STYLE} ...  {LINE_STYLE:#}");
                }

                print_highlight(highlight, ctx.span, path.as_deref(), contents,compact);
            }
        });
    }
}

fn print_highlight(
    highlight: Style,
    span: Span,
    path: Option<&str>,
    contents: &str,
    compact: bool,
) {
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

    let (line, col) = line_column(contents, span.start as usize);
    let snippet = contents.snippet().lines_containing(span);
    let tokens = Lexer::new(contents)
        .for_range(snippet.range())
        .collect::<Box<_>>();

    if let Some(path) = path {
        anstream::println!(
            "{LINE_STYLE}   /->{LINE_STYLE:#} {PATH_STYLE}{path}:{line}:{col}{PATH_STYLE:#}",
        );
    }

    if !compact {
        anstream::println!("{LINE_STYLE}    | {LINE_STYLE:#}");
    }
    anstream::println!(
        "{}",
        snippet
            .mark_line_numbers()
            .mark_syntax(&tokens)
            .mark_semicolons(&tokens)
            .annotate(std::iter::once(Error(highlight).at(span)))
    );
    if !compact {
        anstream::println!("{LINE_STYLE}    | {LINE_STYLE:#}");
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
            fn context(&self, f: &mut dyn FnMut(Context<'_>)) {
                match self {
                    $(Self::$variant(v) => Diagnostic::context(v, f)),*
                }
            }
        }
    };
}

#[rustfmt::skip]
diagnostics!(
    (UnexpectedToken  (Expected), 100, Error, "Unexpected token"),
    (UnexpectedNewline(Expected), 101, Error, "Unexpected newline"),
    (UnexpectedEOF    (Expected), 102, Error, "Unexpected end of file"),

    (UnknownFile      (CompactString), 103, Error, "Could not access module file"),
    (UnknownLibrary   (CompactString), 104, Error, "Unknown library"),
    (InvalidIdentifier(()),            105, Error, "File name is not a valid identifier"),

    (MultipleDefinitions(MultipleDefinitions), 106, Error, "Name is defined multiple times"),
);
