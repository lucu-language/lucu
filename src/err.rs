use std::borrow::Cow;

use annotate_snippets::{
    Annotation, AnnotationKind, Element, Group, Level, Origin, Renderer, Snippet, Title,
};
use compact_str::CompactString;
use do_notation::Lift;

use crate::{
    module::{Module, ModuleResolver},
    stage::lexer::token::Span,
};

#[must_use = "this `Result` may have diagnostics, which should be handled"]
#[derive(Clone, Debug)]
pub struct Result<T = ()> {
    pub value: Option<T>,
    pub diagnostics: im::Vector<LucuDiagnostic>,
}

impl<T> Default for Result<T>
where
    T: Default,
{
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl Result<()> {
    pub fn ok() -> Self {
        Self::new(())
    }
    pub fn require(cond: bool, f: impl FnOnce() -> LucuDiagnostic) -> Self {
        if cond {
            Self::ok()
        } else {
            Self::ok().with(f())
        }
    }
    pub fn add<T>(&mut self, rhs: Result<T>) -> Option<T> {
        self.diagnostics.append(rhs.diagnostics);
        rhs.value
    }
}

impl From<Option<LucuDiagnostic>> for Result<()> {
    fn from(value: Option<LucuDiagnostic>) -> Self {
        match value {
            Some(diag) => Result::ok().with(diag),
            None => Result::ok(),
        }
    }
}

impl<T> From<std::result::Result<T, LucuDiagnostic>> for Result<T> {
    fn from(value: std::result::Result<T, LucuDiagnostic>) -> Self {
        match value {
            Ok(t) => Result::new(t),
            Err(e) => Result::error(e),
        }
    }
}

impl<A, V: FromIterator<A>> FromIterator<Result<A>> for Result<V> {
    fn from_iter<T: IntoIterator<Item = Result<A>>>(iter: T) -> Self {
        let mut diagnostics = im::Vector::new();

        let values = V::from_iter(iter.into_iter().filter_map(|r| {
            diagnostics.append(r.diagnostics);
            r.value
        }));

        Self {
            value: Some(values),
            diagnostics,
        }
    }
}

impl<T> Result<T>
where
    T: Default,
{
    pub fn or_default(self) -> Self {
        match self.value {
            Some(_) => self,
            None => Result {
                value: Some(T::default()),
                diagnostics: self.diagnostics,
            },
        }
    }
}

impl<T> Result<T> {
    pub fn new(t: T) -> Self {
        Self {
            value: Some(t),
            diagnostics: im::Vector::new(),
        }
    }
    pub fn tap_none(self, f: impl FnOnce()) -> Result<T> {
        if self.value.is_none() {
            f();
        }
        self
    }
    pub fn discard(self) -> Result<()> {
        Result {
            value: Some(()),
            diagnostics: self.diagnostics,
        }
    }
    pub fn with(self, diagnostic: LucuDiagnostic) -> Self {
        Self {
            value: self.value,
            diagnostics: self.diagnostics + im::Vector::unit(diagnostic),
        }
    }
    pub fn error(diagnostic: LucuDiagnostic) -> Self {
        assert_eq!(diagnostic.level(), DiagnosticLevel::Error);
        Self {
            value: None,
            diagnostics: im::Vector::unit(diagnostic),
        }
    }
    pub fn and_then<U>(self, f: impl FnOnce(T) -> Result<U>) -> Result<U> {
        match self.value {
            Some(t) => {
                let u = f(t);
                Result {
                    value: u.value,
                    diagnostics: self.diagnostics + u.diagnostics,
                }
            }
            None => Result {
                value: None,
                diagnostics: self.diagnostics,
            },
        }
    }
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Result<U> {
        Result {
            value: self.value.map(f),
            diagnostics: self.diagnostics,
        }
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
            Ok(source) => Snippet::<Annotation>::source(source)
                .path(path)
                .annotations(annotations)
                .into(),
            Err(_) => Origin::path(path).into(),
        }
    }
}

pub trait Diagnostic {
    fn module(&self) -> &Module;
    fn span(&self) -> Span;
    fn label(&self) -> Option<Cow<str>> {
        None
    }

    fn report<'a>(&'a self, title: Title<'a>, resolver: &impl ModuleResolver) -> Vec<Group<'a>> {
        vec![
            title.element(
                self.module().snippet(
                    resolver,
                    [AnnotationKind::Primary
                        .span(self.span().into())
                        .label(self.label())],
                ),
            ),
        ]
    }
}

#[derive(Clone, Debug)]
pub struct SimpleDiagnostic(Module, Span, Option<CompactString>);

impl SimpleDiagnostic {
    pub fn new(module: Module, span: Span) -> Self {
        Self(module, span, None)
    }
    pub fn label(mut self, label: impl Into<CompactString>) -> Self {
        self.2 = Some(label.into());
        self
    }
}

impl Diagnostic for SimpleDiagnostic {
    fn module(&self) -> &Module {
        &self.0
    }
    fn span(&self) -> Span {
        self.1
    }
    fn label(&self) -> Option<Cow<str>> {
        self.2.as_ref().map(|label| Cow::Borrowed(label.as_str()))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DiagnosticLevel {
    Error,
    Warning,
}

impl From<DiagnosticLevel> for Level<'static> {
    fn from(value: DiagnosticLevel) -> Self {
        match value {
            DiagnosticLevel::Error => Self::ERROR,
            DiagnosticLevel::Warning => Self::WARNING,
        }
    }
}

macro_rules! diagnostics {
    ($(($variant:ident($value:ty), $id:literal, $level:ident, $title:literal $(,)?)),*$(,)?) => {
        #[derive(Clone, Debug)]
        pub enum LucuDiagnostic {
            $($variant($value)),*
        }
        impl LucuDiagnostic {
            pub fn id(&self) -> u32 {
                match self {
                    $(Self::$variant(_) => $id),*
                }
            }
            pub fn level(&self) -> DiagnosticLevel {
                match self {
                    $(Self::$variant(_) => DiagnosticLevel::$level),*
                }
            }
            pub fn title(&self) -> &'static str {
                match self {
                    $(Self::$variant(_) => $title),*
                }
            }
        }
        impl Diagnostic for LucuDiagnostic {
            fn module(&self) -> &Module {
                match self {
                    $(Self::$variant(v) => Diagnostic::module(v)),*
                }
            }
            fn span(&self) -> Span {
                match self {
                    $(Self::$variant(v) => Diagnostic::span(v)),*
                }
            }
            fn report<'a>(
                &'a self,
                title: Title<'a>,
                resolver: &impl ModuleResolver,
            ) -> Vec<Group<'a>> {
                match self {
                    $(Self::$variant(v) => Diagnostic::report(v, title, resolver)),*
                }
            }
        }
    };
}

impl LucuDiagnostic {
    pub fn print(&self, resolver: &impl ModuleResolver, renderer: &Renderer) {
        let title =
            Level::from(self.level()).primary_title(format!("[{}] {}", self.id(), self.title()));
        let report = self.report(title, resolver);
        anstream::println!("{}", renderer.render(&report));
    }
}

#[rustfmt::skip]
diagnostics!(
    (UnexpectedToken  (SimpleDiagnostic),      0, Error, "Unexpected token"),
    (UnexpectedEOF    (SimpleDiagnostic),      1, Error, "Unexpected end of file"),

    (UnknownFile      (SimpleDiagnostic),      2, Error, "Could not access module file"),
    (UnknownLibrary   (SimpleDiagnostic),      3, Error, "Unknown library"),
    (InvalidIdentifier(SimpleDiagnostic),      4, Error, "File name is not a valid identifier"),
);
