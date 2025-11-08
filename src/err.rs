use std::borrow::Cow;

use annotate_snippets::{
    Annotation, AnnotationKind, Element, Group, Level, Origin, Renderer, Snippet, Title,
};
use compact_str::CompactString;
use do_notation::Lift;

use crate::{
    module::{Module, ModuleResolver},
    stage::{lexer::token::Span, parser::visitor::Combine},
};

#[must_use = "this `Result` may have diagnostics, which should be handled"]
#[derive(Clone, Debug)]
pub struct Result<T> {
    value: Option<T>,
    diagnostics: im::Vector<LucuDiagnostic>,
}

#[must_use = "`Problems` may have diagnostics, which should be handled"]
#[derive(Clone, Debug, Default)]
pub struct Problems {
    diagnostics: im::Vector<LucuDiagnostic>,
}

impl From<Problems> for Result<()> {
    fn from(value: Problems) -> Self {
        Self {
            value: Some(()),
            diagnostics: value.diagnostics,
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
            diagnostics: im::Vector::new(),
        }
    }
    pub fn new(diagnostic: LucuDiagnostic) -> Self {
        Self {
            diagnostics: im::Vector::unit(diagnostic),
        }
    }
    pub fn with<T>(self, value: T) -> Result<T> {
        Result {
            value: Some(value),
            diagnostics: self.diagnostics,
        }
    }
    pub fn require(cond: bool, f: impl FnOnce() -> LucuDiagnostic) -> Self {
        if cond { Self::ok() } else { Self::new(f()) }
    }
    pub fn diagnostics(&self) -> impl Iterator<Item = &LucuDiagnostic> {
        self.diagnostics.iter()
    }
    pub fn append<T>(&mut self, rhs: impl Into<Result<T>>) -> Option<T> {
        let rhs = rhs.into();
        self.diagnostics.append(rhs.diagnostics);
        rhs.value
    }
}

impl FromIterator<Problems> for Problems {
    fn from_iter<T: IntoIterator<Item = Problems>>(iter: T) -> Self {
        let mut diagnostics = im::Vector::new();

        for problems in iter {
            diagnostics.append(problems.diagnostics);
        }

        Self { diagnostics }
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

impl Combine for Problems {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        Self::from_iter(iter)
    }
}

impl<V: Combine> Combine for Result<V> {
    fn combine(iter: impl IntoIterator<Item = Self>) -> Self {
        let mut diagnostics = im::Vector::new();

        let values = V::combine(iter.into_iter().filter_map(|r| {
            diagnostics.append(r.diagnostics);
            r.value
        }));

        Self {
            value: Some(values),
            diagnostics,
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
    pub fn error(diagnostic: LucuDiagnostic) -> Self {
        assert_eq!(diagnostic.level(), DiagnosticLevel::Error);
        Self {
            value: None,
            diagnostics: im::Vector::unit(diagnostic),
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
            diagnostics: self.diagnostics,
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
                diagnostics: self.diagnostics,
            },
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
    pub fn value(&self) -> Option<&T> {
        self.value.as_ref()
    }
    pub fn diagnostics(&self) -> impl Iterator<Item = &LucuDiagnostic> {
        self.diagnostics.iter()
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
