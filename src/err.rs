use std::borrow::Cow;

use annotate_snippets::{
    Annotation, AnnotationKind, Element, Group, Level, Origin, Renderer, Snippet, Title,
};
use compact_str::CompactString;
use do_notation::Lift;

use crate::{
    module::{Module, ModuleResolver},
    stage::lexer::Span,
};

#[must_use = "this `Result` may have diagnostics, which should be handled"]
#[derive(Clone, Debug)]
pub struct Result<T> {
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
}

impl<A, V: FromIterator<A>> FromIterator<Result<A>> for Result<V> {
    fn from_iter<T: IntoIterator<Item = Result<A>>>(iter: T) -> Self {
        let mut diagnostics = im::Vector::new();
        let mut complete = true;

        let values = V::from_iter(iter.into_iter().filter_map(|r| {
            diagnostics.append(r.diagnostics);
            complete &= r.value.is_some();
            r.value
        }));

        Self {
            value: complete.then_some(values),
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
    pub fn checked(self, f: impl FnOnce(&T) -> Option<LucuDiagnostic>) -> Self {
        match &self.value {
            Some(val) => match f(val) {
                Some(diag) => Self {
                    value: self.value,
                    diagnostics: self.diagnostics + im::Vector::unit(diag),
                },
                None => self,
            },
            None => self,
        }
    }
    pub fn prepended(self, diagnostics: im::Vector<LucuDiagnostic>) -> Self {
        Self {
            value: self.value,
            diagnostics: diagnostics + self.diagnostics,
        }
    }
    pub fn and_then<U>(self, f: impl FnOnce(T) -> Result<U>) -> Result<U> {
        match self.value {
            Some(t) => f(t).prepended(self.diagnostics),
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
    (UnknownFile      (SimpleDiagnostic), 0, Error, "Could not access module file"),
    (UnknownLibrary   (SimpleDiagnostic), 1, Error, "Unknown library"),
    (InvalidIdentifier(SimpleDiagnostic), 2, Error, "File name is not a valid identifier"),
    (UnexpectedToken  (SimpleDiagnostic), 3, Error, "Unexpected token"),
    (UnexpectedEOF    (SimpleDiagnostic), 4, Error, "Unexpected end of file"),
);
