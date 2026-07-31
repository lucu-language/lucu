use std::iter;
use std::sync::Arc;

use crate::error::{Context, ContextLevel, Diagnostic, Label};
use crate::module::Module;
use crate::span::Span;
use crate::type_table::{Effect, Kind, Term, Type, TypeTable};

#[derive(Clone, Copy, Debug)]
pub struct InvalidEffectItem;

impl Diagnostic for InvalidEffectItem {
    fn label(&self, _source: &str, _tt: &TypeTable) -> Option<Label<'_>> {
        Some("only functions are allowed".into())
    }
}

#[derive(Clone, Debug)]
pub enum Namespace {
    Local,
    Module(Module),
}

#[derive(Clone, Debug)]
pub struct UnknownSymbol {
    pub symbol: Span,
    pub namespace: Namespace,
}

impl Diagnostic for UnknownSymbol {
    fn label<'a>(&'a self, source: &'a str, _tt: &TypeTable) -> Option<Label<'a>> {
        let name = &source[self.symbol];
        Some(match &self.namespace {
            Namespace::Local => format!("'{name}' not found in scope").into(),
            Namespace::Module(module) => format!("'{name}' not found in module '{module}'").into(),
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeMismatch {
    pub expected: Type,
    pub found: Type,
}

impl Diagnostic for TypeMismatch {
    fn label(&self, _source: &str, tt: &TypeTable) -> Option<Label<'_>> {
        Some(
            format!(
                "expected {}, found {}",
                self.expected.display(tt),
                self.found.display(tt)
            )
            .into(),
        )
    }
}

#[derive(Clone, Copy, Debug)]
pub struct KindMismatch {
    pub expected: Kind,
    pub found: Kind,
}

impl Diagnostic for KindMismatch {
    fn label(&self, _source: &str, tt: &TypeTable) -> Option<Label<'_>> {
        Some(
            format!(
                "expected {}, found {}",
                self.expected.display(tt),
                self.found.display(tt)
            )
            .into(),
        )
    }
}

#[derive(Clone, Copy, Debug)]
pub enum FoundLiteral {
    Integer,
    String,
    Character,
}

#[derive(Clone, Copy, Debug)]
pub struct LiteralMismatch {
    pub expected: Type,
    pub found: FoundLiteral,
}

impl Diagnostic for LiteralMismatch {
    fn label<'a>(&'a self, _source: &'a str, tt: &TypeTable) -> Option<Label<'a>> {
        Some(match self.found {
            FoundLiteral::Integer => format!(
                "expected {}, found integer literal",
                self.expected.display(tt)
            )
            .into(),
            FoundLiteral::String => format!(
                "expected {}, found string literal",
                self.expected.display(tt)
            )
            .into(),
            FoundLiteral::Character => format!(
                "expected {}, found character literal",
                self.expected.display(tt)
            )
            .into(),
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct NotEnoughInfo(pub Term);

impl Diagnostic for NotEnoughInfo {
    fn label<'a>(&'a self, _source: &'a str, tt: &TypeTable) -> Option<Label<'a>> {
        Some(format!("found '{}'", self.0.display(tt)).into())
    }
}

#[derive(Clone, Debug)]
pub struct SignatureMismatch {
    pub defined_module: Module,
    pub defined_span: Span,
}

impl Diagnostic for SignatureMismatch {
    fn label<'a>(&'a self, _source: &'a str, _tt: &TypeTable) -> Option<Label<'a>> {
        None
    }
    fn context<'a>(
        &'a self,
        _source: &'a str,
        _tt: &'a TypeTable,
    ) -> impl Iterator<Item = Context<'a>> {
        iter::once(Context {
            module: Some(self.defined_module.clone()),
            span: self.defined_span,
            label: Some("effect function declared here".into()),
            level: ContextLevel::Info,
        })
    }
}

#[derive(Clone, Copy, Debug)]
pub struct MissingEffects(pub Effect);

impl Diagnostic for MissingEffects {
    fn label<'a>(&'a self, _source: &'a str, tt: &TypeTable) -> Option<Label<'a>> {
        Some(self.0.display(tt).to_string().into())
    }
}
