use std::sync::Arc;

use compact_str::CompactString;

use crate::error::{Context, ContextLevel, Diagnostic, Label};
use crate::span::Span;
use crate::type_table::TypeTable;

#[derive(Clone, Debug)]
pub struct MultipleDefinitions {
    pub name: CompactString,
    pub redefined: Arc<[Span]>,
}

impl Diagnostic for MultipleDefinitions {
    fn label(&self, _source: &str, _tt: &TypeTable) -> Option<Label<'_>> {
        None
    }
    fn context<'a>(&'a self, _source: &str, _tt: &TypeTable) -> impl Iterator<Item = Context<'a>> {
        self.redefined
            .iter()
            .copied()
            .enumerate()
            .map(|(i, span)| Context {
                module: None,
                span,
                label: Some(if i == 0 {
                    "later redefined here".into()
                } else {
                    "and here".into()
                }),
                level: ContextLevel::Info,
            })
    }
}
