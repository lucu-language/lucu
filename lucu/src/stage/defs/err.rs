use std::sync::Arc;

use compact_str::CompactString;

use crate::err::{Context, ContextLevel, Diagnostic, Label};
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct MultipleDefinitions {
    pub name: CompactString,
    pub redefined: Arc<[Span]>,
}

impl Diagnostic for MultipleDefinitions {
    fn label(&self) -> Option<Label<'_>> {
        None
    }
    fn context(&self, f: &mut dyn FnMut(Context<'_>)) {
        for (i, span) in self.redefined.iter().copied().enumerate() {
            f(Context {
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
}
