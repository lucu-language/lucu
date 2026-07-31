use crate::error::{Diagnostic, Label};

#[derive(Clone, Copy, Debug)]
pub struct InvalidEffectItem;

impl Diagnostic for InvalidEffectItem {
    fn label(&self) -> Option<Label<'_>> {
        Some("only functions are allowed".into())
    }
}
