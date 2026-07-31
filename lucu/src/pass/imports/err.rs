use std::path::PathBuf;

use crate::error::{Diagnostic, Label};
use crate::module::Library;
use crate::type_table::TypeTable;

#[derive(Clone, Debug)]
pub struct UnknownFile(pub PathBuf);

#[derive(Clone, Debug)]
pub struct UnknownLibrary(pub Library);

impl Diagnostic for UnknownFile {
    fn label<'a>(&'a self, _source: &'a str, _tt: &TypeTable) -> Option<Label<'a>> {
        Some(format!("path resolved to '{}'", self.0.display()).into())
    }
}

impl Diagnostic for UnknownLibrary {
    fn label<'a>(&'a self, _source: &'a str, _tt: &TypeTable) -> Option<Label<'a>> {
        Some(format!("'{}'", self.0).into())
    }
}
