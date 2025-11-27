use std::collections::{HashMap, hash_map};
use std::fmt::Display;

use compact_str::{CompactString, format_compact};

use crate::err::{ProblemKind, Problems, Result};
use crate::module::{Module, ModuleResolver, UnknownModule};
use crate::span::{HasSpan, Span, Spanned};
use crate::stage::ast::{self, inner};
use crate::stage::token::is_valid_identifier;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Import {
    Implicit,
    Named(CompactString),
}

impl Display for Import {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Import::Implicit => Ok(()),
            Import::Named(compact_string) => compact_string.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Imports(HashMap<Import, Module>);

impl<'a> IntoIterator for &'a Imports {
    type Item = (&'a Import, &'a Module);

    type IntoIter = hash_map::Iter<'a, Import, Module>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl Imports {
    pub fn iter(&self) -> impl Iterator<Item = (&Import, &Module)> {
        self.0.iter()
    }
    pub fn from(
        resolver: &impl ModuleResolver,
        parent: &Module,
        ast: &ast::Module,
    ) -> Result<Self> {
        let mut problems = Problems::ok();

        let mut map = HashMap::new();

        if let Some(module) = resolver.preamble(parent) {
            map.insert(Import::Implicit, module);
        }

        for import in &ast.imports {
            let module = Module::from_import(parent, import.path.as_str());

            // get identifier and check if valid
            let ident = match &import.ident {
                Some(ident) => ident.as_str().into(),
                None => {
                    let ident = Self::import_name(&import.path);
                    problems.append(Problems::require(
                        is_valid_identifier(ident.as_str()),
                        || ProblemKind::InvalidIdentifier(()).at(parent, &ident),
                    ));
                    ident.0.0
                }
            };

            problems.append(Self::require_import_exists(
                resolver, import, &module, parent,
            ));

            // TODO: check for duplicates
            map.insert(Import::Named(ident), module);
        }

        problems.with(Self(map))
    }
    fn library_span(path: &ast::String) -> Span {
        let len = path.as_str().find(':').unwrap_or_default();

        let mut inner = path.span().inner();
        inner.end = inner.start + len as u32;

        inner
    }
    fn import_name(path: &ast::String) -> ast::Ident {
        let without_extension = path
            .as_str()
            .rsplit_once('.')
            .map(|t| t.0)
            .unwrap_or(path.as_str());
        let end = path.span().end - 1 - (path.as_str().len() - without_extension.len()) as u32;

        let ident = without_extension
            .rsplit_once(['/', '\\', ':'])
            .map(|t| t.1)
            .unwrap_or(without_extension);
        let start = path.span().start + 1 + (without_extension.len() - ident.len()) as u32;

        Spanned(inner::Ident(ident.into()), Span::new(start, end))
    }
    fn require_import_exists(
        resolver: &impl ModuleResolver,
        import: &ast::Import,
        module: &Module,
        parent: &Module,
    ) -> Problems {
        match resolver.exists(module) {
            Ok(()) => Problems::ok(),
            Err(UnknownModule::UnknownLibrary(lib)) => {
                ProblemKind::UnknownLibrary(format_compact!("'{}'", lib))
                    .at(parent, &Self::library_span(&import.path))
                    .into()
            }
            Err(UnknownModule::UnknownFile(file)) => {
                ProblemKind::UnknownFile(format_compact!("path resolved to {}", file.display()))
                    .at(parent, &import.path)
                    .into()
            }
        }
    }
}
