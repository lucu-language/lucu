use core::fmt;
use std::path::{Path, PathBuf};

use compact_str::{CompactString, format_compact};
use path_clean::clean;

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Library(CompactString);

impl Library {
    pub const MAIN: Library = Library::const_new("main");
    pub const BUILTIN: Library = Library::const_new("builtin");
    pub const CORE: Library = Library::const_new("core");

    pub const fn const_new(name: &'static str) -> Self {
        Self(CompactString::const_new(name))
    }
    pub fn new(name: &str) -> Self {
        Self(CompactString::new(name))
    }
}

impl fmt::Display for Library {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Module {
    pub library: Library,
    pub relative_path: CompactString,
}

impl Module {
    pub fn new(library: Library, path: impl AsRef<Path>) -> Self {
        let relative_path = clean(path)
            .into_os_string()
            .into_string()
            .expect("ICE: module relative path is non-utf8");
        let relative_path = relative_path
            .strip_suffix(".lucu")
            .unwrap_or(&relative_path)
            .into();
        Self {
            library,
            relative_path,
        }
    }
    pub fn from_import(parent: &Module, import: &str) -> Self {
        match import.split_once(':') {
            Some((lib, path)) => {
                let lib = if lib.is_empty() {
                    parent.library.clone()
                } else {
                    Library::new(lib)
                };
                Self::new(lib, path)
            }
            None => {
                let lib = parent.library.clone();
                let parent_dir = Path::new(&parent.relative_path)
                    .parent()
                    .expect("ICE: the root directory is a module");
                Self::new(lib, parent_dir.join(import))
            }
        }
    }
    pub fn path_with_extension(&self) -> CompactString {
        if self.relative_path.contains('.') {
            self.relative_path.clone()
        } else {
            format_compact!("{}.lucu", self.relative_path)
        }
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.library != Library::MAIN {
            write!(f, "{}:", self.library)?;
        }
        write!(f, "{}", self.relative_path)?;
        Ok(())
    }
}

impl fmt::Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}:{}\"", self.library, self.relative_path)
    }
}

pub trait ModuleResolver {
    fn main(&self) -> Module;

    fn exists(&self, module: &Module) -> Result<(), UnknownModule>;

    fn preamble(&self, module: &Module) -> Option<Module>;
    fn contents(&self, module: &Module) -> Option<String>;
    fn readable_path(&self, module: &Module) -> String;
}

#[derive(Debug)]
pub enum UnknownModule {
    UnknownLibrary(Library),
    UnknownFile(PathBuf),
}
