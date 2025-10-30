use core::fmt;
use std::{
    borrow::Cow,
    path::{Path, PathBuf},
};

use compact_str::{CompactString, format_compact};
use path_clean::{PathClean, clean};

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Library(CompactString);

impl Library {
    pub const MAIN: Library = Library(CompactString::const_new("main"));
    pub const BUILTIN: Library = Library(CompactString::const_new("builtin"));
    pub const CORE: Library = Library(CompactString::const_new("core"));

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

#[derive(Clone)]
pub struct LibraryDir {
    pub location: PathBuf,
    pub preamble: Option<Module>,
    pub modules_override: Option<include_dir::Dir<'static>>,
}

impl LibraryDir {
    pub fn new<P: Into<PathBuf>>(location: P) -> Self {
        let path: PathBuf = location.into();
        let absolute_path = if path.is_absolute() {
            path.clean()
        } else {
            std::env::current_dir()
                .expect("ICE: library path is relative but cannot access current dir")
                .join(path)
                .clean()
        };

        Self {
            location: absolute_path,
            preamble: None,
            modules_override: None,
        }
    }
    pub fn with_preamble(mut self, library: Library, path: impl AsRef<Path>) -> Self {
        self.preamble = Some(Module::new(library, path));
        self
    }
    pub fn with_modules(mut self, modules: include_dir::Dir<'static>) -> Self {
        self.modules_override = Some(modules);
        self
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Module {
    pub library: Library,
    pub relative_path: CompactString,
}

impl Module {
    pub fn new(library: Library, path: impl AsRef<Path>) -> Self {
        let relative_path = clean(path)
            .into_os_string()
            .into_string()
            .expect("ICE: path is suddenly non-utf8");
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
        let (lib, path) = match import.split_once(':') {
            Some((lib, path)) => {
                let lib = if lib.is_empty() {
                    parent.library.clone()
                } else {
                    Library::new(lib)
                };
                (lib, Cow::Borrowed(Path::new(path)))
            }
            None => {
                let lib = parent.library.clone();
                let parent_file = PathBuf::from(&parent.relative_path);
                let parent_dir = parent_file
                    .parent()
                    .expect("ICE: the root directory is a module");
                (lib, Cow::Owned(parent_dir.join(import)))
            }
        };
        Self::new(lib, path)
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

#[derive(Debug)]
pub enum UnknownModule {
    UnknownLibrary(Library),
    UnknownFile(PathBuf),
}
