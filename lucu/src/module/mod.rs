use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::{env, fmt, fs};

use compact_str::{CompactString, ToCompactString, format_compact};
use include_dir::{Dir, File, include_dir};
use path_clean::{PathClean, clean};

#[cfg(feature = "watcher")]
pub mod watcher;

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Library(CompactString);

impl Library {
    pub const MAIN: Library = Library::const_new("main");
    pub const BUILTIN: Library = Library::const_new("builtin");
    pub const CORE: Library = Library::const_new("core");
    pub const LIBC: Library = Library::const_new("libc");

    pub const fn const_new(name: &'static str) -> Self {
        Self(CompactString::const_new(name))
    }
    pub fn new(name: &str) -> Self {
        Self(CompactString::new(name))
    }
}

impl Default for Library {
    fn default() -> Self {
        Self::MAIN
    }
}

impl From<&Library> for Library {
    fn from(value: &Library) -> Self {
        Self(value.0.to_owned())
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

impl Default for Module {
    fn default() -> Self {
        Self::MAIN
    }
}

impl From<&Module> for Module {
    fn from(value: &Module) -> Self {
        Self {
            library: value.library.to_owned(),
            relative_path: value.relative_path.to_owned(),
        }
    }
}

pub fn import_name(import: &str) -> &str {
    let relative_path = import
        .split_once(':')
        .map(|(pkg, path)| if path.is_empty() { pkg } else { path })
        .unwrap_or(import);
    let basename = relative_path
        .rsplit_once(['/', '\\'])
        .map(|(_, base)| base)
        .unwrap_or(relative_path);
    basename
        .rsplit_once('.')
        .map(|(name, _)| name)
        .unwrap_or(basename)
}

impl Module {
    pub const MAIN: Module = Self {
        library: Library::MAIN,
        relative_path: CompactString::const_new("main"),
    };
    pub const BUILTIN_C: Module = Self {
        library: Library::BUILTIN,
        relative_path: CompactString::const_new("c"),
    };
    pub const BUILTIN_TYPES: Module = Self {
        library: Library::BUILTIN,
        relative_path: CompactString::const_new("types"),
    };
    pub const BUILTIN: Module = Self {
        library: Library::BUILTIN,
        relative_path: CompactString::const_new("builtin"),
    };
    pub const LIBC_TYPES: Module = Self {
        library: Library::LIBC,
        relative_path: CompactString::const_new("types"),
    };
    pub const CORE: Module = Self {
        library: Library::CORE,
        relative_path: CompactString::const_new("core"),
    };
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
    pub fn name(&self) -> &str {
        import_name(&self.relative_path)
    }
    pub fn from_import(parent: &Module, import: &str) -> Self {
        match import.split_once(':') {
            Some((lib, path)) => {
                let lib = if lib.is_empty() {
                    parent.library.clone()
                } else {
                    Library::new(lib)
                };
                let path = if path.is_empty() {
                    import_name(&lib.0)
                } else {
                    path
                };
                Self::new(lib.clone(), path)
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
        let filename = self
            .relative_path
            .rsplit_once(['/', '\\'])
            .map(|t| t.1)
            .unwrap_or(&self.relative_path);
        if filename.contains('.') {
            filename.to_compact_string()
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

pub trait Modules {
    fn libraries(&self) -> &impl Libraries;

    fn path(&self, module: &Module) -> Result<PathBuf, UnknownModule> {
        Ok(self
            .libraries()
            .path(&module.library)?
            .join(module.path_with_extension())
            .clean())
    }
    fn relative_path(&self, module: &Module) -> Option<PathBuf> {
        self.libraries()
            .relative_path(&module.library)
            .map(|dir| dir.join(module.path_with_extension()).clean())
    }

    fn preamble(&self, module: &Module) -> Option<Module> {
        self.libraries()
            .preamble(&module.library)
            .filter(|preamble| preamble != module)
    }

    fn exists(&self, module: &Module) -> Result<(), UnknownModule>;
    fn contents(&self, module: &Module) -> Option<String>;
}

pub trait Libraries {
    fn path(&self, library: &Library) -> Result<PathBuf, UnknownModule>;
    fn relative_path(&self, library: &Library) -> Option<PathBuf> {
        let current_dir = env::current_dir().ok();
        let library_dir = self.path(library).ok();
        Option::zip(current_dir, library_dir)
            .and_then(|(cur, lib)| lib.strip_prefix(cur).ok().map(Path::to_path_buf))
    }

    fn preamble(&self, library: &Library) -> Option<Module>;
}

#[derive(Clone, Debug)]
pub struct LibraryDir {
    pub location: PathBuf,
    pub preamble: Option<Module>,
    pub modules_override: Option<Dir<'static>>,
}

impl LibraryDir {
    pub fn builtin<P: Into<PathBuf>>(location: P) -> Self {
        Self::new(location)
            .with_preamble(Module::BUILTIN_TYPES)
            .with_modules(include_dir!("$CARGO_MANIFEST_DIR/../modules/builtin"))
    }
    pub fn stdlib<P: AsRef<Path>>(location: P) -> HashMap<Library, Self> {
        let location = location.as_ref();
        let mut dirs = HashMap::new();
        dirs.insert(
            Library::BUILTIN,
            LibraryDir::builtin(location.join("builtin")),
        );
        dirs.insert(
            Library::LIBC,
            LibraryDir::new(location.join("libc")).with_preamble(Module::LIBC_TYPES),
        );
        dirs.insert(
            Library::CORE,
            LibraryDir::new(location.join("core")).with_preamble(Module::BUILTIN),
        );
        dirs
    }

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
    pub fn with_preamble(mut self, module: Module) -> Self {
        self.preamble = Some(module);
        self
    }
    pub fn with_modules(mut self, modules: Dir<'static>) -> Self {
        self.modules_override = Some(modules);
        self
    }
}

impl Libraries for HashMap<Library, LibraryDir> {
    fn path(&self, library: &Library) -> Result<PathBuf, UnknownModule> {
        self.get(library)
            .map(|e| e.location.clone())
            .ok_or(UnknownModule::UnknownLibrary)
    }
    fn preamble(&self, library: &Library) -> Option<Module> {
        self.get(library).and_then(|e| e.preamble.clone())
    }
}

impl Modules for HashMap<Library, LibraryDir> {
    fn libraries(&self) -> &impl Libraries {
        self
    }
    fn exists(&self, module: &Module) -> Result<(), UnknownModule> {
        match &self
            .get(&module.library)
            .ok_or(UnknownModule::UnknownLibrary)?
            .modules_override
        {
            Some(dir) => dir
                .get_file(module.path_with_extension())
                .map(|_| ())
                .ok_or(UnknownModule::UnknownFile),
            None => <Self as Modules>::path(self, module)
                .and_then(|p| p.is_file().then_some(()).ok_or(UnknownModule::UnknownFile)),
        }
    }
    fn contents(&self, module: &Module) -> Option<String> {
        match &self.get(&module.library)?.modules_override {
            Some(dir) => dir
                .get_file(module.path_with_extension())
                .and_then(File::contents_utf8)
                .map(String::from),
            None => <Self as Modules>::path(self, module)
                .ok()
                .map(fs::read_to_string)
                .and_then(Result::ok),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnknownModule {
    UnknownLibrary,
    UnknownFile,
}
