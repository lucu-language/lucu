use std::collections::{HashMap, HashSet};
use std::env;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crossbeam_channel::{Receiver, unbounded};
use include_dir::Dir;
use notify_debouncer_full::notify::{RecommendedWatcher, RecursiveMode};
use notify_debouncer_full::{DebounceEventResult, Debouncer, RecommendedCache, new_debouncer};
use path_clean::PathClean;

use crate::module::{Library, Module, ModuleResolver, UnknownModule};

pub struct FileWatcher {
    main: Module,
    libraries: HashMap<Library, WatchedLibrary>,

    rx: Receiver<DebounceEventResult>,
    #[expect(unused)]
    file_watcher: Debouncer<RecommendedWatcher, RecommendedCache>,
}

#[derive(Clone)]
pub struct WatchedLibrary {
    pub location: PathBuf,
    pub preamble: Option<Module>,
    pub modules_override: Option<Dir<'static>>,
}

impl WatchedLibrary {
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

impl FileWatcher {
    pub fn new(
        main: Module,
        libraries: HashMap<Library, WatchedLibrary>,
        timeout: Duration,
    ) -> Self {
        let (tx, rx) = unbounded();
        let mut file_watcher = new_debouncer(timeout, None, tx).unwrap();
        for lib in libraries.values() {
            if lib.modules_override.is_none() {
                file_watcher
                    .watch(&lib.location, RecursiveMode::Recursive)
                    .unwrap();
            }
        }
        Self {
            main,
            libraries,
            rx,
            file_watcher,
        }
    }
    pub fn await_change(&mut self) -> HashSet<Module> {
        let mut changed = HashSet::new();
        while changed.is_empty() {
            for event in self.rx.recv().unwrap().unwrap() {
                if event.kind.is_access() || event.kind.is_other() {
                    continue;
                }

                // Check for modified files
                for path in &event.paths {
                    for (lib, lib_path) in self.libraries.iter() {
                        if let Ok(relative) = path.strip_prefix(&lib_path.location) {
                            changed.insert(Module::new(lib.clone(), relative));
                        }
                    }
                }
            }
        }
        changed
    }
    fn library_path(&self, lib: &Library) -> Result<&PathBuf, UnknownModule> {
        self.libraries
            .get(lib)
            .map(|e| &e.location)
            .ok_or_else(|| UnknownModule::UnknownLibrary(lib.clone()))
    }
}

impl ModuleResolver for FileWatcher {
    fn main(&self) -> Module {
        self.main.clone()
    }
    fn preamble(&self, module: &Module) -> Option<Module> {
        self.libraries
            .get(&module.library)
            .and_then(|lp| lp.preamble.clone())
    }
    fn readable_path(&self, module: &Module) -> String {
        let current_dir = env::current_dir().ok();
        let library_dir = self.library_path(&module.library).ok();
        let relative_dir =
            Option::zip(current_dir, library_dir).and_then(|(cur, lib)| lib.strip_prefix(cur).ok());

        match relative_dir {
            Some(dir) => dir
                .join(module.path_with_extension())
                .to_string_lossy()
                .into_owned(),
            None => module.to_string(),
        }
    }
    fn contents(&self, module: &Module) -> Option<String> {
        self.library_path(&module.library)
            .ok()
            .map(|lib| lib.join(module.path_with_extension()))
            .and_then(|path| std::fs::read_to_string(path).ok())
    }
    fn exists(&self, module: &Module) -> Result<(), UnknownModule> {
        let full_path = self
            .library_path(&module.library)?
            .join(module.path_with_extension());
        full_path.is_file().then_some(()).ok_or_else(|| {
            let current_dir = env::current_dir().ok();
            let relative_dir = current_dir.and_then(|cur| full_path.strip_prefix(cur).ok());
            UnknownModule::UnknownFile(relative_dir.map(Path::to_path_buf).unwrap_or(full_path))
        })
    }
}
