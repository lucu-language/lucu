use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
    time::Duration,
};

use crossbeam_channel::{Receiver, unbounded};
use notify_debouncer_full::{
    DebounceEventResult, Debouncer, RecommendedCache, new_debouncer,
    notify::{RecommendedWatcher, RecursiveMode},
};
use pathdiff::diff_paths;

use crate::module::{Library, LibraryDir, Module, UnknownModule};

pub trait ModuleReader {
    fn main(&self) -> Module;
    fn preamble(&mut self, pkg: &Module) -> Option<Module>;
    fn contents(&mut self, pkg: &Module) -> Result<String, UnknownModule>;
}

pub struct FileWatcher {
    main: Module,
    watched_modules: HashSet<Module>,
    libraries: HashMap<Library, LibraryDir>,

    rx: Receiver<DebounceEventResult>,
    file_watcher: Debouncer<RecommendedWatcher, RecommendedCache>,
}

impl FileWatcher {
    pub fn new(main: Module, libraries: HashMap<Library, LibraryDir>) -> Self {
        let (tx, rx) = unbounded();
        let mut file_watcher = new_debouncer(Duration::from_secs_f64(0.1), None, tx).unwrap();
        for lib in libraries.values() {
            if lib.modules_override.is_none() {
                file_watcher
                    .watch(&lib.location, RecursiveMode::Recursive)
                    .unwrap();
            }
        }
        Self {
            main,
            watched_modules: HashSet::new(),
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
                        let path = diff_paths(path, &lib_path.location).expect(
                            "ICE: could not get the difference between module and library path",
                        );
                        let module = Module::new(lib.clone(), path);
                        if self.watched_modules.contains(&module) {
                            eprintln!("{} changed!", module);
                            changed.insert(module);
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

impl ModuleReader for FileWatcher {
    fn main(&self) -> Module {
        self.main.clone()
    }
    fn preamble(&mut self, module: &Module) -> Option<Module> {
        self.libraries
            .get(&module.library)
            .and_then(|lp| lp.preamble.clone())
    }
    fn contents(&mut self, module: &Module) -> Result<String, UnknownModule> {
        let full_path = self
            .library_path(&module.library)?
            .join(module.path_with_extension());

        if !self.watched_modules.contains(module) {
            self.watched_modules.insert(module.clone());
        }

        std::fs::read_to_string(&full_path).map_err(|_| UnknownModule::UnknownFile(full_path))
    }
}
