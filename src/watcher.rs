use std::{
    collections::{HashMap, HashSet},
    ffi::OsString,
    path::PathBuf,
    sync::{Arc, Mutex},
    time::Duration,
};

use crossbeam_channel::{Receiver, unbounded};
use notify_debouncer_full::{
    DebounceEventResult, Debouncer, RecommendedCache, new_debouncer,
    notify::{
        EventKind, RecommendedWatcher, RecursiveMode,
        event::{ModifyKind, RenameMode},
    },
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
    file_watcher: Arc<Mutex<Debouncer<RecommendedWatcher, RecommendedCache>>>,
    parent_watchers: HashMap<PathBuf, HashSet<OsString>>,
}

impl FileWatcher {
    pub fn new(main: Module, libraries: HashMap<Library, LibraryDir>) -> Self {
        let (tx, rx) = unbounded();
        Self {
            main,
            watched_modules: HashSet::new(),
            libraries,
            rx,
            file_watcher: Arc::new(Mutex::new(
                new_debouncer(Duration::from_secs_f64(0.1), None, tx).unwrap(),
            )),
            parent_watchers: HashMap::new(),
        }
    }
    pub fn await_change(&mut self) -> HashSet<Module> {
        let mut changed = HashSet::new();
        while changed.is_empty() {
            for event in self.rx.recv().unwrap().unwrap() {
                if event.kind.is_access() || event.kind.is_other() {
                    continue;
                }

                // Check for removed files,
                // possibly add a watch on the parent directory.
                if matches!(
                    event.kind,
                    EventKind::Remove(_)
                        | EventKind::Modify(ModifyKind::Name(RenameMode::Both | RenameMode::From))
                ) {
                    let path = event
                        .paths
                        .first()
                        .expect("ICE: file event does not have a path");

                    if !path.exists() && self.parent_watchers.contains_key(path) {
                        eprintln!("{} removed!", path.display());

                        let name = path
                            .file_name()
                            .expect("ICE: removed file has no filename")
                            .to_os_string();
                        let parent = path
                            .parent()
                            .expect("ICE: removed file has no parent directory")
                            .to_path_buf();

                        self.file_watcher
                            .lock()
                            .unwrap()
                            .watch(&parent, RecursiveMode::NonRecursive)
                            .unwrap();

                        let mut set = HashSet::new();
                        set.insert(name);
                        self.parent_watchers.insert(parent, set);
                    }
                }

                // Check for newly created files,
                // possibly remove the watch on the parent directory.
                if matches!(
                    event.kind,
                    EventKind::Create(_)
                        | EventKind::Modify(ModifyKind::Name(RenameMode::Both | RenameMode::To))
                ) {
                    let path = event
                        .paths
                        .last()
                        .expect("ICE: file event does not have a path");

                    let name = path.file_name().expect("ICE: created file has no filename");
                    let parent = path
                        .parent()
                        .expect("ICE: created file has no parent directory");

                    let matches = self
                        .parent_watchers
                        .get_mut(parent)
                        .is_some_and(|s| s.remove(name));

                    if matches {
                        eprintln!("{} created!", path.display());

                        let mut watcher = self.file_watcher.lock().unwrap();
                        watcher.watch(path, RecursiveMode::NonRecursive).unwrap();

                        if self.parent_watchers[parent].is_empty() {
                            self.parent_watchers.remove(parent);
                            watcher.unwatch(parent).unwrap();
                        } else {
                            watcher.watch(parent, RecursiveMode::NonRecursive).unwrap();
                        }
                    }
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

        // re-apply watchers for changed modules
        for module in &changed {
            let full_path = self
                .library_path(&module.library)
                .expect("ICE: cannot get library path of watched module")
                .join(module.path_with_extension());
            self.watch_file(full_path);
        }

        changed
    }
    fn watch_file(&mut self, mut path: PathBuf) {
        while !path.exists() {
            let name = path
                .file_name()
                .expect("ICE: tried watching a file without a filename")
                .to_os_string();
            path.pop();
            self.parent_watchers
                .entry(path.clone())
                .or_default()
                .insert(name);
        }

        let watcher = &mut *self.file_watcher.lock().unwrap();
        watcher.watch(path, RecursiveMode::NonRecursive).unwrap();
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
            self.watch_file(full_path.clone());
            self.watched_modules.insert(module.clone());
        }

        std::fs::read_to_string(&full_path).map_err(|_| UnknownModule::UnknownFile(full_path))
    }
}
