#![cfg(feature = "watcher")]

use std::collections::{HashMap, HashSet};
use std::time::Duration;

use crossbeam_channel::{Receiver, unbounded};
use notify_debouncer_full::notify::{RecommendedWatcher, RecursiveMode};
use notify_debouncer_full::{DebounceEventResult, Debouncer, RecommendedCache, new_debouncer};

use crate::module::{Library, LibraryDir, Module, Modules};

pub struct FileWatcher {
    libraries: HashMap<Library, LibraryDir>,

    rx: Receiver<DebounceEventResult>,
    #[expect(unused)]
    file_watcher: Debouncer<RecommendedWatcher, RecommendedCache>,
}

impl FileWatcher {
    pub fn new(libraries: HashMap<Library, LibraryDir>, timeout: Duration) -> Self {
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
    pub fn modules(&self) -> &impl Modules {
        &self.libraries
    }
}
