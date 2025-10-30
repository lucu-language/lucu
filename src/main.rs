use std::collections::HashMap;

use include_dir::include_dir;
use module::{Library, LibraryDir, Module};
use watcher::{FileWatcher, ModuleReader};

mod module;
mod watcher;

fn main() {
    let mut dirs = HashMap::new();
    dirs.insert(
        Library::BUILTIN,
        LibraryDir::new("./modules/builtin").with_modules(include_dir!("modules/builtin")),
    );
    dirs.insert(
        Library::CORE,
        LibraryDir::new("./modules/core").with_preamble(Library::BUILTIN, "preamble"),
    );
    dirs.insert(
        Library::MAIN,
        LibraryDir::new("./modules/test").with_preamble(Library::CORE, "preamble"),
    );

    let main = Module::new(Library::MAIN, "main");
    let mut watcher = FileWatcher::new(main.clone(), dirs);

    loop {
        println!("{:?}", watcher.contents(&main));
        watcher.await_change();
    }
}
