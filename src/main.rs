use std::{collections::HashMap, time::Duration};

use annotate_snippets::{Renderer, renderer::DecorStyle};
use import::ModuleImports;
use include_dir::include_dir;
use module::{Library, Module, ModuleResolver};
use stage::{lexer::Lexer, parser::Parser};
use watcher::{FileWatcher, WatchedLibrary};

mod err;
mod import;
mod module;
mod watcher;

mod stage {
    pub mod lexer;
    pub mod parser;
}

fn main() {
    let mut dirs = HashMap::new();
    dirs.insert(
        Library::BUILTIN,
        WatchedLibrary::new("./modules/builtin").with_modules(include_dir!("modules/builtin")),
    );
    dirs.insert(
        Library::CORE,
        WatchedLibrary::new("./modules/core").with_preamble(Library::BUILTIN, "preamble"),
    );
    dirs.insert(
        Library::MAIN,
        WatchedLibrary::new("./modules/test").with_preamble(Library::CORE, "preamble"),
    );

    let main = Module::new(Library::MAIN, "main");
    let mut watcher = FileWatcher::new(main.clone(), dirs, Duration::from_secs_f32(0.1));

    let renderer = Renderer::styled().decor_style(DecorStyle::Unicode);
    loop {
        let all = ModuleImports::all(&watcher);
        for diagnostic in all.diagnostics {
            diagnostic.print(&watcher, &renderer);
        }
        println!("{:?}", all.value.unwrap());

        watcher.await_change();
    }
}
