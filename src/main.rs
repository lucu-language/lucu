use std::{collections::HashMap, time::Duration};

use annotate_snippets::{Renderer, renderer::DecorStyle};
use import::{ModuleGraph, ModuleScope};
use include_dir::include_dir;
use module::{Library, Module};
use petgraph::graph::NodeIndex;
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
        let graph = ModuleGraph::from(&watcher);
        for diagnostic in graph.diagnostics() {
            diagnostic.print(&watcher, &renderer);
        }

        let graph = graph.value().unwrap();
        println!("{}", graph.dot());

        let scope = ModuleScope::from(graph.ast(NodeIndex::new(0)));
        let scope = scope.value().unwrap();
        println!("{}", scope.dot());

        println!("{:#?}", graph.ast(NodeIndex::new(0)));

        for &def in scope.postorder().value().unwrap() {
            println!("{:?}", def);
        }

        for &node in graph.postorder().value().unwrap() {
            println!("{:?}", graph.module(node));
        }

        watcher.await_change();
    }
}
