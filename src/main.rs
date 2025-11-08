use std::{collections::HashMap, time::Duration};

use annotate_snippets::{Renderer, renderer::DecorStyle};
use err::HasProblems;
use include_dir::include_dir;
use module::{Library, Module};
use stage::ModuleGraph;
use watcher::{FileWatcher, WatchedLibrary};

mod err;
mod module;
mod span;
mod stage;
mod watcher;

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

    let mut graph = ModuleGraph::new();
    graph.insert_or_update(&watcher, main.clone());

    loop {
        println!("{}", graph.dot());

        let stages = graph.stages(&main).unwrap();
        let definitions = stages.definitions().unwrap();
        println!("{}", definitions.dot());

        stages.print_problems(&watcher, &renderer);

        // wait for changes
        let changes = watcher.await_change();
        for changed in changes {
            if graph.contains(&changed) {
                graph.insert_or_update(&watcher, changed);
            }
        }
        graph.retain_connected(&main);
    }
}
