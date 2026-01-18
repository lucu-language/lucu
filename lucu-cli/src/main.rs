use std::collections::HashMap;
use std::time::Duration;

use include_dir::include_dir;
use lucu::annotate::AnnotateExt;
use lucu::err::HasProblems;
use lucu::ir::untyped::IR;
use lucu::module::{Library, Module};
use lucu::stage::ModuleGraph;
use lucu::watcher::{FileWatcher, WatchedLibrary};
use lucu_annotate::Annotate;

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

    let mut graph = ModuleGraph::new();
    graph.insert_or_update(&watcher, main.clone());

    loop {
        println!("{}", graph.dot());

        let stages = graph.stages(&main).unwrap();

        let definitions = stages.definitions().unwrap();
        println!("{}", definitions.dot());

        for module in graph.modules() {
            if let Some(stages) = graph.stages(module) {
                let source = stages.source().unwrap();
                let tokens = stages.tokens().unwrap();
                let ast = stages.ast().unwrap();
                let definitions = stages.definitions().unwrap();

                let annotated = source
                    .snippet()
                    .mark_line_numbers()
                    .mark_syntax(tokens)
                    .mark_definition_order(ast, definitions);
                anstream::println!("{}", annotated);

                stages.print_problems2(&watcher);
            }
        }

        let stages = graph.stages(&Module::MAIN).unwrap();
        let mut ir = IR::new();
        let untyped = stages.untyped_ir(&graph, &mut ir).unwrap();
        println!("{}", untyped.display(&ir));

        // wait for changes
        let changes = watcher.await_change();
        for changed in changes {
            if graph.contains(&changed) {
                graph.insert_or_update(&watcher, changed);
            }
        }
        // graph.retain_connected(&main);
    }
}
