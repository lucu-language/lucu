use std::collections::HashMap;
use std::time::Duration;

use include_dir::include_dir;
use lucu::annotate::AnnotateExt;
use lucu::error::print::PrintProblems;
use lucu::module::watcher::{FileWatcher, WatchedLibrary};
use lucu::module::{Library, Module};
use lucu::pass::ModuleGraph;
use lucu::type_table::TypeTable;
use lucu_annotate::Annotate;

fn main() {
    let mut dirs = HashMap::new();
    dirs.insert(
        Library::BUILTIN,
        WatchedLibrary::new("./modules/builtin")
            .with_modules(include_dir!("modules/builtin"))
            .with_preamble(Module::BUILTIN_PREAMBLE),
    );
    dirs.insert(
        Library::CORE,
        WatchedLibrary::new("./modules/core").with_preamble(Module::BUILTIN_PREAMBLE),
    );
    dirs.insert(
        Library::MAIN,
        WatchedLibrary::new("./modules/test").with_preamble(Module::CORE_PREAMBLE),
    );

    let main = Module::new(Library::MAIN, "main");
    let mut watcher = FileWatcher::new(main.clone(), dirs, Duration::from_secs_f32(0.1));

    let mut graph = ModuleGraph::new();
    graph.insert_or_update(&watcher, main.clone());

    let mut tt = TypeTable::new();

    loop {
        println!("{}", graph.dot());

        for module in graph.modules() {
            if let Some(stages) = graph.stages(module) {
                let source = stages.source().unwrap();
                let tokens = stages.tokens().unwrap();
                let ast = stages.ast().unwrap();

                let annotated = source.snippet().mark_line_numbers().mark_syntax(tokens);

                if let Some(definitions) = stages.definitions() {
                    anstream::println!("{}", annotated.mark_definition_order(ast, definitions));
                } else {
                    anstream::println!("{}", annotated);
                }

                if let Some(untyped) = stages.untyped_ir(&graph, &mut tt) {
                    println!("{}", untyped.display(&tt));
                }

                stages.print_problems(&watcher, true);
                println!();
            }
        }

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
