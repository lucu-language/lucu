use std::time::Duration;

use asta_annotate::Annotate;
use lucu::annotate::AnnotateExt;
use lucu::error::print::PrintProblems;
use lucu::module::watcher::FileWatcher;
use lucu::module::{Library, LibraryDir, Module};
use lucu::pass::ModuleGraph;
use lucu::type_table::TypeTable;

fn main() {
    let mut dirs = LibraryDir::stdlib("./modules");
    dirs.insert(
        Library::MAIN,
        LibraryDir::new("./test").with_preamble(Module::CORE),
    );

    let mut watcher = FileWatcher::new(dirs, Duration::from_secs_f32(0.1));

    let mut graph = ModuleGraph::new();
    graph.insert_or_update(watcher.modules(), Module::MAIN);

    let tt = TypeTable::new();

    loop {
        println!("{}", graph.dot());

        for module in graph.postorder().unwrap() {
            if let Some(stages) = graph.stages(module) {
                if stages.source().is_some() {
                    let source = stages.source().unwrap();
                    let tokens = stages.tokens().unwrap();
                    let ast = stages.ast().unwrap();

                    // let annotated = source.snippet().mark_line_numbers().mark_syntax(tokens);

                    // if let Some(definitions) = stages.definitions() {
                    //     anstream::println!("{}", annotated.mark_definition_order(ast, definitions));
                    // } else {
                    //     anstream::println!("{}", annotated);
                    // }

                    anstream::println!(
                        "{}",
                        source
                            .snippet()
                            .mark_ast(ast)
                            // .debug()
                            .mark_line_numbers()
                            .mark_syntax(tokens)
                    );

                    if let Some(header) = stages.header(&graph, &tt) {
                        println!("{}", header.display(&tt));
                    }
                }

                stages.print_problems(watcher.modules(), true);
                println!();
            }
        }
        tt.eprint_lengths();

        // wait for changes
        let changes = watcher.await_change();
        for changed in changes {
            if graph.contains(&changed) {
                graph.insert_or_update(watcher.modules(), changed);
            }
        }
        // graph.retain_connected(&Module::MAIN);
    }
}
