use std::collections::HashMap;
use std::time::Duration;

use annotate_snippets::Renderer;
use annotate_snippets::renderer::DecorStyle;
use include_dir::include_dir;
use lucu::annotate::AnnotateExt;
use lucu::err::HasProblems;
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

    let renderer = Renderer::styled().decor_style(DecorStyle::Unicode);

    let mut graph = ModuleGraph::new();
    graph.insert_or_update(&watcher, main.clone());

    loop {
        println!("{}", graph.dot());

        let stages = graph.stages(&main).unwrap();

        {
            let source = stages.source().unwrap();
            let tokens = stages.tokens().unwrap();
            let ast = stages.ast().unwrap();
            let definitions = stages.definitions().unwrap();

            let annotated = source
                .snippet()
                .mark_line_numbers()
                .mark_syntax(tokens)
                .mark_semicolons(tokens)
                .mark_definition_order(ast, definitions);
            anstream::println!("{}", annotated);
        }

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
