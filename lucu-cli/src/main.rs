use std::path::{Path, PathBuf};
use std::time::Duration;

use asta_annotate::Annotate;
use facet::Facet;
use facet_args as args;
use lucu::annotate::AnnotateExt;
use lucu::error::print::PrintProblems;
use lucu::module::watcher::FileWatcher;
use lucu::module::{Library, LibraryDir, Module};
use lucu::pass::ModuleGraph;
use lucu::type_table::TypeTable;

mod test;

#[derive(Facet)]
struct CheckCommand {
    /// .lucu file with entry point
    #[facet(args::positional)]
    main: PathBuf,
    /// Set the location of the folder that contains the standard libraries
    #[facet(args::named)]
    #[facet(default = AsRef::<Path>::as_ref(&env!("CARGO_MANIFEST_DIR")).join("../modules"))]
    stdlib: PathBuf,
    /// Print compiler output in plaintext, without color
    #[facet(args::named)]
    plaintext: bool,
    /// Print compiler debug info
    #[facet(args::named)]
    debug: bool,
}

#[derive(Facet)]
struct BuildCommand {
    /// .lucu file with entry point
    #[facet(args::positional)]
    main: PathBuf,
    /// Set the file name of the outputted executable, defaults to 'out'
    #[facet(args::named, args::short)]
    #[facet(default = String::from("out"))]
    out: String,

    /// Target architecture triple, defaults to the host architecture
    #[facet(args::named)]
    target: Option<String>,
    /// Target cpu name, defaults to the common denominator for the target architecture
    #[facet(args::named)]
    cpu: Option<String>,
    /// Target cpu features, defaults to the common denominator for the target architecture
    #[facet(args::named)]
    features: Option<String>,

    /// Set the location of the folder that contains the standard libraries
    #[facet(args::named)]
    #[facet(default = AsRef::<Path>::as_ref(&env!("CARGO_MANIFEST_DIR")).join("../modules"))]
    stdlib: PathBuf,
    /// Print compiler output in plaintext, without color
    #[facet(args::named)]
    plaintext: bool,
    /// Print compiler debug info
    #[facet(args::named)]
    debug: bool,
}

#[derive(Facet)]
#[repr(u8)]
enum SubCommand {
    Check(CheckCommand),
    Watch(CheckCommand),
    Build(BuildCommand),
    Run(BuildCommand),
    Test,
}

#[derive(Facet)]
struct Command {
    #[facet(args::subcommand)]
    command: SubCommand,
}

fn main() {
    let c = match args::from_std_args::<Command>() {
        Ok(c) => c,
        Err(a) => {
            match a.help_text() {
                Some(help) => println!("{}", help),
                None => {
                    eprintln!(
                        "{}",
                        args::generate_help::<Command>(&args::HelpConfig::default())
                    )
                }
            }
            return;
        }
    };

    match c.command {
        SubCommand::Check(check_command) => todo!(),
        SubCommand::Watch(check_command) => watch(check_command),
        SubCommand::Build(build_command) => {
            todo!()
        }
        SubCommand::Run(build_command) => {
            todo!()
        }
        SubCommand::Test => {
            test::test();
        }
    }
}

fn watch(cmd: CheckCommand) {
    let mut dirs = LibraryDir::stdlib(cmd.stdlib);
    dirs.insert(
        Library::MAIN,
        LibraryDir::new(cmd.main).with_preamble(Module::BUILTIN),
    );

    let mut watcher = FileWatcher::new(dirs, Duration::from_secs_f32(0.1));

    let mut graph = ModuleGraph::new();
    graph.insert_or_update(watcher.modules(), Module::MAIN);

    let tt = TypeTable::new();

    loop {
        if cmd.debug {
            println!("{}", graph.dot());
        }

        for module in graph.postorder().unwrap() {
            if let Some(stages) = graph.stages(module) {
                if cmd.debug && stages.source().is_some() {
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

                if cmd.debug {
                    println!();
                }
            }
        }
        if cmd.debug {
            tt.eprint_lengths();
        }

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
