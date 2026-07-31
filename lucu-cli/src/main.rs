use std::path::{Path, PathBuf};
use std::time::Duration;

use asta_handle_map::HandleSet;
use facet::Facet;
use facet_args as args;
use inkwell::OptimizationLevel;
use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::context::Context;
use inkwell::targets::{InitializationConfig, Target, TargetMachine, TargetMachineOptions};
use lucu::error::HasProblems;
use lucu::error::print::PrintProblems;
use lucu::module::watcher::FileWatcher;
use lucu::module::{Library, LibraryDir, Module};
use lucu::mu;
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

    let modules = HandleSet::<Module>::new();
    let mut graph = ModuleGraph::new();
    graph.insert_or_update(watcher.modules(), const { &Module::MAIN }, |m| {
        modules.intern_cloned(m)
    });

    let tt = TypeTable::new();
    let mu_tt = unsafe { mu::table::TypeTable::new() };
    let mu_et = unsafe { mu::table::ExpressionTable::new() };

    loop {
        if cmd.debug {
            println!("---");
            println!("{}", graph.dot());
        }

        let mut functions = Vec::new();
        for module in graph.postorder().unwrap() {
            if let Some(stages) = graph.stages(module) {
                if cmd.debug
                    && stages.source().is_some()
                    && let Some(header) = stages.header(&graph, &tt)
                {
                    println!("{}", header.display(&tt));
                }

                if let Some(mu) = stages.mu(&graph, &tt, &mu_tt, &mu_et) {
                    functions.extend(mu.functions.iter().cloned())
                }

                stages.print_problems(watcher.modules(), &tt, false);

                if cmd.debug {
                    println!();
                }
            }
        }
        if cmd.debug {
            tt.eprint_lengths();
        }

        if cmd.debug && !graph.problems().next().is_some() {
            // owo no problems
            // COMPILE
            Target::initialize_native(&InitializationConfig::default()).unwrap();

            let triple = TargetMachine::get_default_triple();
            let machine = Target::from_triple(&triple)
                .unwrap()
                .create_target_machine_from_options(
                    &triple,
                    TargetMachineOptions::new().set_level(OptimizationLevel::Aggressive),
                )
                .unwrap();

            let context = Context::create();
            let llvm =
                lucu_llvm::Builder::build(&context, &mu_tt, &mu_et, machine, "main", &functions);

            if let Some(fun) = llvm.module.get_function("_start") {
                fun.add_attribute(
                    AttributeLoc::Function,
                    context.create_enum_attribute(Attribute::get_named_enum_kind_id("noreturn"), 0),
                );
                fun.add_attribute(
                    AttributeLoc::Function,
                    context.create_string_attribute("stackrealign", ""),
                );
                fun.add_attribute(
                    AttributeLoc::Function,
                    context.create_enum_attribute(Attribute::get_named_enum_kind_id("naked"), 0),
                );
            }

            llvm.build_functions_that_llvm_tries_to_call_for_some_reason();

            // eprintln!(" --- LLVM --- ");
            // llvm.eprint();
            llvm.verify().unwrap();
            llvm.optimize().unwrap();
            // eprintln!(" --- LLVM O3 --- ");
            // llvm.eprint();

            llvm.write_asm(Path::new("out.asm")).unwrap();
            llvm.write_object(Path::new("out.o")).unwrap();
            std::process::Command::new("ld")
                .arg("out.o")
                .arg("-o")
                .arg("out")
                .arg("-e_start")
                .status()
                .unwrap();

            eprintln!("COMPILED");
        }

        // wait for changes
        let changes = watcher.await_change();
        for changed in changes {
            if graph.contains(&changed) {
                graph.insert_or_update(watcher.modules(), modules.intern(changed), |m| {
                    modules.intern_cloned(m)
                });
            }
        }
        graph.retain_connected(&Module::MAIN);
    }
}
