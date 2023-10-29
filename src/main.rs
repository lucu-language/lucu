use std::{
    collections::HashMap,
    env,
    ffi::OsStr,
    fs::{read_dir, read_to_string},
    path::{Path, PathBuf},
    println,
    process::Command,
};

use analyzer::{analyze, Analysis};
use clap::Parser;
use error::{Errors, File, FileIdx};
use lexer::Tokenizer;
use parser::{parse_ast, Parsed};

mod analyzer;
mod error;
mod ir;
mod lexer;
mod llvm;
mod parser;
mod vecmap;

fn parse_from_filename(main_file: &Path, core_path: &Path) -> Result<(Parsed, Analysis), Errors> {
    let mut parsed = Parsed::default();
    let mut errors = Errors::new();

    let preamble = core_path.join("preamble.lucu");
    let system = core_path.join("sys/unix"); // TODO: get current system
    let mut files_todo = vec![
        (main_file.to_path_buf(), parsed.main),
        (preamble, parsed.preamble),
        (system, parsed.system),
    ];

    let mut libs = HashMap::new();
    libs.insert("core", core_path);

    let mut n = 0;
    while let Some(&(ref path, pkg)) = files_todo.get(n) {
        n += 1;

        match path.extension() == Some(OsStr::new("lucu")) {
            true => {
                println!("{:?}", path);
                let content = read_to_string(&path).unwrap().replace('\t', "  ");
                let idx = errors.files.push(
                    FileIdx,
                    File {
                        content: content.clone(),
                        name: path.to_string_lossy().into_owned(),
                    },
                );
                let tok = Tokenizer::new(&content, idx, &mut errors);
                parse_ast(
                    tok,
                    pkg,
                    &mut parsed,
                    &path.clone().parent().unwrap(),
                    &libs,
                    &mut files_todo,
                );
            }
            false => match read_dir(&path) {
                Ok(files) => {
                    let iter = files.filter_map(|entry| {
                        // get lucu files
                        let path = entry.ok()?.path();
                        if path.extension() == Some(OsStr::new("lucu")) {
                            Some(path)
                        } else {
                            None
                        }
                    });
                    for path in iter {
                        let content = read_to_string(&path).unwrap().replace('\t', "  ");
                        let idx = errors.files.push(
                            FileIdx,
                            File {
                                content: content.clone(),
                                name: path.to_string_lossy().into_owned(),
                            },
                        );
                        let tok = Tokenizer::new(&content, idx, &mut errors);
                        parse_ast(tok, pkg, &mut parsed, &path.clone(), &libs, &mut files_todo);
                    }
                }
                Err(_) => {}
            },
        }
    }

    let asys = analyze(&parsed, &mut errors);

    if errors.is_empty() {
        Ok((parsed, asys))
    } else {
        Err(errors)
    }
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(help = ".lucu file with entry point")]
    main: PathBuf,
    #[arg(short, long, help = "Set the file name of the outputted executable")]
    out: Option<PathBuf>,

    #[arg(long, help = "Set the location of the core library")]
    core: Option<PathBuf>,
    #[arg(long, help = "Print compiler output in plaintext, without color")]
    plaintext: bool,
    #[arg(long, help = "Print compiler debug info")]
    debug: bool,
}

fn main() {
    let args = Args::parse();
    let core = args.core.unwrap_or_else(|| {
        option_env!("LUCU_CORE")
            .map(PathBuf::from)
            .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("core"))
    });

    let debug = args.debug;
    let color = !args.plaintext;
    let output = args.out.unwrap_or_else(|| PathBuf::from("out"));

    // analyze
    match parse_from_filename(&args.main, &core) {
        Ok((parsed, asys)) => {
            // generate ir
            let ir = ir::generate_ir(&parsed, &asys);
            if debug {
                println!("\n--- IR ---");
                println!("{}", ir);
                println!("\n--- LLVM ---");
            }

            // generate llvm
            llvm::generate_ir(&ir, &output.with_extension("o"), debug);

            // output
            if debug {
                println!("\n--- OUTPUT ---");
            }

            Command::new("ld")
                .arg(&output.with_extension("o"))
                .arg("-o")
                .arg(&output)
                .status()
                .unwrap();

            Command::new(Path::new("./").join(&output))
                .status()
                .unwrap();
        }
        Err(errors) => {
            errors.print(color);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;

    fn execute(filename: &Path, output: &Path) -> String {
        let core = Path::new(env!("CARGO_MANIFEST_DIR")).join("core");

        match parse_from_filename(Path::new(filename), &core) {
            Ok((parsed, asys)) => {
                let ir = ir::generate_ir(&parsed, &asys);
                llvm::generate_ir(&ir, &output.with_extension("o"), false);

                Command::new("ld")
                    .arg(&output.with_extension("o"))
                    .arg("-o")
                    .arg(output)
                    .status()
                    .unwrap();

                let vec = Command::new(output).output().unwrap().stdout;
                String::from_utf8(vec).unwrap()
            }
            Err(errors) => {
                errors.print(false);
                String::from("[ERROR]")
            }
        }
    }

    fn test_file(filename: &str, expected: &str) {
        let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");

        let dir = std::env::temp_dir();
        assert_eq!(
            execute(
                &examples.join(filename).with_extension("lucu"),
                &dir.join(filename)
            ),
            expected
        )
    }

    #[test]
    fn safe_div() {
        test_file("div", "3\n1\n420\n")
    }

    #[test]
    fn hello() {
        test_file("hello", "Hello, World!\n")
    }

    #[test]
    fn implicit_explicit() {
        test_file("implicit", "69\n420\n90\n")
    }

    #[test]
    fn implicit_nonzero() {
        test_file("nonzero", "7\n2\n")
    }

    #[test]
    fn handler_type() {
        test_file("simple_effect", "420\n69\n69\n")
    }

    #[test]
    fn fail_union() {
        test_file("yeet", "42\nHello, World!\n")
    }

    #[test]
    fn naked_vs_nonnaked() {
        test_file("naked", "5\n5\nreachable\n69\n")
    }

    #[test]
    fn mutation_outside() {
        test_file("setter", "69\n420\n24\n42\n")
    }

    #[test]
    fn mutation_inside() {
        test_file("counter", "5\n6\n7\n")
    }

    #[test]
    fn effect_function_handlers() {
        test_file("printget", "onetwotea")
    }

    #[test]
    fn arrays() {
        test_file("strbuffer", "Hello\nworld\nworld\nHello\n")
    }
}
