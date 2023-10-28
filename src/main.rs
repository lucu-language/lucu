#![feature(test)]

extern crate test;

use std::{
    collections::HashMap,
    env,
    ffi::OsStr,
    fs::{read_dir, read_to_string},
    path::Path,
    println,
    process::Command,
};

use analyzer::{analyze, Analysis};
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
                let content = read_to_string(&path).unwrap();
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
                        let content = read_to_string(&path).unwrap();
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
                Err(_) => {
                    // TODO: error
                    panic!();
                }
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

fn main() {
    let debug = true;
    let color = true;
    let args: Vec<String> = env::args().collect();

    // analyze
    match parse_from_filename(Path::new(&args[1]), Path::new("core")) {
        Ok((parsed, asys)) => {
            // generate ir
            let ir = ir::generate_ir(&parsed, &asys);
            if debug {
                println!("\n--- IR ---");
                println!("{}", ir);
                println!("\n--- LLVM ---");
            }

            // generate llvm
            llvm::generate_ir(&ir, &Path::new("out.o"), debug);

            // output
            if debug {
                println!("\n--- OUTPUT ---");
            }

            Command::new("./link.sh").arg("out").status().unwrap();
            Command::new("./out").status().unwrap();
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

    fn execute(filename: &str, output: &str) -> String {
        match parse_from_filename(Path::new(filename), Path::new("core")) {
            Ok((parsed, asys)) => {
                let ir = ir::generate_ir(&parsed, &asys);
                llvm::generate_ir(&ir, &Path::new(&format!("{}.o", output)), false);

                Command::new("./link.sh").arg(output).status().unwrap();

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
        assert_eq!(
            execute(
                &format!("./examples/{}.lucu", filename),
                &format!("./examples/{}", filename)
            ),
            expected
        )
    }

    #[test]
    fn safe_div() {
        test_file("div", "3\n1\n420\n")
    }

    #[test]
    fn imports() {
        test_file("factorial", "12\n479001600\n144\n")
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
