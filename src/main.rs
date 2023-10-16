#![feature(test)]

extern crate test;

use std::{env, fs::read_to_string, path::Path, print, println, process::Command};

use crate::{error::Ranged, lexer::Token};

mod analyzer;
mod error;
mod ir;
mod lexer;
mod llvm;
mod parser;
mod vecmap;

fn main() {
    let mut errors = error::Errors::new();

    let debug = true;
    let args: Vec<String> = env::args().collect();
    let file = read_to_string(args[1].clone()).unwrap().replace('\t', "  ");

    if debug {
        // print extra semicolons
        println!("\n--- SEMICOLONS ---");

        let mut chars = file.chars().enumerate().peekable();

        for tok in lexer::Tokenizer::new(file.as_str(), &mut error::Errors::new()) {
            let start = tok.1;

            // print until start
            while let Some(char) = chars.peek().filter(|&(i, _)| *i < start).map(|&(_, c)| c) {
                chars.next();
                print!("{}", char);
            }

            // print extra semicolon
            if matches!(tok, Ranged(Token::Semicolon, ..))
                && !chars.peek().is_some_and(|&(_, c)| c == ';')
            {
                print!("\x1b[7m;\x1b[0m");
            }
        }

        // print remaining
        for char in chars.map(|(_, c)| c) {
            print!("{}", char);
        }
        println!();
    }

    // analyze
    let tokenizer = lexer::Tokenizer::new(file.as_str(), &mut errors);
    let (ast, ctx) = parser::parse_ast(tokenizer);
    let asys = analyzer::analyze(&ast, &ctx, &mut errors);

    if debug {
        // visualize idents
        println!("\n--- SCOPE ANALYSIS ---");

        let mut idents = asys
            .values
            .values()
            .zip(ctx.idents.values())
            .collect::<Vec<_>>();
        idents.sort_by_key(|(_, range)| range.1);

        let mut chars = file.chars().enumerate();
        let mut idents = idents.into_iter().peekable();

        while let Some((i, char)) = chars.next() {
            if let Some(id) = idents.peek().filter(|id| id.1 .1 == i) {
                // background!
                let mut bg = 100;

                let num = usize::from(*id.0);
                if num != usize::MAX {
                    bg = 41 + (num % 14);

                    if bg >= 48 {
                        bg = 101 + (bg - 48)
                    }
                }

                print!("\x1b[{};30m{} {}", bg, num, char);

                if id.1 .2 != i + 1 {
                    while let Some((i, char)) = chars.next() {
                        print!("{}", char);
                        if id.1 .2 == i + 1 {
                            break;
                        }
                    }
                }

                print!("\x1b[0m");
                idents.next();
            } else {
                print!("{}", char);
            }
        }
        println!();
    }

    // print errors
    if !errors.is_empty() {
        println!();
        errors.print(file.as_str(), &args[1], true);
        return;
    }

    // generate ir
    let ir = ir::generate_ir(&ast, &ctx, &asys);
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

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;

    fn execute(filename: &str, output: &str) -> String {
        let file = read_to_string(filename).unwrap().replace('\t', "  ");

        let mut errors = error::Errors::new();

        let tokenizer = lexer::Tokenizer::new(&file, &mut errors);
        let (ast, ctx) = parser::parse_ast(tokenizer);
        let asys = analyzer::analyze(&ast, &ctx, &mut errors);

        if !errors.is_empty() {
            println!();
            errors.print(&file, filename, true);
            return "[ERROR]".into();
        }

        let ir = ir::generate_ir(&ast, &ctx, &asys);
        llvm::generate_ir(&ir, &Path::new(&format!("{}.o", output)), false);

        Command::new("./link.sh").arg(output).status().unwrap();

        let vec = Command::new(output).output().unwrap().stdout;
        String::from_utf8(vec).unwrap()
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
    fn test_div() {
        test_file("div", "3\n1\n420\n")
    }

    #[test]
    fn test_factorial() {
        test_file("factorial", "12\n479001600\n")
    }

    #[test]
    fn test_hello() {
        test_file("hello", "Hello, World!\n")
    }

    #[test]
    fn test_implicit() {
        test_file("implicit", "69\n420\n90\n")
    }

    #[test]
    fn test_nonzero() {
        test_file("nonzero", "7\n2\n")
    }

    #[test]
    fn test_simple_effect() {
        test_file("simple_effect", "420\n69\n69\n")
    }

    #[test]
    fn test_yeet() {
        test_file("yeet", "42\nHello, World!\n")
    }
}
