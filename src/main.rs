use std::{env, fs::read_to_string, path::Path, print, println, process::Command};

use crate::lexer::{Ranged, Token};

mod analyzer;
mod ir;
mod lexer;
mod llvm;
mod parser;
mod vecmap;

fn main() {
    let debug = false;
    let args: Vec<String> = env::args().collect();
    let file = read_to_string(args[1].clone()).unwrap();

    if debug {
        // print extra semicolons
        println!("\n--- SEMICOLONS ---");

        let mut chars = file.chars().enumerate().peekable();

        for tok in lexer::Tokenizer::new(file.as_str()) {
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
    }

    // analyze
    let tokenizer = lexer::Tokenizer::new(file.as_str());
    let (ast, ctx) = parser::parse_ast(tokenizer);
    let asys = analyzer::analyze(&ast, &ctx);

    if debug {
        // print errors
        println!("\n--- ERRORS ---");
        println!("{:#?}", ctx.errors);

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
    } else {
        // TODO: colors
        println!("{}", file);
    }

    // generate ir
    let ir = ir::generate_ir(&ast, &ctx, &asys);
    if debug {
        println!("\n--- IR ---");
        println!("{}", ir.procs);
        println!("\n--- LLVM ---");
    }

    // generate llvm
    llvm::generate_ir(&ir, &Path::new("out.o"), debug);

    // output
    println!("\n--- OUTPUT ---");

    Command::new("./link.sh").status().unwrap();
    Command::new("./out").status().unwrap();
}
