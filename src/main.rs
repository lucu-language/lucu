#![feature(let_chains)]

use std::{fs::read_to_string, print, println};

mod analyzer;
mod lexer;
mod parser;

fn main() {
    let file = read_to_string("div.lucu").unwrap();
    let tokenizer = lexer::Tokenizer::new(file.as_str());
    let (ast, ctx) = parser::parse_ast(tokenizer);
    let actx = analyzer::analyze(&ast, &ctx);

    // print errors
    println!("\n--- ERRORS ---");
    println!("{:#?}", ctx.errors);

    // visualize idents
    println!("\n--- SCOPE ANALYSIS ---");

    let mut idents = actx
        .values
        .iter()
        .zip(ctx.idents.iter())
        .collect::<Vec<_>>();
    idents.sort_by_key(|(_, range)| range.1);

    let mut chars = file.chars().enumerate();
    let mut idents = idents.into_iter().peekable();

    while let Some((i, char)) = chars.next() {
        if let Some(id) = idents.peek() && id.1.1 == i {
            // background!
            let mut bg = 100;

            if *id.0 != usize::MAX {
                bg = 41 + (*id.0 % 14);

                if bg >= 48 {
                    bg = 101 + (bg - 48)
                }
            }

            print!("\x1b[{};30m{} {}", bg, id.0, char);

            if id.1.2 != i + 1 {
                while let Some((i, char)) = chars.next() {
                    print!("{}", char);
                    if id.1.2 == i + 1 {
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

    // execute
    println!("\n--- OUTPUT ---");
    todo!();
}
