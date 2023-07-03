use std::{env, fs::read_to_string, print, println};

use crate::lexer::{Ranged, Token};

mod analyzer;
mod lexer;
mod parser;
mod vm;

fn main() {
    let args: Vec<String> = env::args().collect();
    let file = read_to_string(args[1].clone()).unwrap();

    // print extra semicolons
    println!("\n--- SEMICOLONS ---");

    let mut chars = file.chars().enumerate().peekable();

    for tok in lexer::Tokenizer::new(file.as_str()) {
        let start = match tok {
            Ok(Ranged(_, start, _)) => start,
            Err(Ranged(_, start, _)) => start,
        };

        // print until start
        while let Some(char) = chars.peek().filter(|&(i, _)| *i < start).map(|&(_, c)| c) {
            chars.next();
            print!("{}", char);
        }

        // print extra semicolon
        if matches!(tok, Ok(Ranged(Token::Semicolon, ..)))
            && !chars.peek().is_some_and(|&(_, c)| c == ';')
        {
            print!("\x1b[7m;\x1b[0m");
        }
    }

    // print remaining
    for char in chars.map(|(_, c)| c) {
        print!("{}", char);
    }

    // compile
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
        if let Some(id) = idents.peek().filter(|id| id.1 .1 == i) {
            // background!
            let mut bg = 100;

            if *id.0 != usize::MAX {
                bg = 41 + (*id.0 % 14);

                if bg >= 48 {
                    bg = 101 + (bg - 48)
                }
            }

            print!("\x1b[{};30m{} {}", bg, id.0, char);

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

    // VM test
    println!("\n--- VM TEST ---");
    let main = vm::Chunk {
        bytecode: Box::new([
            vm::Opcode::ResetRel as u8,
            1, // jmp
            vm::Opcode::Print as u8,
            vm::Opcode::Halt as u8,
        ]),
        constants: Box::new([]),
    };

    let foo = vm::Chunk {
        bytecode: Box::new([
            vm::Opcode::PushRel as u8,
            1, // from stack
            vm::Opcode::ShiftRel as u8,
            1, // jmp
            vm::Opcode::Push as u8,
            0, // constant
            vm::Opcode::Add as u8,
            vm::Opcode::ReturnVal as u8,
        ]),
        constants: Box::new([vm::Value::Int(2)]),
    };

    let bar = vm::Chunk {
        bytecode: Box::new([
            vm::Opcode::Pop as u8,
            vm::Opcode::Push as u8,
            0, // consyant
            vm::Opcode::ReturnVal as u8,
        ]),
        constants: Box::new([vm::Value::Int(3)]),
    };

    let mut vm = vm::VM::new(Box::new([main, foo, bar]));

    while !vm.halted() {
        vm.dump();
        vm.next_instruction();
    }

    // execute
    println!("\n--- OUTPUT ---");
    todo!();
}
