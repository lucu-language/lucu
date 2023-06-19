use std::fs::read_to_string;

use lexer::Tokenizer;

use crate::parser::{Parse, AST};

// mod analyzer;
mod lexer;
mod parser;

fn main() {
    let file = read_to_string("example.lucu").unwrap();
    let tokenizer = Tokenizer::new(file.as_str());
    let tokens: Result<Vec<_>, _> = tokenizer.collect();
    println!("{:#?}\n", tokens);

    let mut tokenizer = Tokenizer::new(file.as_str()).peekable();
    let mut errors = Vec::new();
    let ast = AST::parse(&mut tokenizer, &mut errors);
    println!("{:#?}\n", ast);
}
