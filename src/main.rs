use std::fs::read_to_string;

use lexer::Tokenizer;

// mod analyzer;
mod lexer;
// mod parser;

fn main() {
    let file = read_to_string("example.lucu").unwrap();
    let tokenizer = Tokenizer::new(file.as_str());
    let tokens: Result<Vec<_>, ()> = tokenizer.collect();
    println!("{:?}", tokens);
}
