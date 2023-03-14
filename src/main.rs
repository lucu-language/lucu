#![feature(is_some_and)]

use std::fs::read_to_string;

mod lexer;
mod parser;

fn main() {
    let str = read_to_string("example.lucu").unwrap();
    let tok = lexer::tokenize(str.as_str());
    println!("{}", tok);
    let ast = parser::parse(str.as_str(), tok).unwrap();
    println!("{:?}", ast);
}
