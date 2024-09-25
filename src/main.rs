use lexer::tokenize;
use parser::parse;

pub mod lexer;
pub mod parser;

fn main() {
    let src = include_str!("../core/preamble.lucu");

    let tokens = tokenize(src).collect::<Box<[_]>>();
    tokens.iter().for_each(|t| println!("{:?}", t.token));

    let nodes = parse(&tokens);

    println!("{:?}", nodes);

    let out = std::fs::File::create("out.graphviz").unwrap();
    nodes.graphviz(src, out).unwrap();
}
