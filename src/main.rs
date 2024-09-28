use lexer::tokenize;
use parser::parse;

use crate::untyped_ir::codegen;

pub mod lexer;
pub mod parser;
pub mod untyped_ir;

fn main() {
    unsafe { backtrace_on_stack_overflow::enable() };

    let src = include_str!("../core/preamble/internal.lucu");

    let tokens = tokenize(src).collect::<Box<[_]>>();
    let (nodes, errors) = parse(&tokens);
    let file = codegen(&nodes, src);

    println!("{:?}", errors);
    println!("{}", file);

    let out = std::fs::File::create("out.graphviz").unwrap();
    nodes.graphviz(src, out).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests if we can parse array types []T in an expression.
    #[test]
    fn parse_array_type() {
        let src = include_str!("../test/parse_array.lucu");

        let tokens = tokenize(src).collect::<Box<[_]>>();
        let (_, errors) = parse(&tokens);

        assert_eq!(errors.len(), 0, "errors while parsing: {:?}", errors);
    }
}
