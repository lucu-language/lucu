use std::{collections::HashMap, iter::Peekable};

use crate::lexer::{Ranged, Token, TokenErr, Tokenizer};

pub type Expr = usize;

#[derive(Debug)]
pub enum Expression {
    Body(Vec<Expr>, Option<Expr>),
    String(String),
    Ident(Path),
    Call(Expr, Vec<Expr>),
    TryWith(Expr, Vec<Handler>),
}

#[derive(Debug)]
pub struct Handler {
    effect: Path,
    functions: HashMap<String, Function>,
}

#[derive(Debug)]
pub struct Path {
    ident: String,
}

#[derive(Debug)]
pub struct Type {
    ident: Path,
}

#[derive(Debug)]
pub struct FunSign {
    inputs: Vec<(String, Type)>,
    effects: Vec<Path>,
}

#[derive(Debug)]
pub struct Function {
    sign: FunSign,
    body: Expr,
}

#[derive(Debug)]
pub struct Effect {
    functions: HashMap<String, FunSign>,
}

#[derive(Debug)]
pub struct AST {
    exprs: Vec<Expression>,
    exprs_pos: Vec<(usize, usize)>,

    effects: HashMap<String, Effect>,
    functions: HashMap<String, Function>,
}

#[derive(Debug)]
pub enum ParseErr {
    Token(TokenErr),
    Unexpected(Token),
}

#[derive(Debug)]
pub struct Parsed<T> {
    result: T,
    errors: Vec<Ranged<ParseErr>>,
}

impl<T> Parsed<T> {
    pub fn new(t: T) -> Self {
        Self {
            result: t,
            errors: Vec::new(),
        }
    }
    pub fn get<U>(self, other: &mut Parsed<U>) -> T {
        other.errors.extend(self.errors);
        self.result
    }
    pub fn err(&mut self, err: Ranged<ParseErr>) {
        self.errors.push(err);
    }
}

type TK<'a> = Peekable<Tokenizer<'a>>;

pub fn parse(tk: Tokenizer) -> Parsed<AST> {
    let mut tk = tk.peekable();
    let mut ast = Parsed::new(AST {
        exprs: Vec::new(),
        exprs_pos: Vec::new(),
        effects: HashMap::new(),
        functions: HashMap::new(),
    });
    loop {
        match tk.peek() {
            // effect
            Some(Ok(Ranged(Token::Effect, ..))) => {
                // TODO
                tk.next();
            }

            // function
            Some(Ok(Ranged(Token::Fun, ..))) => {
                // TODO
                tk.next();
            }

            // unexpected
            Some(Ok(_)) => ast.err(tk.next().unwrap().unwrap().map(ParseErr::Unexpected)),
            Some(Err(_)) => ast.err(tk.next().unwrap().unwrap_err().map(ParseErr::Token)),

            // eof
            None => break ast,
        }
    }
}
