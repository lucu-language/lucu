use std::{collections::HashMap, iter::Peekable};

use crate::lexer::{Group, Ranged, Token, TokenErr, Tokenizer};

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
    name: Ranged<String>,
    sign: FunSign,
    body: Expr,
}

#[derive(Debug)]
pub struct Effect {
    name: Ranged<String>,
    functions: HashMap<String, FunSign>,
}

#[derive(Debug)]
pub struct AST {
    exprs: Vec<Ranged<Expression>>,

    effects: HashMap<String, Effect>,
    functions: HashMap<String, Function>,
}

#[derive(Debug)]
pub enum ParseErr {
    Token(TokenErr),
    Unexpected(Token),
    UnexpectedEOF,
    Unclosed(Group),
}

type Tokens<'a> = Peekable<Tokenizer<'a>>;
type Errors = Vec<Ranged<ParseErr>>;

pub trait Parse: Sized {
    fn parse(tk: &mut Tokens, errors: &mut Errors) -> Option<Self>;
    fn is_statement_end(t: &Token) -> bool;

    // parse, and if it could not be parsed, skip to statement end
    fn parse_catch(tk: &mut Tokens, errors: &mut Errors) -> Option<Self> {
        match Self::parse(tk, errors) {
            Some(s) => Some(s),
            None => loop {
                match tk.next() {
                    Some(Ok(Ranged(Token::Open(g), ..))) => {
                        // skip until closed
                        tk.skip_close(g)?;

                        // is this close token the end?
                        if Self::is_statement_end(&Token::Close(g)) {
                            break None;
                        }
                    }
                    Some(Ok(t)) if Self::is_statement_end(&t.0) => break None,
                    None => break None,
                    _ => {}
                }
            },
        }
    }
}

pub trait TokenIter: Iterator<Item = Result<Ranged<Token>, Ranged<TokenErr>>> {
    fn expect(&mut self, token: Token, errors: &mut Errors) -> Option<Ranged<()>> {
        let err = match self.next() {
            Some(Ok(t)) if t.0 == token => return Some(t.map(|_| ())),
            Some(Ok(t)) => t.map(ParseErr::Unexpected),
            Some(Err(e)) => e.map(ParseErr::Token),
            None => Ranged(ParseErr::UnexpectedEOF, usize::MAX, usize::MAX),
        };
        errors.push(err);
        None
    }
    fn skip_close(&mut self, group: Group) -> Option<Ranged<()>> {
        loop {
            match self.next() {
                // open new group, needs to be skipped first
                Some(Ok(Ranged(Token::Open(g), ..))) => {
                    self.skip_close(g)?;
                }

                // TODO: error on close different group

                // we found it
                Some(Ok(t)) if t.0 == Token::Close(group) => break Some(t.map(|_| ())),

                Some(_) => {}
                None => {
                    // TODO: give error unclosed group
                }
            }
        }
    }
    fn ident(&mut self, errors: &mut Errors) -> Option<Ranged<String>> {
        let err = match self.next() {
            Some(Ok(Ranged(Token::Ident(s), start, end))) => return Some(Ranged(s, start, end)),
            Some(Ok(t)) => t.map(ParseErr::Unexpected),
            Some(Err(e)) => e.map(ParseErr::Token),
            None => Ranged(ParseErr::UnexpectedEOF, usize::MAX, usize::MAX),
        };
        errors.push(err);
        None
    }
    fn group(
        &mut self,
        group: Group,
        errors: &mut Errors,
        mut f: impl FnMut(&mut Self, &mut Errors),
    ) -> Option<Ranged<()>> {
        let open = self.expect(Token::Open(group), errors)?;
        loop {
            match self.peek() {
                Some(Ok(t)) if t.0 == Token::Close(group) => {
                    let t = self.next().unwrap().unwrap();
                    break Some(t.map(|_| ()));
                }
                None => {
                    errors.push(Ranged(ParseErr::Unclosed(group), open.1, open.2));
                    break None;
                }
                _ => f(self, errors),
            }
        }
    }

    fn peek(&mut self) -> Option<&Self::Item>;
}

impl<'a> TokenIter for Tokens<'a> {
    fn peek(&mut self) -> Option<&Result<Ranged<Token>, Ranged<TokenErr>>> {
        self.peek()
    }
}

impl Parse for AST {
    fn parse(tk: &mut Tokens, errors: &mut Errors) -> Option<Self> {
        let mut ast = AST {
            exprs: Vec::new(),
            effects: HashMap::new(),
            functions: HashMap::new(),
        };
        loop {
            match tk.peek() {
                // effect
                Some(Ok(Ranged(Token::Effect, ..))) => {
                    if let Some(effect) = Effect::parse(tk, errors) {
                        ast.effects.insert(effect.name.0.clone(), effect);
                    }
                }

                // function
                Some(Ok(Ranged(Token::Fun, ..))) => {
                    if let Some(function) = Function::parse(tk, errors) {
                        ast.functions.insert(function.name.0.clone(), function);
                    }
                }

                // unexpected
                Some(Ok(_)) => errors.push(tk.next().unwrap().unwrap().map(ParseErr::Unexpected)),
                Some(Err(_)) => errors.push(tk.next().unwrap().unwrap_err().map(ParseErr::Token)),

                // eof
                None => break Some(ast),
            }
        }
    }
    fn is_statement_end(t: &Token) -> bool {
        false
    }
}

impl Parse for Effect {
    fn parse(tk: &mut Tokens, errors: &mut Errors) -> Option<Self> {
        tk.expect(Token::Effect, errors)?;
        let name = tk.ident(errors)?;

        let mut effect = Effect {
            name,
            functions: HashMap::new(),
        };

        tk.group(Group::Brace, errors, |tk, errors| {
            todo!();
        });

        Some(effect)
    }

    fn is_statement_end(t: &Token) -> bool {
        matches!(t, Token::Semicolon | Token::Close(Group::Brace))
    }
}

impl Parse for Function {
    fn parse(tk: &mut Tokens, errors: &mut Errors) -> Option<Self> {
        todo!()
    }

    fn is_statement_end(t: &Token) -> bool {
        matches!(t, Token::Semicolon | Token::Close(Group::Brace))
    }
}
