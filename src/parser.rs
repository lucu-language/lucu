use std::{collections::HashMap, iter::Peekable};

use crate::lexer::{Group, Ranged, Token, TokenErr, Tokenizer};

pub type Expr = usize;

#[derive(Debug)]
pub enum Expression {
    Body(Body),
    String(String),
    Ident(Path),
    Call(Expr, Vec<Expr>),
    TryWith(Expr, Vec<Handler>),
    Member(Expr, Ranged<String>),
    Error, // error at parsing, coerces to any type
}

#[derive(Debug)]
pub struct Body {
    main: Vec<Expr>,
    last: Option<Expr>,
}

#[derive(Debug)]
pub struct Handler {
    effect: Path,
    functions: HashMap<String, Function>,
}

#[derive(Debug)]
pub struct Path {
    ident: Ranged<String>,
}

#[derive(Debug)]
pub struct Type {
    ident: Path,
}

#[derive(Debug)]
pub struct FunSign {
    inputs: Vec<(Ranged<String>, Type)>,
    effects: Vec<Path>,
}

#[derive(Debug)]
pub struct FunDecl {
    name: Ranged<String>,
    sign: FunSign,
}

#[derive(Debug)]
pub struct Function {
    decl: FunDecl,
    body: Expr,
}

#[derive(Debug)]
pub struct Effect {
    name: Ranged<String>,
    functions: HashMap<String, FunDecl>,
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
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self>;

    // parse, and if it could not be parsed, skip to anchor tokens (fun effect , ; ( ) { } [ ])
    fn parse_or_skip(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        match Self::parse(tk, errors, exprs) {
            Some(s) => Some(s),
            None => loop {
                match tk.peek() {
                    Some(Ok(Ranged(t, ..))) if t.is_anchor() => break None,
                    None => break None,
                    _ => {
                        tk.next();
                    }
                }
            },
        }
    }
}

pub trait TokenIter: Iterator<Item = Result<Ranged<Token>, Ranged<TokenErr>>> {
    fn check(&mut self, token: Token) -> Option<Ranged<()>> {
        match self.peek() {
            Some(Ok(t)) if t.0 == token => Some(self.next().unwrap().unwrap().map(|_| ())),
            _ => None,
        }
    }
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
    fn skip_close(&mut self, group: Ranged<Group>, errors: &mut Errors) -> Option<Ranged<()>> {
        loop {
            match self.next() {
                // open new group, needs to be skipped first
                Some(Ok(Ranged(Token::Open(g), start, end))) => {
                    self.skip_close(Ranged(g, start, end), errors)?;
                }

                // error on close different group
                Some(Ok(Ranged(Token::Close(g), ..))) if g != group.0 => {
                    errors.push(group.map(ParseErr::Unclosed));
                    break None;
                }

                // we found it
                Some(Ok(Ranged(Token::Close(_), _, end))) => {
                    break Some(Ranged((), group.1, end));
                }

                // skip characters
                Some(_) => {}

                // error on unclosed group
                None => {
                    errors.push(group.map(ParseErr::Unclosed));
                    break None;
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
        comma_separated: bool,
        errors: &mut Errors,
        mut f: impl FnMut(&mut Self, &mut Errors) -> Option<()>,
    ) -> Option<Ranged<()>> {
        let open = self.expect(Token::Open(group), errors)?;
        loop {
            match self.peek() {
                Some(Ok(t)) if t.0 == Token::Close(group) => {
                    let t = self.next().unwrap().unwrap();
                    break Some(Ranged((), open.1, t.2));
                }
                None => {
                    errors.push(Ranged(ParseErr::Unclosed(group), open.1, open.2));
                    break None;
                }
                _ => {
                    // parse inner
                    let _ = f(self, errors);

                    // parse comma?
                    if comma_separated {
                        match self.peek() {
                            // we are closing next
                            Some(Ok(t)) if t.0 == Token::Close(group) => {}

                            // else expect comma
                            _ => match self.expect(Token::Comma, errors) {
                                Some(_) => {}
                                None => {
                                    break self.skip_close(Ranged(group, open.1, open.2), errors)
                                }
                            },
                        }
                    }
                }
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

pub fn parse_ast(tk: &mut Tokens, errors: &mut Errors) -> Option<AST> {
    let mut exprs = Vec::new();
    let mut ast = AST::parse(tk, errors, &mut exprs)?;
    ast.exprs = exprs;
    Some(ast)
}

impl Parse for AST {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        let mut ast = AST {
            exprs: Vec::new(),
            effects: HashMap::new(),
            functions: HashMap::new(),
        };
        loop {
            match tk.peek() {
                // effect
                Some(Ok(Ranged(Token::Effect, ..))) => {
                    if let Some(effect) = Effect::parse_or_skip(tk, errors, exprs) {
                        ast.effects.insert(effect.name.0.clone(), effect);
                    }
                }

                // function
                Some(Ok(Ranged(Token::Fun, ..))) => {
                    if let Some(function) = Function::parse_or_skip(tk, errors, exprs) {
                        ast.functions.insert(function.decl.name.0.clone(), function);
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
}

impl Parse for Path {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        _exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        Some(Path {
            ident: tk.ident(errors)?,
        })
    }
}

impl Parse for Type {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        Some(Type {
            ident: Path::parse_or_skip(tk, errors, exprs)?,
        })
    }
}

impl Parse for FunSign {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        let mut decl = FunSign {
            inputs: Vec::new(),
            effects: Vec::new(),
        };

        tk.group(Group::Paren, true, errors, |tk, errors| {
            let name = tk.ident(errors)?;
            let typ = Type::parse_or_skip(tk, errors, exprs)?;
            decl.inputs.push((name, typ));
            Some(())
        })?;

        if tk.check(Token::Slash).is_some() {
            while matches!(tk.peek(), Some(Ok(Ranged(Token::Ident(_), ..)))) {
                let Some(effect) = Path::parse_or_skip(tk, errors, exprs) else { continue };
                decl.effects.push(effect);
            }
        }

        Some(decl)
    }
}

impl Parse for FunDecl {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        tk.expect(Token::Fun, errors)?;
        let name = tk.ident(errors)?;

        let decl = FunDecl {
            name,
            sign: FunSign::parse_or_skip(tk, errors, exprs)?,
        };

        Some(decl)
    }
}

impl Parse for Effect {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        tk.expect(Token::Effect, errors)?;
        let name = tk.ident(errors)?;

        let mut effect = Effect {
            name,
            functions: HashMap::new(),
        };

        tk.group(Group::Brace, false, errors, |tk, errors| {
            let f = FunDecl::parse_or_skip(tk, errors, exprs)?;
            effect.functions.insert(f.name.0.clone(), f);

            tk.expect(Token::Semicolon, errors)?;
            Some(())
        })?;

        Some(effect)
    }
}

impl Parse for Function {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        let decl = FunDecl::parse_or_skip(tk, errors, exprs)?;
        let body = Ranged::<Body>::parse_or_skip(tk, errors, exprs);
        let n = exprs.len();
        match body {
            Some(b) => exprs.push(b.map(Expression::Body)),
            None => exprs.push(Ranged(Expression::Error, 0, 0)),
        }
        Some(Function { decl, body: n })
    }
}

impl Parse for Handler {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        todo!("handler")
    }
}

impl Parse for Ranged<Expression> {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        let expr = match tk.peek() {
            // try-with
            Some(Ok(Ranged(Token::Try, ..))) => {
                let t = tk.expect(Token::Try, errors)?;
                let body = Ranged::<Expression>::parse_or_skip(tk, errors, exprs)?;
                let mut handlers = Vec::new();
                while matches!(tk.peek(), Some(Ok(Ranged(Token::With, ..)))) {
                    tk.expect(Token::With, errors)?;
                    let Some(handler) = Handler::parse_or_skip(tk, errors, exprs) else { continue };
                    handlers.push(handler);
                }

                let n = exprs.len();
                exprs.push(body);
                Ranged(Expression::TryWith(n, handlers), t.1, t.2) // TODO: get end
            }

            // ident
            Some(Ok(Ranged(Token::Ident(_), ..))) => {
                let path = Path::parse_or_skip(tk, errors, exprs)?;
                let start = path.ident.1;
                let end = path.ident.2;
                Ranged(Expression::Ident(path), start, end)
            }

            // string
            Some(Ok(Ranged(Token::String(s), start, end))) => {
                let start = *start;
                let end = *end;
                let s = s.clone();
                tk.next();
                Ranged(Expression::String(s), start, end)
            }

            // block
            Some(Ok(Ranged(Token::Open(Group::Brace), ..))) => {
                Ranged::<Body>::parse_or_skip(tk, errors, exprs)?.map(Expression::Body)
            }

            _ => {
                errors.push(match tk.next() {
                    Some(Ok(t)) => t.map(ParseErr::Unexpected),
                    Some(Err(e)) => e.map(ParseErr::Token),
                    None => Ranged(ParseErr::UnexpectedEOF, usize::MAX, usize::MAX),
                });
                return None;
            }
        };

        Some(expr)

        // TODO: Call, Member
        // let n = exprs.len();
        // exprs.push(expr);
    }
}

impl Parse for Ranged<Body> {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        let mut main = Vec::new();
        let mut last = None;

        let group = tk.group(Group::Brace, false, errors, |tk, errors| {
            let expr = Ranged::<Expression>::parse_or_skip(tk, errors, exprs)?;
            let n = exprs.len();
            exprs.push(expr);

            if tk.check(Token::Semicolon).is_none() {
                last = Some(n);
            } else {
                main.push(n);
            }

            Some(())
        })?;

        Some(Ranged(Body { main, last }, group.1, group.2))
    }
}
