use std::collections::HashMap;

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
    pub main: Vec<Expr>,
    pub last: Option<Expr>,
}

#[derive(Debug)]
pub struct Handler {
    effect: Path,
    pub functions: HashMap<String, Function>,
}

#[derive(Debug)]
pub struct Path {
    pub ident: Ranged<String>,
}

#[derive(Debug)]
pub struct Type {
    ident: Path,
}

#[derive(Debug)]
pub struct FunSign {
    pub inputs: Vec<(Ranged<String>, Type)>,
    effects: Vec<Path>,
}

#[derive(Debug)]
pub struct FunDecl {
    name: Ranged<String>,
    pub sign: FunSign,
}

#[derive(Debug)]
pub struct Function {
    pub decl: FunDecl,
    pub body: Expr,
}

#[derive(Debug)]
pub struct Effect {
    name: Ranged<String>,
    functions: HashMap<String, FunDecl>,
}

#[derive(Debug)]
pub struct AST {
    pub exprs: Vec<Ranged<Expression>>,

    effects: HashMap<String, Effect>,
    pub functions: HashMap<String, Function>,
}

#[derive(Debug)]
pub enum ParseErr {
    Token(TokenErr),
    Unexpected(Token),
    UnexpectedEOF,
    Unclosed(Group),
}

struct Tokens<'a> {
    iter: Tokenizer<'a>,
    peeked: Option<Option<<Tokenizer<'a> as Iterator>::Item>>,
    last: usize,
}

impl<'a> Tokens<'a> {
    fn pos_start(&mut self) -> usize {
        self.peek()
            .map(|p| match p {
                Ok(r) => r.1,
                Err(r) => r.1,
            })
            .unwrap_or(self.iter.pos)
    }
    fn pos_end(&self) -> usize {
        self.last
    }
    fn peek(&mut self) -> Option<&<Tokenizer<'a> as Iterator>::Item> {
        let iter = &mut self.iter;
        self.peeked.get_or_insert_with(|| iter.next()).as_ref()
    }
    fn next(&mut self) -> Option<<Tokenizer<'a> as Iterator>::Item> {
        let tok = match self.peeked.take() {
            Some(v) => v,
            None => self.iter.next(),
        };
        self.last = tok
            .as_ref()
            .map(|p| match p {
                Ok(r) => r.2,
                Err(r) => r.2,
            })
            .unwrap_or(self.iter.pos);
        tok
    }
    fn ranged<T>(&mut self, f: impl FnOnce(&mut Self) -> Option<T>) -> Option<Ranged<T>> {
        let start = self.pos_start();
        let t = f(self)?;
        Some(Ranged(t, start, self.pos_end()))
    }
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
}

type Errors = Vec<Ranged<ParseErr>>;

trait Parse: Sized {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self>;

    // parse, and if it could not be parsed, skip to anchor tokens
    fn parse_or_skip(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Ranged<Self>> {
        let start = tk.pos_start();
        match Self::parse(tk, errors, exprs) {
            // successful parse
            Some(s) => Some(Ranged(s, start, tk.pos_end())),

            // skip to anchor
            None => loop {
                match tk.peek() {
                    Some(Ok(Ranged(Token::Open(g), start, end))) => {
                        let g = *g;
                        let start = *start;
                        let end = *end;
                        tk.next();
                        tk.skip_close(Ranged(g, start, end), errors);
                    }
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

pub fn parse_ast(tk: Tokenizer, errors: &mut Errors) -> Option<AST> {
    let mut exprs = Vec::new();
    let mut ast = AST::parse(
        &mut Tokens {
            iter: tk,
            peeked: None,
            last: 0,
        },
        errors,
        &mut exprs,
    )?;
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
                    if let Some(Ranged(effect, ..)) = Effect::parse_or_skip(tk, errors, exprs) {
                        ast.effects.insert(effect.name.0.clone(), effect);
                    }
                }

                // function
                Some(Ok(Ranged(Token::Fun, ..))) => {
                    if let Some(Ranged(function, ..)) = Function::parse_or_skip(tk, errors, exprs) {
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
            ident: Path::parse_or_skip(tk, errors, exprs)?.0,
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
            let typ = Type::parse_or_skip(tk, errors, exprs)?.0;
            decl.inputs.push((name, typ));
            Some(())
        })?;

        if tk.check(Token::Slash).is_some() {
            while matches!(tk.peek(), Some(Ok(Ranged(Token::Ident(_), ..)))) {
                let Some(Ranged(effect, ..)) = Path::parse_or_skip(tk, errors, exprs) else { continue };
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
            sign: FunSign::parse(tk, errors, exprs)?,
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
            let f = FunDecl::parse_or_skip(tk, errors, exprs)?.0;
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
        let decl = FunDecl::parse_or_skip(tk, errors, exprs)?.0;
        let body = Body::parse_or_skip(tk, errors, exprs);
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
        let ident = Path::parse_or_skip(tk, errors, exprs)?.0;
        let mut funcs = HashMap::new();

        tk.group(Group::Brace, false, errors, |tk, errors| {
            let func = Function::parse_or_skip(tk, errors, exprs)?.0;
            funcs.insert(func.decl.name.0.clone(), func);
            Some(())
        })?;

        Some(Handler {
            effect: ident,
            functions: funcs,
        })
    }
}

impl Parse for Expression {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        let start = tk.pos_start();
        let mut expr = tk.ranged(|tk| match tk.peek() {
            // try-with
            Some(Ok(Ranged(Token::Try, ..))) => {
                tk.expect(Token::Try, errors)?;
                let body = Expression::parse_or_skip(tk, errors, exprs)?;
                let mut handlers = Vec::new();
                while matches!(tk.peek(), Some(Ok(Ranged(Token::With, ..)))) {
                    tk.expect(Token::With, errors)?;
                    let Some(Ranged(handler, ..)) = Handler::parse_or_skip(tk, errors, exprs) else { continue };
                    handlers.push(handler);
                }

                let n = exprs.len();
                exprs.push(body);
                Some(Expression::TryWith(n, handlers))
            }

            // ident
            Some(Ok(Ranged(Token::Ident(_), ..))) => {
                let path = Path::parse_or_skip(tk, errors, exprs)?.0;
                Some(Expression::Ident(path))
            }

            // string
            Some(Ok(Ranged(Token::String(s), ..))) => {
                let s = s.clone();
                tk.next();
                Some(Expression::String(s))
            }

            // block
            Some(Ok(Ranged(Token::Open(Group::Brace), ..))) => {
                Some(Expression::Body(Body::parse_or_skip(tk, errors, exprs)?.0))
            }

            _ => {
                errors.push(match tk.next() {
                    Some(Ok(t)) => t.map(ParseErr::Unexpected),
                    Some(Err(e)) => e.map(ParseErr::Token),
                    None => Ranged(ParseErr::UnexpectedEOF, tk.pos_end(), tk.pos_end()),
                });
                None
            }
        })?;

        // post-fixes
        loop {
            match tk.peek() {
                // member
                Some(Ok(Ranged(Token::Period, ..))) => {
                    tk.expect(Token::Period, errors)?;
                    let member = tk.ident(errors)?;

                    let n = exprs.len();
                    exprs.push(expr);
                    expr = Ranged(Expression::Member(n, member), start, tk.pos_end());
                }

                // call
                Some(Ok(Ranged(Token::Open(Group::Paren), ..))) => {
                    let mut args = Vec::new();
                    tk.group(Group::Paren, true, errors, |tk, errors| {
                        let expr = Expression::parse_or_skip(tk, errors, exprs)?;
                        let n = exprs.len();
                        exprs.push(expr);
                        args.push(n);
                        Some(())
                    })?;

                    let n = exprs.len();
                    exprs.push(expr);
                    expr = Ranged(Expression::Call(n, args), start, tk.pos_end());
                }

                _ => break Some(expr.0),
            }
        }
    }
}

impl Parse for Body {
    fn parse(
        tk: &mut Tokens,
        errors: &mut Errors,
        exprs: &mut Vec<Ranged<Expression>>,
    ) -> Option<Self> {
        let mut main = Vec::new();
        let mut last = None;

        tk.group(Group::Brace, false, errors, |tk, errors| {
            // if we already got the last expression, we should now close this body
            if last.is_some() {
                tk.expect(Token::Close(Group::Brace), errors)?;
            }

            let expr = Expression::parse_or_skip(tk, errors, exprs)?;
            let n = exprs.len();
            exprs.push(expr);

            if tk.check(Token::Semicolon).is_none() {
                last = Some(n);
            } else {
                main.push(n);
            }

            Some(())
        })?;

        Some(Body { main, last })
    }
}
