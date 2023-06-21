use std::collections::HashMap;

use crate::lexer::{Group, Ranged, Token, TokenErr, Tokenizer};

pub type Expr = usize;
pub type Ident = usize;

#[derive(Debug, Default)]
pub enum Expression {
    Body(Body),
    String(String),
    Ident(Identifier),
    Call(Expr, Vec<Expr>),
    TryWith(Expr, Vec<Handler>),
    Member(Expr, Ranged<String>),
    #[default]
    Error, // error at parsing, coerces to any type
}

#[derive(Debug)]
pub struct Body {
    pub main: Vec<Expr>,
    pub last: Option<Expr>,
}

#[derive(Debug)]
pub struct Handler {
    effect: Identifier,
    pub functions: HashMap<String, Function>,
}

#[derive(Debug)]
pub struct Identifier(pub Ranged<Ident>);

#[derive(Debug)]
pub struct Type {
    ident: Identifier,
}

#[derive(Debug)]
pub struct FunSign {
    pub inputs: Vec<(Identifier, Type)>,
    effects: Vec<Identifier>,
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

#[derive(Default)]
pub struct ParseContext {
    pub errors: Vec<Ranged<ParseErr>>,
    pub exprs: Vec<Ranged<Expression>>,
    pub idents: Vec<String>,
}

struct Tokens<'a> {
    iter: Tokenizer<'a>,
    peeked: Option<Option<<Tokenizer<'a> as Iterator>::Item>>,
    last: usize,
    context: ParseContext,
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
    fn expect(&mut self, token: Token) -> Option<Ranged<()>> {
        let err = match self.next() {
            Some(Ok(t)) if t.0 == token => return Some(t.map(|_| ())),
            Some(Ok(t)) => t.map(ParseErr::Unexpected),
            Some(Err(e)) => e.map(ParseErr::Token),
            None => Ranged(ParseErr::UnexpectedEOF, usize::MAX, usize::MAX),
        };
        self.context.errors.push(err);
        None
    }
    fn skip_close(&mut self, group: Ranged<Group>) -> Option<Ranged<()>> {
        loop {
            match self.next() {
                // open new group, needs to be skipped first
                Some(Ok(Ranged(Token::Open(g), start, end))) => {
                    self.skip_close(Ranged(g, start, end))?;
                }

                // error on close different group
                Some(Ok(Ranged(Token::Close(g), ..))) if g != group.0 => {
                    self.context.errors.push(group.map(ParseErr::Unclosed));
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
                    self.context.errors.push(group.map(ParseErr::Unclosed));
                    break None;
                }
            }
        }
    }
    fn push_expr(&mut self, expr: Ranged<Expression>) -> Expr {
        let n = self.context.exprs.len();
        self.context.exprs.push(expr);
        n
    }
    fn push_ident(&mut self, ident: String) -> Ident {
        let n = self.context.idents.len();
        self.context.idents.push(ident);
        n
    }
    fn ident(&mut self) -> Option<Ranged<String>> {
        let err = match self.next() {
            Some(Ok(Ranged(Token::Ident(s), start, end))) => return Some(Ranged(s, start, end)),
            Some(Ok(t)) => t.map(ParseErr::Unexpected),
            Some(Err(e)) => e.map(ParseErr::Token),
            None => Ranged(ParseErr::UnexpectedEOF, usize::MAX, usize::MAX),
        };
        self.context.errors.push(err);
        None
    }
    fn group(
        &mut self,
        group: Group,
        comma_separated: bool,
        mut f: impl FnMut(&mut Self) -> Option<()>,
    ) -> Option<Ranged<()>> {
        let open = self.expect(Token::Open(group))?;
        loop {
            match self.peek() {
                Some(Ok(t)) if t.0 == Token::Close(group) => {
                    let t = self.next().unwrap().unwrap();
                    break Some(Ranged((), open.1, t.2));
                }
                None => {
                    self.context
                        .errors
                        .push(Ranged(ParseErr::Unclosed(group), open.1, open.2));
                    break None;
                }
                _ => {
                    // parse inner
                    let _ = f(self);

                    // parse comma?
                    if comma_separated {
                        match self.peek() {
                            // we are closing next
                            Some(Ok(t)) if t.0 == Token::Close(group) => {}

                            // else expect comma
                            _ => match self.expect(Token::Comma) {
                                Some(_) => {}
                                None => break self.skip_close(Ranged(group, open.1, open.2)),
                            },
                        }
                    }
                }
            }
        }
    }
}

trait Parse: Sized {
    fn parse(tk: &mut Tokens) -> Option<Self>;

    // parse, and if it could not be parsed, skip to anchor tokens
    fn parse_or_skip(tk: &mut Tokens) -> Option<Ranged<Self>> {
        let start = tk.pos_start();
        match Self::parse(tk) {
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
                        tk.skip_close(Ranged(g, start, end));
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

trait ParseDefault: Parse + Default {
    fn parse_or_default(tk: &mut Tokens) -> Ranged<Self> {
        let start = tk.pos_start();
        Self::parse_or_skip(tk).unwrap_or(Ranged(Self::default(), start, start))
    }
}

impl<T> ParseDefault for T where T: Parse + Default {}

pub fn parse_ast(tk: Tokenizer) -> (AST, ParseContext) {
    let mut tk = Tokens {
        iter: tk,
        peeked: None,
        last: 0,
        context: ParseContext::default(),
    };
    let ast = AST::parse(&mut tk).unwrap();
    (ast, tk.context)
}

impl Parse for AST {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut ast = AST {
            effects: HashMap::new(),
            functions: HashMap::new(),
        };
        loop {
            match tk.peek() {
                // effect
                Some(Ok(Ranged(Token::Effect, ..))) => {
                    if let Some(Ranged(effect, ..)) = Effect::parse_or_skip(tk) {
                        ast.effects.insert(effect.name.0.clone(), effect);
                    }
                }

                // function
                Some(Ok(Ranged(Token::Fun, ..))) => {
                    if let Some(Ranged(function, ..)) = Function::parse_or_skip(tk) {
                        ast.functions.insert(function.decl.name.0.clone(), function);
                    }
                }

                // unexpected
                Some(Ok(_)) => {
                    let err = tk.next().unwrap().unwrap().map(ParseErr::Unexpected);
                    tk.context.errors.push(err);
                }
                Some(Err(_)) => {
                    let err = tk.next().unwrap().unwrap_err().map(ParseErr::Token);
                    tk.context.errors.push(err);
                }

                // eof
                None => break Some(ast),
            }
        }
    }
}

impl Parse for Identifier {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        Some(Identifier(tk.ident()?.map(|s| tk.push_ident(s))))
    }
}

impl Parse for Type {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        Some(Type {
            ident: Identifier::parse_or_skip(tk)?.0,
        })
    }
}

impl Parse for FunSign {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut decl = FunSign {
            inputs: Vec::new(),
            effects: Vec::new(),
        };

        tk.group(Group::Paren, true, |tk| {
            let name = Identifier::parse_or_skip(tk)?.0;
            let typ = Type::parse_or_skip(tk)?.0;
            decl.inputs.push((name, typ));
            Some(())
        })?;

        if tk.check(Token::Slash).is_some() {
            while matches!(tk.peek(), Some(Ok(Ranged(Token::Ident(_), ..)))) {
                let Some(Ranged(effect, ..)) = Identifier::parse_or_skip(tk) else { continue };
                decl.effects.push(effect);
            }
        }

        Some(decl)
    }
}

impl Parse for FunDecl {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        tk.expect(Token::Fun)?;
        let name = tk.ident()?;

        let decl = FunDecl {
            name,
            sign: FunSign::parse(tk)?,
        };

        Some(decl)
    }
}

impl Parse for Effect {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        tk.expect(Token::Effect)?;
        let name = tk.ident()?;

        let mut effect = Effect {
            name,
            functions: HashMap::new(),
        };

        tk.group(Group::Brace, false, |tk| {
            let f = FunDecl::parse_or_skip(tk)?.0;
            effect.functions.insert(f.name.0.clone(), f);

            tk.expect(Token::Semicolon)?;
            Some(())
        })?;

        Some(effect)
    }
}

impl Parse for Function {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let decl = FunDecl::parse_or_skip(tk)?.0;

        let start = tk.pos_start();
        let body = Body::parse_or_skip(tk);
        let expr = match body {
            Some(b) => b.map(Expression::Body),
            None => Ranged(Expression::Error, start, start),
        };

        Some(Function {
            decl,
            body: tk.push_expr(expr),
        })
    }
}

impl Parse for Handler {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let ident = Identifier::parse_or_skip(tk)?.0;
        let mut funcs = HashMap::new();

        tk.group(Group::Brace, false, |tk| {
            let func = Function::parse_or_skip(tk)?.0;
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
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let start = tk.pos_start();
        let mut expr = tk.ranged(|tk| match tk.peek() {
            // try-with
            Some(Ok(Ranged(Token::Try, ..))) => {
                tk.expect(Token::Try)?;
                let body = Expression::parse_or_default(tk);
                let mut handlers = Vec::new();
                while matches!(tk.peek(), Some(Ok(Ranged(Token::With, ..)))) {
                    tk.expect(Token::With)?;
                    let Some(Ranged(handler, ..)) = Handler::parse_or_skip(tk) else { continue };
                    handlers.push(handler);
                }
                Some(Expression::TryWith(tk.push_expr(body), handlers))
            }

            // ident
            Some(Ok(Ranged(Token::Ident(_), ..))) => {
                let path = Identifier::parse_or_skip(tk)?.0;
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
                Some(Expression::Body(Body::parse_or_skip(tk)?.0))
            }

            _ => {
                let err = match tk.next() {
                    Some(Ok(t)) => t.map(ParseErr::Unexpected),
                    Some(Err(e)) => e.map(ParseErr::Token),
                    None => Ranged(ParseErr::UnexpectedEOF, tk.pos_end(), tk.pos_end()),
                };
                tk.context.errors.push(err);
                None
            }
        })?;

        // post-fixes
        loop {
            match tk.peek() {
                // member
                Some(Ok(Ranged(Token::Period, ..))) => {
                    tk.expect(Token::Period)?;
                    let member = tk.ident()?;
                    expr = Ranged(
                        Expression::Member(tk.push_expr(expr), member),
                        start,
                        tk.pos_end(),
                    );
                }

                // call
                Some(Ok(Ranged(Token::Open(Group::Paren), ..))) => {
                    let mut args = Vec::new();
                    tk.group(Group::Paren, true, |tk| {
                        let expr = Expression::parse_or_default(tk);
                        args.push(tk.push_expr(expr));
                        Some(())
                    })?;
                    expr = Ranged(
                        Expression::Call(tk.push_expr(expr), args),
                        start,
                        tk.pos_end(),
                    );
                }

                _ => break Some(expr.0),
            }
        }
    }
}

impl Parse for Body {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut main = Vec::new();
        let mut last = None;

        tk.group(Group::Brace, false, |tk| {
            // if we already got the last expression, we should now close this body
            if last.is_some() {
                tk.expect(Token::Close(Group::Brace))?;
            }

            let expr = Expression::parse_or_default(tk);
            let n = tk.push_expr(expr);

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
