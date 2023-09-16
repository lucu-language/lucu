use std::matches;

use crate::{
    analyzer::{EffFunIdx, EffIdx, FunIdx, ParamIdx},
    lexer::{Group, Ranged, Token, TokenErr, Tokenizer},
    vecmap::VecMap,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ExprIdx(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Ident(usize);

impl From<ExprIdx> for usize {
    fn from(value: ExprIdx) -> Self {
        value.0
    }
}

impl From<Ident> for usize {
    fn from(value: Ident) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Equals,
    Divide,
}

#[derive(Debug, Default)]
pub enum Expression {
    Body(Body),

    Call(ExprIdx, Vec<ExprIdx>),
    Member(ExprIdx, Ranged<String>),
    IfElse(ExprIdx, ExprIdx, Option<ExprIdx>),
    Op(ExprIdx, Op, ExprIdx),
    Break(Option<ExprIdx>),

    TryWith(ExprIdx, ExprIdx),
    Handler(Handler),

    String(String),
    Int(i128),
    Ident(Ident),

    #[default]
    Error, // error at parsing, coerces to any type
}

#[derive(Debug)]
pub struct Body {
    pub main: Vec<ExprIdx>,
    pub last: Option<ExprIdx>,
}

#[derive(Debug)]
pub struct Handler {
    pub effect: Ident,
    pub functions: Vec<Function>,
}

#[derive(Debug)]
pub struct Type {
    pub ident: Ident,
}

#[derive(Debug)]
pub enum ReturnType {
    Never,
    Type(Type),
}

#[derive(Debug)]
pub struct FunSign {
    pub inputs: VecMap<ParamIdx, (Ident, Type)>,
    pub output: Option<ReturnType>,
    pub effects: Vec<Ident>,
}

#[derive(Debug)]
pub struct FunDecl {
    pub name: Ident,
    pub sign: FunSign,
}

#[derive(Debug)]
pub struct Function {
    pub decl: FunDecl,
    pub body: ExprIdx,
}

#[derive(Debug)]
pub struct Effect {
    pub name: Ident,
    pub functions: VecMap<EffFunIdx, FunDecl>,
}

#[derive(Debug)]
pub struct AST {
    pub effects: VecMap<EffIdx, Effect>,
    pub functions: VecMap<FunIdx, Function>,
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
    pub exprs: VecMap<ExprIdx, Ranged<Expression>>,
    pub idents: VecMap<Ident, Ranged<String>>,
}

struct Tokens<'a> {
    iter: Tokenizer<'a>,
    peeked: Option<Option<<Tokenizer<'a> as Iterator>::Item>>,
    last: usize,
    context: ParseContext,
}

impl<'a> Tokens<'a> {
    fn pos_start(&mut self) -> usize {
        self.peek().map(|p| p.1).unwrap_or(usize::MAX)
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
        self.last = tok.as_ref().map(|p| p.2).unwrap_or(usize::MAX);
        tok
    }
    fn ranged<T>(&mut self, f: impl FnOnce(&mut Self) -> Option<T>) -> Option<Ranged<T>> {
        let start = self.pos_start();
        let t = f(self)?;
        Some(Ranged(t, start, self.pos_end()))
    }
    fn check(&mut self, token: Token) -> Option<Ranged<()>> {
        match self.peek() {
            Some(t) if t.0 == token => Some(self.next().unwrap().map(|_| ())),
            _ => None,
        }
    }
    fn expect(&mut self, token: Token) -> Option<Ranged<()>> {
        let err = match self.next() {
            Some(t) if t.0 == token => return Some(t.map(|_| ())),
            Some(t) => t.map(ParseErr::Unexpected),
            None => Ranged(ParseErr::UnexpectedEOF, usize::MAX, usize::MAX),
        };
        self.context.errors.push(err);
        None
    }
    fn skip_close(&mut self, group: Ranged<Group>) -> Option<Ranged<()>> {
        loop {
            match self.next() {
                // open new group, needs to be skipped first
                Some(Ranged(Token::Open(g), start, end)) => {
                    self.skip_close(Ranged(g, start, end))?;
                }

                // error on close different group
                Some(Ranged(Token::Close(g), ..)) if g != group.0 => {
                    self.context.errors.push(group.map(ParseErr::Unclosed));
                    break None;
                }

                // we found it
                Some(Ranged(Token::Close(_), _, end)) => {
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
    fn push_expr(&mut self, expr: Ranged<Expression>) -> ExprIdx {
        self.context.exprs.push(ExprIdx, expr)
    }
    fn push_ident(&mut self, ident: Ranged<String>) -> Ident {
        self.context.idents.push(Ident, ident)
    }
    fn ident(&mut self) -> Option<Ranged<String>> {
        let err = match self.next() {
            Some(Ranged(Token::Ident(s), start, end)) => return Some(Ranged(s, start, end)),
            Some(t) => t.map(ParseErr::Unexpected),
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
                Some(t) if t.0 == Token::Close(group) => {
                    let t = self.next().unwrap();
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
                            Some(t) if t.0 == Token::Close(group) => {}

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
                    Some(Ranged(Token::Open(g), start, end)) => {
                        let g = *g;
                        let start = *start;
                        let end = *end;
                        tk.next();
                        tk.skip_close(Ranged(g, start, end));
                    }
                    Some(Ranged(t, ..)) if t.is_anchor() => break None,
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

    // parse ast
    let ast = AST::parse(&mut tk).unwrap();

    // add token errors
    tk.context
        .errors
        .extend(tk.iter.errors.into_iter().map(|r| r.map(ParseErr::Token)));

    // return
    (ast, tk.context)
}

impl Parse for AST {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut ast = AST {
            effects: VecMap::new(),
            functions: VecMap::new(),
        };
        loop {
            match tk.peek() {
                // effect
                Some(Ranged(Token::Effect, ..)) => {
                    if let Some(Ranged(effect, ..)) = Effect::parse_or_skip(tk) {
                        ast.effects.push_value(effect);
                    }
                }

                // function
                Some(Ranged(Token::Fun, ..)) => {
                    if let Some(Ranged(function, ..)) = Function::parse_or_skip(tk) {
                        ast.functions.push_value(function);
                    }
                }

                // ignore semicolons
                Some(Ranged(Token::Semicolon, ..)) => {
                    tk.next();
                }

                // unexpected
                Some(_) => {
                    let err = tk.next().unwrap().map(ParseErr::Unexpected);
                    tk.context.errors.push(err);
                }

                // eof
                None => break Some(ast),
            }
        }
    }
}

impl Parse for Type {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let id = tk.ident()?;
        Some(Type {
            ident: tk.push_ident(id),
        })
    }
}

impl Parse for FunSign {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut decl = FunSign {
            inputs: VecMap::new(),
            effects: Vec::new(),
            output: None,
        };

        tk.group(Group::Paren, true, |tk| {
            let id = tk.ident()?;
            let name = tk.push_ident(id);
            let typ = Type::parse_or_skip(tk)?.0;
            decl.inputs.push_value((name, typ));
            Some(())
        })?;

        match tk.peek() {
            // never returns
            Some(Ranged(Token::Bang, ..)) => {
                tk.expect(Token::Bang)?;
                decl.output = Some(ReturnType::Never);
            }

            // no return type
            Some(Ranged(t, ..)) if t.continues_statement() => {}
            None => {}

            // some return type
            _ => {
                let typ = Type::parse_or_skip(tk)?.0;
                decl.output = Some(ReturnType::Type(typ));
            }
        }

        if tk.check(Token::Slash).is_some() {
            while matches!(tk.peek(), Some(Ranged(Token::Ident(_), ..))) {
                let Some(effect) = tk.ident() else { continue };
                let effect = tk.push_ident(effect);
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
            name: tk.push_ident(name),
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
            name: tk.push_ident(name),
            functions: VecMap::new(),
        };

        tk.group(Group::Brace, false, |tk| {
            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            // parse function
            let f = FunDecl::parse_or_skip(tk)?.0;
            effect.functions.push_value(f);

            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

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
        let id = tk.ident()?;
        let ident = tk.push_ident(id);
        let mut funcs = Vec::new();

        tk.group(Group::Brace, false, |tk| {
            let func = Function::parse_or_skip(tk)?.0;
            funcs.push(func);
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
            Some(Ranged(Token::Try, ..)) => {
                tk.expect(Token::Try)?;
                let body = Expression::parse_or_default(tk);
                tk.expect(Token::With)?;
                let handler = Handler::parse_or_skip(tk)?;
                let handler = tk.push_expr(handler.map(Expression::Handler));
                Some(Expression::TryWith(tk.push_expr(body), handler))
            }

            // if-(else)
            Some(Ranged(Token::If, ..)) => {
                tk.expect(Token::If)?;

                let condition = Expression::parse_or_default(tk);
                let condition = tk.push_expr(condition);

                let yes = Body::parse_or_skip(tk)?.map(Expression::Body);
                let yes = tk.push_expr(yes);

                let no = if tk.check(Token::Else).is_some() {
                    let no = Body::parse_or_skip(tk)?.map(Expression::Body);
                    Some(tk.push_expr(no))
                } else {
                    None
                };

                Some(Expression::IfElse(condition, yes, no))
            }

            // break
            Some(Ranged(Token::Break, ..)) => {
                tk.expect(Token::Break)?;

                if matches!(
                    tk.peek(),
                    Some(Ranged(t, ..), ..) if t.continues_statement()
                ) {
                    Some(Expression::Break(None))
                } else {
                    let value = Expression::parse_or_default(tk);
                    let value = tk.push_expr(value);
                    Some(Expression::Break(Some(value)))
                }
            }

            // ident
            Some(Ranged(Token::Ident(_), ..)) => {
                let id = tk.ident()?;
                let path = tk.push_ident(id);
                Some(Expression::Ident(path))
            }

            // string
            Some(Ranged(Token::String(s), ..)) => {
                let s = s.clone();
                tk.next();
                Some(Expression::String(s))
            }

            // int
            Some(&Ranged(Token::Int(num), ..)) => {
                tk.next();
                Some(Expression::Int(num))
            }

            // block
            Some(Ranged(Token::Open(Group::Brace), ..)) => {
                Some(Expression::Body(Body::parse_or_skip(tk)?.0))
            }

            _ => {
                let err = match tk.next() {
                    Some(t) => t.map(ParseErr::Unexpected),
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
                Some(Ranged(Token::Period, ..)) => {
                    tk.expect(Token::Period)?;
                    let member = tk.ident()?;
                    expr = Ranged(
                        Expression::Member(tk.push_expr(expr), member),
                        start,
                        tk.pos_end(),
                    );
                }

                // call
                Some(Ranged(Token::Open(Group::Paren), ..)) => {
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

                // binary ops
                // TODO: operator precedence
                Some(Ranged(Token::DoubleEquals, ..)) => {
                    tk.expect(Token::DoubleEquals)?;

                    let right = Expression::parse_or_default(tk);
                    let right = tk.push_expr(right);

                    expr = Ranged(
                        Expression::Op(tk.push_expr(expr), Op::Equals, right),
                        start,
                        tk.pos_end(),
                    )
                }

                Some(Ranged(Token::Slash, ..)) => {
                    tk.expect(Token::Slash)?;

                    let right = Expression::parse_or_default(tk);
                    let right = tk.push_expr(right);

                    expr = Ranged(
                        Expression::Op(tk.push_expr(expr), Op::Divide, right),
                        start,
                        tk.pos_end(),
                    )
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

            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            // parse expression
            let expr = Expression::parse_or_default(tk);
            let n = tk.push_expr(expr);

            if tk.check(Token::Semicolon).is_none() {
                last = Some(n);
            } else {
                // skip semicolons
                while tk.check(Token::Semicolon).is_some() {}
                main.push(n);
            }

            Some(())
        })?;

        Some(Body { main, last })
    }
}
