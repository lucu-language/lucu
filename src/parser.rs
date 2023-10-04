use std::matches;

use crate::{
    analyzer::{EffFunIdx, EffIdx, FunIdx, ParamIdx},
    error::{Error, Expected, Ranged},
    lexer::{Group, Token, Tokenizer},
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
    Multiply,
    Subtract,
    Add,
}

impl Op {
    fn from_token(value: &Token) -> Option<Op> {
        match value {
            Token::Slash => Some(Op::Divide),
            Token::DoubleEquals => Some(Op::Equals),
            Token::Dash => Some(Op::Subtract),
            Token::Asterisk => Some(Op::Multiply),
            Token::Plus => Some(Op::Add),
            _ => None,
        }
    }
}

#[derive(Debug, Default)]
pub enum Expression {
    Body(Body),

    Call(ExprIdx, Vec<ExprIdx>),
    Member(ExprIdx, Ident),
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
    pub break_type: Option<ReturnType>,
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
    pub implied: Vec<ExprIdx>,
    pub functions: VecMap<FunIdx, Function>,
}

#[derive(Default)]
pub struct ParseContext {
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
        if self.peek_check(token) {
            Some(self.next().unwrap().empty())
        } else {
            None
        }
    }
    fn peek_check(&mut self, token: Token) -> bool {
        matches!(self.peek(), Some(t) if t.0 == token)
    }
    fn expect(&mut self, token: Token) -> Option<Ranged<()>> {
        let err = match self.next() {
            Some(t) if t.0 == token => return Some(t.empty()),
            Some(ref t @ Ranged(Token::Open(group), _, _)) => {
                // skip entire unexpected group
                self.skip_close(t.with(group));
                t.with(Error::Unexpected(token.into()))
            }
            Some(t) => t.with(Error::Unexpected(token.into())),
            None => Ranged(Error::Unexpected(token.into()), usize::MAX, usize::MAX),
        };
        self.iter.errors.push(err);
        None
    }
    fn skip_close(&mut self, group: Ranged<Group>) -> Ranged<()> {
        loop {
            match self.peek() {
                // open new group, needs to be skipped first
                Some(&Ranged(Token::Open(g), start, end)) => {
                    self.next();
                    self.skip_close(Ranged(g, start, end));
                }

                // error on close different group
                Some(&Ranged(Token::Close(g), start, _)) if g != group.0 => {
                    self.iter.errors.push(group.map(Error::UnclosedGroup));
                    break Ranged((), group.1, start);
                }

                // we found it
                Some(&Ranged(Token::Close(_), _, end)) => {
                    self.next();
                    break Ranged((), group.1, end);
                }

                // skip characters
                Some(_) => {
                    self.next();
                }

                // error on unclosed group
                None => {
                    self.iter.errors.push(group.map(Error::UnclosedGroup));
                    break Ranged((), group.1, usize::MAX);
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
            Some(t) => t.with(Error::Unexpected(Expected::Identifier)),
            None => Ranged(
                Error::Unexpected(Expected::Identifier),
                usize::MAX,
                usize::MAX,
            ),
        };
        self.iter.errors.push(err);
        None
    }
    fn group(
        &mut self,
        group: Group,
        comma_separated: bool,
        mut f: impl FnMut(&mut Self) -> Option<()>,
    ) -> Option<Ranged<()>> {
        let open = self.expect(Token::Open(group))?;
        Some(loop {
            match self.peek() {
                Some(t) if t.0 == Token::Close(group) => {
                    let t = self.next().unwrap();
                    break Ranged((), open.1, t.2);
                }
                None => {
                    self.iter
                        .errors
                        .push(Ranged(Error::UnclosedGroup(group), open.1, open.2));
                    break Ranged((), open.1, usize::MAX);
                }
                _ => {
                    // parse inner
                    if f(self).is_none() {
                        // error parsing, skip to anchor
                        loop {
                            match self.peek() {
                                Some(Ranged(Token::Open(g), start, end)) => {
                                    let g = *g;
                                    let start = *start;
                                    let end = *end;
                                    self.next();
                                    self.skip_close(Ranged(g, start, end));
                                }
                                Some(Ranged(t, ..)) if t.is_anchor() => break,
                                None => break,
                                _ => {
                                    self.next();
                                }
                            }
                        }
                    }
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
        })
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

    // return
    (ast, tk.context)
}

impl Parse for AST {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut ast = AST {
            effects: VecMap::new(),
            functions: VecMap::new(),
            implied: Vec::new(),
        };
        loop {
            match tk.peek() {
                // effect
                Some(Ranged(Token::Effect, ..)) => {
                    if let Some(Ranged(effect, ..)) = Effect::parse_or_skip(tk) {
                        ast.effects.push_value(effect);
                    }
                }

                // implied
                Some(Ranged(Token::Implicit, ..)) => {
                    tk.next();
                    if let Some(handler) = Handler::parse_or_skip(tk) {
                        let expr = tk.push_expr(handler.map(Expression::Handler));
                        ast.implied.push(expr);
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
                Some(r) => {
                    let err = r.with(Error::Unexpected(Expected::Definition));
                    tk.next();
                    tk.iter.errors.push(err);
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

impl Parse for ReturnType {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        match tk.peek() {
            // never returns
            Some(Ranged(Token::Bang, ..)) => {
                tk.next();
                Some(ReturnType::Never)
            }

            // no return type
            Some(Ranged(t, ..)) if t.continues_statement() => None,
            None => None,

            // some return type
            _ => {
                let typ = Type::parse_or_skip(tk)?.0;
                Some(ReturnType::Type(typ))
            }
        }
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

        decl.output = ReturnType::parse(tk);

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

        let break_type = ReturnType::parse(tk);

        tk.group(Group::Brace, false, |tk| {
            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            // parse function
            let func = Function::parse_or_skip(tk)?.0;
            funcs.push(func);

            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            Some(())
        })?;

        Some(Handler {
            effect: ident,
            functions: funcs,
            break_type,
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
                    // allow for else-if
                    let no = if tk.peek_check(Token::If) {
                        Expression::parse_or_default(tk)
                    } else {
                        Body::parse_or_skip(tk)?.map(Expression::Body)
                    };
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
                    Some(t) => t.with(Error::Unexpected(Expected::Expression)),
                    None => Ranged(
                        Error::Unexpected(Expected::Expression),
                        tk.pos_end(),
                        tk.pos_end(),
                    ),
                };
                tk.iter.errors.push(err);
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
                        Expression::Member(tk.push_expr(expr), tk.push_ident(member)),
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
                Some(Ranged(t, ..)) => match Op::from_token(t) {
                    Some(op) => {
                        tk.next();

                        let right = Expression::parse_or_default(tk);
                        let right = tk.push_expr(right);

                        expr = Ranged(
                            Expression::Op(tk.push_expr(expr), op, right),
                            start,
                            tk.pos_end(),
                        )
                    }
                    None => break Some(expr.0),
                },

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
            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            // parse expression
            let expr = Expression::parse_or_default(tk);
            let n = tk.push_expr(expr);

            if tk.check(Token::Semicolon).is_none() {
                last = Some(n);
                if !tk.peek_check(Token::Close(Group::Brace)) {
                    None
                } else {
                    Some(())
                }
            } else {
                // skip semicolons
                while tk.check(Token::Semicolon).is_some() {}
                main.push(n);
                Some(())
            }
        })?;

        Some(Body { main, last })
    }
}
