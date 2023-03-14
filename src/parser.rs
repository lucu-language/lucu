use std::{collections::HashMap, iter::Peekable, slice::Iter, str::from_utf8};

use crate::lexer;

#[derive(Debug)]
pub enum EffectName<'a> {
    Unnamed(Path<'a>),
    Named(&'a str, Path<'a>),
}

#[derive(Debug)]
pub enum Effect<'a> {
    EffectAlias(Vec<EffectName<'a>>),
    EffectDef(EffectDef<'a>),
}

#[derive(Debug)]
pub enum Type<'a> {
    Path(Path<'a>),
}

#[derive(Debug)]
pub struct Path<'a>(Vec<&'a str>);

#[derive(Debug)]
pub struct FuncSig<'a> {
    params: Vec<(&'a str, Type<'a>)>,
    ret: Option<Type<'a>>,
    effects: Vec<EffectName<'a>>,
}

#[derive(Debug)]
pub struct EffectDef<'a> {
    funcs: HashMap<&'a str, FuncSig<'a>>,
}

#[derive(Debug)]
pub struct Func<'a> {
    sig: FuncSig<'a>,
    body: Body<'a>,
}

#[derive(Debug)]
pub struct Body<'a> {
    exprs: Vec<Expr<'a>>,
    last: Option<Box<Expr<'a>>>,
}

#[derive(Debug)]
pub enum Expr<'a> {
    TryWith(Body<'a>, Vec<Expr<'a>>),
    Call(Box<Expr<'a>>, Vec<Expr<'a>>),
    Handler(Path<'a>, HashMap<&'a str, Func<'a>>),
    Path(Path<'a>),
    String(&'a str),
}

#[derive(Debug)]
pub struct AST<'a> {
    effects: HashMap<&'a str, Effect<'a>>,
    functions: HashMap<&'a str, Func<'a>>,
}

type Result<T> = std::result::Result<T, String>;

pub fn parse(file: &str, tokens: lexer::Tokens) -> Result<AST<'_>> {
    let mut peek = tokens.0.iter().peekable();

    let mut ast = AST {
        effects: HashMap::new(),
        functions: HashMap::new(),
    };

    loop {
        match peek.peek() {
            Some(&token) => match token.typ {
                lexer::TokenType::Semicolon => continue,
                lexer::TokenType::Effect => parse_effect(file, &mut peek, &mut ast)?,
                lexer::TokenType::Fun => {
                    let (name, f) = parse_function(file, &mut peek)?;
                    ast.functions.insert(name, f);
                }
                _ => panic!(),
            },
            None => return Ok(ast),
        }
    }
}

type Tokens<'a> = Peekable<Iter<'a, lexer::Token>>;

fn expect(tokens: &mut Tokens, typ: lexer::TokenType) -> Result<lexer::Token> {
    let Some(&t) = tokens.next() else {
        return Err(format!("unexpected EOF, expected {:?}", typ));
    };

    if t.typ != typ {
        return Err(format!("unexpected {:?}, expected {:?}", t.typ, typ));
    }

    Ok(t)
}

fn ignore(tokens: &mut Tokens, typ: lexer::TokenType) {
    while check(tokens, typ) {
        tokens.next();
    }
}

fn empty(tokens: &mut Tokens) -> Result<()> {
    if let Some(&t) = tokens.peek() {
        Err(format!("unexpected {:?}", t.typ))
    } else {
        Ok(())
    }
}

fn check(tokens: &mut Tokens, typ: lexer::TokenType) -> bool {
    let Some(&t) = tokens.peek() else {
        return false;
    };

    if t.typ != typ {
        return false;
    }

    return true;
}

fn ident<'a>(file: &'a str, tokens: &mut Tokens) -> Result<&'a str> {
    let t = expect(tokens, lexer::TokenType::Identifier)?;

    // FIXME: non-ascii files
    let bytes = &file.as_bytes()[t.place..];

    let mut end = 0;
    while bytes[end].is_ascii_alphanumeric() {
        end += 1;
    }

    Ok(from_utf8(&bytes[..end]).unwrap())
}

fn string<'a>(file: &'a str, tokens: &mut Tokens) -> Result<&'a str> {
    let t = expect(tokens, lexer::TokenType::String)?;
    let mut escaped = false;

    // FIXME: non-ascii files
    let bytes = &file.as_bytes()[(t.place + 1)..];

    let mut end = 0;
    while bytes[end] != 0x22 || escaped {
        if bytes[end] == 0x5C {
            escaped = !escaped;
        } else {
            escaped = false;
        }
        end += 1;
    }

    Ok(from_utf8(&bytes[..end]).unwrap())
}

fn group(tokens: &mut Tokens, typ: lexer::GroupType) -> Result<Vec<lexer::Token>> {
    let t = expect(tokens, lexer::TokenType::Group(typ))?;

    let mut inner: Vec<lexer::Token> = Vec::new();
    for _ in 0..t.len {
        inner.push(*tokens.next().unwrap());
    }
    Ok(inner)
}

fn parse_function<'a>(file: &'a str, peek: &mut Tokens) -> Result<(&'a str, Func<'a>)> {
    let (name, sig) = parse_signature(file, peek)?;
    let body = parse_body(file, peek)?;
    Ok((name, Func { sig, body }))
}

fn parse_body<'a>(file: &'a str, peek: &mut Tokens) -> Result<Body<'a>> {
    let vec = group(peek, lexer::GroupType::Brace)?;
    let mut inner = vec.iter().peekable();

    let mut body = Body {
        exprs: Vec::new(),
        last: None,
    };

    while inner.peek().is_some() {
        ignore(&mut inner, lexer::TokenType::Semicolon);
        let expr = parse_expr(file, &mut inner)?;

        if check(&mut inner, lexer::TokenType::Semicolon) {
            expect(&mut inner, lexer::TokenType::Semicolon)?;
            body.exprs.push(expr);
        } else {
            empty(&mut inner)?;
            body.last = Some(Box::new(expr));
        }
    }

    Ok(body)
}

fn parse_expr<'a>(file: &'a str, peek: &mut Tokens) -> Result<Expr<'a>> {
    // base expr
    let mut expr = if check(peek, lexer::TokenType::Try) {
        // try-with
        expect(peek, lexer::TokenType::Try)?;
        let body = parse_body(file, peek)?;

        let mut handlers = Vec::new();
        while check(peek, lexer::TokenType::With) {
            expect(peek, lexer::TokenType::With)?;
            handlers.push(parse_expr(file, peek)?);
        }

        Expr::TryWith(body, handlers)
    } else if check(peek, lexer::TokenType::String) {
        // string
        Expr::String(string(file, peek)?)
    } else {
        // path or handler
        let path = parse_path(file, peek)?;

        if check(peek, lexer::TokenType::Group(lexer::GroupType::Brace)) {
            // handler
            let vec = group(peek, lexer::GroupType::Brace)?;
            let mut handler = vec.iter().peekable();

            let mut funcs = HashMap::new();
            while handler.peek().is_some() {
                ignore(&mut handler, lexer::TokenType::Semicolon);
                let (name, f) = parse_function(file, &mut handler)?;
                funcs.insert(name, f);
            }

            Expr::Handler(path, funcs)
        } else {
            Expr::Path(path)
        }
    };

    // operators
    while check(peek, lexer::TokenType::Group(lexer::GroupType::Paren)) {
        // call
        let vec = group(peek, lexer::GroupType::Paren)?;
        let mut args = vec.iter().peekable();

        let mut call = Vec::new();
        while args.peek().is_some() {
            call.push(parse_expr(file, &mut args)?);
            if args.peek().is_some() {
                expect(&mut args, lexer::TokenType::Comma)?;
            }
        }

        expr = Expr::Call(Box::new(expr), call);
    }

    Ok(expr)
}

fn parse_type<'a>(file: &'a str, peek: &mut Tokens) -> Result<Type<'a>> {
    Ok(Type::Path(parse_path(file, peek)?))
}

fn parse_path<'a>(file: &'a str, peek: &mut Tokens) -> Result<Path<'a>> {
    let mut vec = vec![ident(file, peek)?];
    while check(peek, lexer::TokenType::Doublecolon) {
        expect(peek, lexer::TokenType::Doublecolon)?;
        vec.push(ident(file, peek)?);
    }
    Ok(Path(vec))
}

fn parse_effects<'a>(file: &'a str, peek: &mut Tokens) -> Result<Vec<EffectName<'a>>> {
    let mut effects = Vec::new();

    loop {
        // FIXME: assumes types start with an identifier
        if check(peek, lexer::TokenType::Identifier) {
            // unnamed
            effects.push(EffectName::Unnamed(parse_path(file, peek)?));
        } else if check(peek, lexer::TokenType::Group(lexer::GroupType::Paren)) {
            // named
            let vec = group(peek, lexer::GroupType::Paren)?;
            let mut inner = vec.iter().peekable();

            let name = ident(file, &mut inner)?;
            let eff = parse_path(file, &mut inner)?;
            empty(&mut inner)?;

            effects.push(EffectName::Named(name, eff));
        } else {
            break;
        }
    }

    Ok(effects)
}

fn parse_signature<'a>(file: &'a str, peek: &mut Tokens) -> Result<(&'a str, FuncSig<'a>)> {
    expect(peek, lexer::TokenType::Fun)?;
    let name = ident(file, peek)?;

    let vec = group(peek, lexer::GroupType::Paren)?;
    let mut input = vec.iter().peekable();

    let mut params = Vec::new();
    while input.peek().is_some() {
        let name = ident(file, &mut input)?;
        let typ = parse_type(file, &mut input)?;

        if input.peek().is_some() {
            expect(&mut input, lexer::TokenType::Comma)?;
        }

        params.push((name, typ));
    }

    // FIXME: assumes types start with an identifier
    let ret = if check(peek, lexer::TokenType::Identifier) {
        Some(parse_type(file, peek)?)
    } else {
        None
    };

    let effects = if check(peek, lexer::TokenType::Slash) {
        expect(peek, lexer::TokenType::Slash)?;
        parse_effects(file, peek)?
    } else {
        vec![]
    };

    Ok((
        name,
        FuncSig {
            params,
            ret,
            effects,
        },
    ))
}

fn parse_effect<'a>(file: &'a str, peek: &mut Tokens, ast: &mut AST<'a>) -> Result<()> {
    expect(peek, lexer::TokenType::Effect)?;
    let name = ident(file, peek)?;

    if check(peek, lexer::TokenType::Equals) {
        // effect alias
        expect(peek, lexer::TokenType::Equals)?;
        let effects = parse_effects(file, peek)?;
        expect(peek, lexer::TokenType::Semicolon)?;

        ast.effects.insert(name, Effect::EffectAlias(effects));
    } else {
        // effect definition
        let vec = group(peek, lexer::GroupType::Brace)?;
        let mut inner = vec.iter().peekable();

        let mut def = EffectDef {
            funcs: HashMap::new(),
        };

        while inner.peek().is_some() {
            ignore(&mut inner, lexer::TokenType::Semicolon);
            let (s, fs) = parse_signature(file, &mut inner)?;
            expect(&mut inner, lexer::TokenType::Semicolon)?;

            def.funcs.insert(s, fs);
        }

        ast.effects.insert(name, Effect::EffectDef(def));
    }

    Ok(())
}
