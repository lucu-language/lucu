use do_notation::m;

use crate::ast::{self, inner};
use crate::error::{ProblemKind, Result};
use crate::module::Module;
use crate::pass::parser::err::Expected;
use crate::span::{Span, Spanned};
use crate::tokens::{Group, Keyword, Literal, Symbol, SymbolAssign, Token, TokenEnum};

pub mod err;

#[derive(Clone, Copy)]
pub struct Parser<'a> {
    module: &'a Module,
    source: &'a str,
    last_token_end: u32,
    tokens: &'a [Token],
}

impl<'a> Parser<'a> {
    pub fn new(module: &'a Module, source: &'a str, tokens: &'a [Token]) -> Self {
        Self {
            module,
            source,
            tokens,
            last_token_end: 0,
        }
    }

    pub fn string(&mut self) -> Result<ast::String> {
        self.consume(Literal::String).map(|tok| {
            Spanned(
                inner::String((&self.source[tok.span.inner()]).into()),
                tok.span,
            )
        })
    }
    pub fn ident(&mut self) -> Result<ast::Ident> {
        self.consume(TokenEnum::Identifier)
            .map(|tok| Spanned(inner::Ident((&self.source[tok.span]).into()), tok.span))
    }
    pub fn import(&mut self) -> Result<ast::Import> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(Keyword::Import);
                path <- parser.string();
                ident <- parser.when_next(TokenEnum::Identifier, Parser::ident);
                return inner::Import { path, ident };
            }
        })
    }
    pub fn module(&mut self) -> Result<ast::Module> {
        self.spanned(|parser| {
            m! {
                imports <- parser.many_while_next(Symbol::Semicolon, Keyword::Import, Parser::import);
                definitions <- parser.many(Symbol::Semicolon, Parser::definition);
                return inner::Module { imports, definitions };
            }
        })
    }
    pub fn definition(&mut self) -> Result<ast::Definition> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Keyword(Keyword::Fun) => {
                m! {
                    declaration <- parser.function_declaration();
                    definition <- parser.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::function_definition);
                    return inner::Definition::Function(declaration, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Type) => {
                m! {
                    _ <- parser.consume(Keyword::Type);
                    name <- parser.name();
                    definition <- parser.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::type_definition);
                    return inner::Definition::Type(name, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Effect) => {
                m! {
                    _ <- parser.consume(Keyword::Effect);
                    name <- parser.name();
                    definition <- parser.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::effect_definition);
                    return inner::Definition::Effect(name, definition);
                }
            },
            _ => parser.error(Expected::Definition),
        })
    }
    pub fn effect_definition(&mut self) -> Result<ast::EffectDefinition> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                parser.skip();
                Result::new(inner::EffectDefinition::Intrinsic)
            }
            TokenEnum::Open(Group::Brace) => {
                parser.effect_body().map(inner::EffectDefinition::Body)
            }
            _ => parser
                .many_until(&[TokenEnum::Symbol(Symbol::Semicolon)], |parser| {
                    parser.path(false)
                })
                .map(inner::EffectDefinition::Alias),
        })
    }
    pub fn effect_body(&mut self) -> Result<ast::EffectBody> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(TokenEnum::Open(Group::Brace));
                definitions <- parser.many(Symbol::Semicolon, Parser::definition);
                _ <- parser.consume(TokenEnum::Close(Group::Brace)).tap_none(|| parser.skip_group(Group::Brace));
                return inner::EffectBody { definitions };
            }
        })
    }
    pub fn function_definition(&mut self) -> Result<ast::FunctionDefinition> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                parser.skip();
                Result::new(inner::FunctionDefinition::Intrinsic)
            }
            _ => parser
                .expression()
                .map(inner::FunctionDefinition::Expression),
        })
    }
    pub fn type_definition(&mut self) -> Result<ast::TypeDefinition> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                parser.skip();
                Result::new(inner::TypeDefinition::Intrinsic)
            }
            TokenEnum::Keyword(Keyword::Struct) => {
                parser.r#struct().map(inner::TypeDefinition::Struct)
            }
            _ => parser.r#type().map(inner::TypeDefinition::Type),
        })
    }
    fn starts_generic_arguments(&self, may_have_type_afterwards: bool) -> bool {
        if self.is_next(TokenEnum::Open(Group::Bracket)) {
            if may_have_type_afterwards {
                let mut copy = *self;
                copy.skip();
                copy.skip_group(Group::Bracket);
                !copy.starts_type()
            } else {
                true
            }
        } else {
            false
        }
    }
    pub fn path(&mut self, may_have_type_afterwards: bool) -> Result<ast::Path> {
        self.spanned(|parser| {
            m! {
                first <- parser.ident();
                second <- parser.consume_next(Symbol::Dot, Parser::ident);
                generics <- parser.when(|parser| parser.starts_generic_arguments(may_have_type_afterwards), |parser| {
                    parser.many_grouped(Group::Bracket, Symbol::Comma, Parser::generic_argument)
                });
                return match second {
                    Some(name) => inner::Path { package: Some(first), name, generics },
                    None => inner::Path { package: None, name: first, generics },
                };
            }
        })
    }
    pub fn generic_argument(&mut self) -> Result<ast::GenericArgument> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Identifier => parser.path(false).map(inner::GenericArgument::Path),
            _ if parser.starts_type() => parser.r#type().map(inner::GenericArgument::Type),
            _ if parser.starts_constant() => {
                parser.constant().map(inner::GenericArgument::Constant)
            }
            _ => parser.error(Expected::GenericArgument),
        })
    }
    fn starts_constant(&self) -> bool {
        false
    }
    pub fn constant(&mut self) -> Result<Box<ast::Constant>> {
        todo!()
    }
    fn starts_type(&self) -> bool {
        matches!(
            self.next().token,
            TokenEnum::Identifier
                | TokenEnum::Symbol(Symbol::Caret)
                | TokenEnum::Open(Group::Bracket)
                // not really types, but we count them
                | TokenEnum::Symbol(Symbol::Bang)
                | TokenEnum::Keyword(Keyword::Struct)
        )
    }
    fn starts_slice(&self) -> bool {
        matches!(
            self.tokens.get(1).map(|t| t.token),
            Some(
                // slice
                TokenEnum::Close(Group::Bracket) |
                // null terminated slice
                TokenEnum::Symbol(Symbol::Colon)
            )
        )
    }
    pub fn r#type(&mut self) -> Result<Box<ast::Type>> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Identifier => parser.path(false).map(inner::Type::Path),
            TokenEnum::Symbol(Symbol::Caret) => {
                // Pointer
                parser.skip();
                parser.consume_next(Symbol::At, |parser| parser.path(true)).and_then(|region| {
                    if parser.is_next(TokenEnum::Open(Group::Bracket)) && parser.starts_slice() {
                        // Pointer to some slice
                        parser.skip();
                        match parser.next().token {
                            TokenEnum::Close(Group::Bracket) => {
                                // Pointer to slice
                                parser.skip();
                                m! {
                                    inner <- parser.r#type();
                                    return inner::Type::PointerSlice(inner, region);
                                }
                            }
                            TokenEnum::Symbol(Symbol::Colon) => {
                                // Pointer to null-terminated slice
                                parser.skip();
                                m! {
                                    _ <- parser.consume(Literal::Zero);
                                    _ <- parser.consume(TokenEnum::Close(Group::Bracket)).tap_none(|| parser.skip_group(Group::Bracket));
                                    inner <- parser.r#type();
                                    return inner::Type::PointerSliceNullTerminated(inner, region);
                                }
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        // Pointer to non-slice
                        m! {
                            inner <- parser.r#type();
                            return inner::Type::Pointer(inner, region);
                        }
                    }
                })
            }
            TokenEnum::Open(Group::Bracket) => {
                if parser.starts_slice() {
                    todo!("error: needs pointer syntax")
                }
                todo!("constant sized array")
            }
            _ => parser.error(Expected::Type),
        })
        .map(Box::new)
    }
    pub fn r#struct(&mut self) -> Result<ast::Struct> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(Keyword::Struct);
                members <- parser.many_grouped(Group::Parenthesis, Symbol::Comma, Parser::struct_member);
                return inner::Struct { members };
            }
        })
    }
    pub fn struct_member(&mut self) -> Result<ast::StructMember> {
        self.spanned(|parser| {
            m! {
                name <- parser.ident();
                ty <- parser.r#type();
                return inner::StructMember::Data(name, ty);
            }
        })
    }
    pub fn expression(&mut self) -> Result<Box<ast::Expression>> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(TokenEnum::Open(Group::Brace));
                _ <- parser.consume(TokenEnum::Close(Group::Brace)).tap_none(|| parser.skip_group(Group::Brace));
                return inner::Expression::Block;
            }
        })
        .map(Box::new)
    }
    pub fn function_parameter(&mut self) -> Result<ast::FunctionParameter> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Keyword(Keyword::Fun) => parser
                .function_declaration()
                .map(inner::FunctionParameter::Lambda),
            TokenEnum::Identifier => {
                m! {
                    name <- parser.ident();
                    ty <- parser.r#type();
                    return inner::FunctionParameter::Data(name, ty);
                }
            }
            _ => parser.error(Expected::FunctionParameter),
        })
    }
    pub fn function_declaration(&mut self) -> Result<ast::FunctionDeclaration> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(Keyword::Fun);
                name <- parser.name();
                parameters <- parser.when_next(TokenEnum::Open(Group::Parenthesis), |parser| parser.many_grouped(
                    Group::Parenthesis,
                    Symbol::Comma,
                    Parser::function_parameter,
                ));
                returns <- parser.when(Parser::starts_type, Parser::returns);
                effects <- parser.consume_next(TokenEnum::Keyword(Keyword::With), |parser| {
                    parser.many_until(&[
                        TokenEnum::Symbol(Symbol::Assign(SymbolAssign::Equals)),
                        TokenEnum::Symbol(Symbol::Semicolon),
                        TokenEnum::Symbol(Symbol::Comma),
                        // not a valid next token, but it improves the error
                        TokenEnum::Open(Group::Brace),
                    ], |parser| parser.path(false))
                });
                return inner::FunctionDeclaration { name, parameters, returns, effects };
            }
        })
    }
    pub fn returns(&mut self) -> Result<ast::Returns> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Symbol(Symbol::Bang) => {
                parser.skip();
                Result::new(inner::Returns::Never)
            }
            _ => {
                if parser.starts_type() {
                    parser.r#type().map(inner::Returns::Data)
                } else {
                    parser.error(Expected::Returns)
                }
            }
        })
    }
    pub fn name(&mut self) -> Result<ast::Name> {
        self.spanned(|parser| {
            m! {
                ident <- parser.ident();
                generics <- parser.when_next(TokenEnum::Open(Group::Bracket), |parser| parser.many_grouped(
                    Group::Bracket,
                    Symbol::Comma,
                    Parser::generic,
                ));
                return inner::Name { ident, generics };
            }
        })
    }
    pub fn generic(&mut self) -> Result<ast::GenericParameter> {
        self.spanned(|parser| {
            m! {
                name <- parser.name();
                kind <- parser.unless_next(&[TokenEnum::Symbol(Symbol::Comma)], Parser::kind);
                return inner::GenericParameter { name, kind };
            }
        })
    }
    pub fn kind(&mut self) -> Result<ast::Kind> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Keyword(Keyword::Type) => {
                parser.skip();
                Result::new(inner::Kind::Type)
            }
            TokenEnum::Keyword(Keyword::Effect) => {
                parser.skip();
                Result::new(inner::Kind::Effect)
            }
            TokenEnum::Keyword(Keyword::Region) => {
                parser.skip();
                Result::new(inner::Kind::Region)
            }
            _ => {
                if parser.starts_type() {
                    parser.r#type().map(inner::Kind::Constant)
                } else {
                    parser.error(Expected::Kind)
                }
            }
        })
    }

    fn spanned<T>(&mut self, parse: impl FnOnce(&mut Self) -> Result<T>) -> Result<Spanned<T>> {
        self.with_span(|parser| parse(parser).map(|t| |span| Spanned(t, span)))
    }
    fn with_span<T, F>(&mut self, parse: impl FnOnce(&mut Self) -> Result<F>) -> Result<T>
    where
        F: FnOnce(Span) -> T,
    {
        let start = self.next().span.start;
        parse(self).map(|t| t(Span::new(start, self.last_token_end)))
    }
    fn consume(&mut self, token: impl Into<TokenEnum>) -> Result<Token> {
        let token = token.into();
        match self.tokens.split_first().expect("ICE: consumed EOF token") {
            (next, rest) if next.token == token => {
                self.tokens = rest;
                self.last_token_end = next.span.end;
                Result::new(*next)
            }
            _ => self.error(Expected::Token(token)),
        }
    }
    fn error<T>(&self, expected: Expected) -> Result<T> {
        let next = self.next();
        let error = if next.is_eof() {
            ProblemKind::UnexpectedEOF(expected)
        } else if next.is_newline() {
            ProblemKind::UnexpectedNewline(expected)
        } else {
            ProblemKind::UnexpectedToken(expected)
        };
        Result::error(error.at(self.module, &next))
    }
    fn skip(&mut self) {
        let (token, tokens) = self.tokens.split_first().expect("ICE: consumed EOF token");
        self.tokens = tokens;
        self.last_token_end = token.span.end;
    }
    fn next(&self) -> Token {
        self.tokens
            .first()
            .copied()
            .expect("ICE: consumed EOF token")
    }
    fn is_next(&self, token: impl Into<TokenEnum>) -> bool {
        self.next().token == token.into()
    }
    fn when<T>(
        &mut self,
        p: impl FnOnce(&Self) -> bool,
        parse: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        if p(self) {
            parse(self).map(Some)
        } else {
            Result::new(None)
        }
    }
    fn unless_next<T>(
        &mut self,
        tokens: &[TokenEnum],
        parse: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        self.when(
            |parser| {
                let next = parser.next().token;
                !tokens.contains(&next) && !matches!(next, TokenEnum::Close(_) | TokenEnum::Eof)
            },
            parse,
        )
    }
    fn when_next<T>(
        &mut self,
        token: impl Into<TokenEnum>,
        parse: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        self.when(|parser| parser.is_next(token), parse)
    }
    fn consume_next<T>(
        &mut self,
        token: impl Into<TokenEnum>,
        parse: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        self.when_next(token, |parser| {
            parser.skip();
            parse(parser)
        })
    }
    fn skip_group(&mut self, group: Group) {
        loop {
            match self.next().token {
                TokenEnum::Eof => break,
                TokenEnum::Close(c) => {
                    if c == group {
                        self.skip();
                    }
                    break;
                }
                TokenEnum::Open(group) => {
                    self.skip();
                    self.skip_group(group)
                }
                _ => self.skip(),
            }
        }
    }
    fn skip_to_recovery(&mut self, sep: Symbol, until: &[TokenEnum]) {
        loop {
            match self.next().token {
                t if until.contains(&t) => {
                    break;
                }
                TokenEnum::Symbol(sym) if sym == sep => {
                    self.skip();
                    break;
                }
                TokenEnum::Close(_) | TokenEnum::Eof => break,
                TokenEnum::Open(group) => {
                    self.skip();
                    self.skip_group(group)
                }
                _ => self.skip(),
            }
        }
    }
    fn many_grouped<T>(
        &mut self,
        group: Group,
        separator: Symbol,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        m! {
            _ <- self.consume(TokenEnum::Open(group));
            many <- self.many(separator, parse).tap_none(|| self.skip_group(group));
            _ <- self.consume(TokenEnum::Close(group));
            return many;
        }
    }
    fn many<T>(
        &mut self,
        separator: Symbol,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        self.many_while(separator, |_| true, parse)
    }
    fn many_while_next<T>(
        &mut self,
        separator: Symbol,
        token: impl Into<TokenEnum>,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        let token = token.into();
        self.many_while(separator, |me| me.is_next(token), parse)
    }
    fn many_while<T>(
        &mut self,
        separator: Symbol,
        pred: impl Fn(&Self) -> bool,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        std::iter::from_fn(|| {
            let next = self.next().token;
            let has_next = pred(self) && !matches!(next, TokenEnum::Close(_) | TokenEnum::Eof);
            has_next.then(|| {
                let parser = &mut *self;
                m! {
                    t <- parse(parser)
                        .tap_none(|| parser.skip_to_recovery(separator, &[]));
                    _ <- parser.unless_next(&[], |parser| parser.consume(separator)
                        .tap_none(|| parser.skip_to_recovery(separator, &[])).recover());
                    return t;
                }
            })
        })
        .collect()
    }
    fn many_until<T>(
        &mut self,
        until: &[TokenEnum],
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        std::iter::from_fn(|| {
            let next = self.next().token;
            let has_next =
                !until.contains(&next) && !matches!(next, TokenEnum::Close(_) | TokenEnum::Eof);
            has_next
                .then(|| parse(self).tap_none(|| self.skip_to_recovery(Symbol::Semicolon, until)))
        })
        .collect()
    }
}
