use do_notation::m;

use crate::err::{ProblemKind, Result};
use crate::module::Module;
use crate::span::{Span, Spanned};
use crate::stage::ast::err::Expected;
use crate::stage::ast::{self, inner};
use crate::stage::token::{Group, Keyword, Literal, Symbol, SymbolAssign, Token, TokenEnum};

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
            TokenEnum::Keyword(Keyword::Fun) => parser.function().map(inner::Definition::Function),
            TokenEnum::Keyword(Keyword::Type) => parser.type_alias().map(inner::Definition::Type),
            TokenEnum::Keyword(Keyword::Effect) => parser.effect().map(inner::Definition::Effect),
            _ => parser.error(Expected::Definition),
        })
    }
    pub fn effect(&mut self) -> Result<ast::Effect> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(Keyword::Effect);
                name <- parser.name();
                _ <- parser.consume(Symbol::Assign(SymbolAssign::Equals));
                definition <- parser.effect_definition();
                return inner::Effect { name, definition };
            }
        })
    }
    pub fn effect_definition(&mut self) -> Result<ast::EffectDefinition> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Open(Group::Brace) => {
                parser.effect_body().map(inner::EffectDefinition::Body)
            }
            _ => parser
                .many_until(&[TokenEnum::Symbol(Symbol::Semicolon)], Parser::path)
                .map(inner::EffectDefinition::Alias),
        })
    }
    pub fn effect_body(&mut self) -> Result<ast::EffectBody> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(TokenEnum::Open(Group::Brace));
                functions <- parser.many(Symbol::Semicolon, Parser::function_declaration);
                _ <- parser.consume(TokenEnum::Close(Group::Brace)).tap_none(|| parser.skip_group(Group::Brace));
                return inner::EffectBody { functions };
            }
        })
    }
    pub fn function(&mut self) -> Result<ast::Function> {
        self.spanned(|parser| {
            m! {
                declaration <- parser.function_declaration();
                _ <- parser.consume(Symbol::Assign(SymbolAssign::Equals));
                definition <- parser.expression();
                return inner::Function { declaration, definition };
            }
        })
    }
    pub fn type_alias(&mut self) -> Result<ast::TypeAlias> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(Keyword::Type);
                name <- parser.name();
                _ <- parser.consume(Symbol::Assign(SymbolAssign::Equals));
                definition <- parser.r#type();
                return inner::TypeAlias { name, definition };
            }
        })
    }
    pub fn path(&mut self) -> Result<ast::Path> {
        self.spanned(|parser| {
            m! {
                first <- parser.ident();
                second <- parser.when_next(Symbol::Dot, |parser| {
                    parser.skip();
                    parser.ident()
                });
                generics <- parser.when_next(TokenEnum::Open(Group::Bracket), |parser| {
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
            TokenEnum::Identifier => parser.path().map(inner::GenericArgument::Path),
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
            TokenEnum::Identifier | TokenEnum::Keyword(Keyword::Struct)
        )
    }
    pub fn r#type(&mut self) -> Result<Box<ast::Type>> {
        self.spanned(|parser| match parser.next().token {
            TokenEnum::Identifier => parser.path().map(|path| {
                if path.package.is_none() && path.name.as_str() == "int" {
                    inner::Type::Int
                } else {
                    inner::Type::Path(path)
                }
            }),
            TokenEnum::Keyword(Keyword::Struct) => parser.r#struct().map(inner::Type::Struct),
            _ => parser.error(Expected::Type),
        })
        .map(Box::new)
    }
    pub fn r#struct(&mut self) -> Result<ast::Struct> {
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(Keyword::Struct);
                members <- parser.many_grouped(Group::Parenthesis, Symbol::Colon, Parser::struct_member);
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
        const DECL_END: &[TokenEnum] = &[
            TokenEnum::Symbol(Symbol::Assign(SymbolAssign::Equals)),
            TokenEnum::Symbol(Symbol::Comma),
            TokenEnum::Symbol(Symbol::Semicolon),
            TokenEnum::Open(Group::Brace),
            TokenEnum::Symbol(Symbol::Slash),
        ];
        self.spanned(|parser| {
            m! {
                _ <- parser.consume(Keyword::Fun);
                name <- parser.name();
                parameters <- parser.when_next(TokenEnum::Open(Group::Parenthesis), |parser| parser.many_grouped(
                    Group::Parenthesis,
                    Symbol::Comma,
                    Parser::function_parameter,
                ));
                returns <- parser.unless_next(
                    DECL_END,
                    Parser::returns
                );
                effects <- parser.when_next(TokenEnum::Symbol(Symbol::Slash), |parser| {
                    parser.skip();
                    parser.many_until(DECL_END, Parser::path)
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
                kind <- parser.unless_next(&[], Parser::kind);
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
    fn unless_next<T>(
        &mut self,
        tokens: &[TokenEnum],
        parse: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        let next = self.next().token;
        if !tokens.contains(&next)
            && !matches!(self.next().token, TokenEnum::Close(_) | TokenEnum::Eof)
        {
            parse(self).map(Some)
        } else {
            Result::new(None)
        }
    }
    fn when_next<T>(
        &mut self,
        token: impl Into<TokenEnum>,
        parse: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        if self.is_next(token) {
            parse(self).map(Some)
        } else {
            Result::new(None)
        }
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
            let has_next =
                pred(self) && !matches!(self.next().token, TokenEnum::Close(_) | TokenEnum::Eof);
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
