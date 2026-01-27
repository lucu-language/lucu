use compact_str::ToCompactString;
use do_notation::m;

use crate::ast;
use crate::error::{ProblemKind, Result};
use crate::module::Module;
use crate::pass::parser::err::Expected;
use crate::tokens::{Group, Keyword, Literal, Symbol, SymbolAssign, Token, TokenEnum};

pub mod err;

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
        m! {
            token <- self.consume(Literal::String);
            return ast::String {
                token,
                value: (&self.source[token.0.inner()]).to_compact_string()
            };
        }
    }
    pub fn ident(&mut self) -> Result<ast::Ident> {
        m! {
            token <- self.consume(TokenEnum::Identifier);
            return ast::Ident {
                token,
                value: (&self.source[token.0]).to_compact_string()
            };
        }
    }
    pub fn import(&mut self) -> Result<ast::Import> {
        m! {
            import <- self.consume(Keyword::Import);
            path <- self.string();
            ident <- self.when_next(TokenEnum::Identifier, Parser::ident);
            return ast::Import { import, path, ident };
        }
    }
    pub fn module(&mut self) -> Result<ast::Module> {
        m! {
            imports <- self.many_while_next(Symbol::Semicolon, Keyword::Import, Parser::import);
            items <- self.many(Symbol::Semicolon, Parser::item);
            return ast::Module { imports, items };
        }
    }
    pub fn item(&mut self) -> Result<ast::Item> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Fun) => {
                m! {
                    declaration <- self.function_declaration();
                    definition <- self.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::function_definition);
                    return ast::Item::Function(declaration, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Type) => {
                m! {
                    let token = self.skip();
                    name <- self.name();
                    definition <- self.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::type_definition);
                    return ast::Item::Type(token, name, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Effect) => {
                m! {
                    let token = self.skip();
                    name <- self.name();
                    definition <- self.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::effect_definition);
                    return ast::Item::Effect(token, name, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Handle) => {
                m! {
                    let token = self.skip();
                    generics <- self.when_next(TokenEnum::Open(Group::Bracket), |parser| parser.many_grouped(
                        Group::Bracket,
                        Symbol::Comma,
                        Parser::generic,
                    ));
                    handler <- self.handler();
                    return ast::Item::Handle(token, generics, handler);
                }
            }
            _ => self.error(Expected::Item),
        }
    }
    pub fn with_effects(&mut self) -> Result<ast::WithEffects> {
        m! {
            with <- self.consume(Keyword::With);
            effects <- self.many_until(&[
                TokenEnum::Open(Group::Brace),
                TokenEnum::Symbol(Symbol::Semicolon),
                TokenEnum::Symbol(Symbol::Comma),
                TokenEnum::Symbol(Symbol::Assign(SymbolAssign::Equals)),
            ], |parser| parser.path(false));
            return ast::WithEffects { with, effects };
        }
    }
    pub fn handler(&mut self) -> Result<ast::Handler> {
        m! {
            effect <- self.path(false);
            with_effects <- self.when_next(Keyword::With, Parser::with_effects);
            items <- self.many_grouped(Group::Brace, Symbol::Semicolon, Parser::item);
            return ast::Handler { effect, with_effects, items };
        }
    }
    pub fn effect_definition(&mut self) -> Result<ast::EffectDefinition> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                Result::new(ast::EffectDefinition::Intrinsic(self.skip()))
            }
            TokenEnum::Open(Group::Brace) => self.effect_body().map(ast::EffectDefinition::Body),
            _ => self
                .many_until(&[TokenEnum::Symbol(Symbol::Semicolon)], |parser| {
                    parser.path(false)
                })
                .map(ast::EffectDefinition::Alias),
        }
    }
    pub fn effect_body(&mut self) -> Result<ast::EffectBody> {
        self.many_grouped(Group::Brace, Symbol::Semicolon, Parser::item)
            .map(|items| ast::EffectBody { items })
    }
    pub fn function_definition(&mut self) -> Result<ast::FunctionDefinition> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                Result::new(ast::FunctionDefinition::Intrinsic(self.skip()))
            }
            _ => self.expression().map(ast::FunctionDefinition::Expression),
        }
    }
    pub fn type_definition(&mut self) -> Result<ast::TypeDefinition> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                Result::new(ast::TypeDefinition::Intrinsic(self.skip()))
            }
            TokenEnum::Keyword(Keyword::Struct) => self.r#struct().map(ast::TypeDefinition::Struct),
            _ => self.r#type().map(ast::TypeDefinition::Type),
        }
    }
    pub fn path(&mut self, may_precede_type: bool) -> Result<ast::Path> {
        m! {
            first <- self.ident();
            second <- self.consume_next(Symbol::Dot, Parser::ident);
            generics <-
                self.when(
                    |parser| {
                        // There is an ambiguous statement in the language.
                        // ^@R[..]T can be parsed as:
                        //  - ^@(R[..]) T  where R is a region function
                        //  - ^@R ([..]T)  where the pointee is an array
                        //
                        // To fix this, we enforce that the generic arguments MUST be
                        // adjacent to the region function, with no whitespace inbetween.
                        // Otherwise, we assume the pointee is some kind of array.
                        parser.is_next(TokenEnum::Open(Group::Bracket))
                            && (!may_precede_type || parser.last_token_end == parser.next().span.start)
                    },
                    |parser| {
                        parser.many_grouped(Group::Bracket, Symbol::Comma, Parser::generic_argument)
                    },
                );
            return match second {
                Some((dot, name)) => ast::Path { package: Some((first, dot)), name, generics },
                None => ast::Path { package: None, name: first, generics },
            };
        }
    }
    pub fn generic_argument(&mut self) -> Result<ast::GenericArgument> {
        match self.next().token {
            TokenEnum::Identifier => self.path(false).map(ast::GenericArgument::Path),
            _ if self.starts_type() => self.r#type().map(ast::GenericArgument::Type),
            _ if self.starts_constant() => self.constant().map(ast::GenericArgument::Constant),
            _ => self.error(Expected::GenericArgument),
        }
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
    pub fn pointer_region(&mut self) -> Result<ast::PointerRegion> {
        m! {
            at <- self.consume(Symbol::At);
            region <- self.path(true);
            return ast::PointerRegion { at, region };
        }
    }
    pub fn r#type(&mut self) -> Result<Box<ast::Type>> {
        match self.next().token {
            TokenEnum::Identifier => self.path(false).map(ast::Type::Path),
            TokenEnum::Symbol(Symbol::Caret) => {
                // Pointer
                let pointer = self.skip();
                self.when_next(Symbol::At, Parser::pointer_region).and_then(|region| {
                    if self.is_next(TokenEnum::Open(Group::Bracket)) && self.starts_slice() {
                        // Pointer to some slice
                        let open = self.skip();
                        match self.next().token {
                            TokenEnum::Close(Group::Bracket) => {
                                // Pointer to slice
                                m! {
                                    let close = self.skip();
                                    let grouped = ast::Grouped { open, inner: (), close };
                                    inner <- self.r#type();
                                    return ast::Type::PointerSlice(pointer, grouped, region, inner);
                                }
                            }
                            TokenEnum::Symbol(Symbol::Colon) => {
                                // Pointer to null-terminated slice
                                m! {
                                    let colon = self.skip();
                                    zero <- self.consume(Literal::Zero).tap_none(|| self.skip_group(Group::Bracket));
                                    close <- self.consume(TokenEnum::Close(Group::Bracket)).tap_none(|| self.skip_group(Group::Bracket));
                                    let grouped = ast::Grouped { open, inner: ast::NullTerminated { colon, zero }, close };
                                    inner <- self.r#type();
                                    return ast::Type::PointerSliceNullTerminated(pointer, grouped, region, inner);
                                }
                            }
                            _ => unreachable!(),
                        }
                    } else {
                        // Pointer to non-slice
                        m! {
                            inner <- self.r#type();
                            return ast::Type::Pointer(pointer, region, inner);
                        }
                    }
                })
            }
            TokenEnum::Open(Group::Bracket) => {
                if self.starts_slice() {
                    todo!("error: needs pointer syntax")
                }
                todo!("constant sized array")
            }
            _ => self.error(Expected::Type),
        }
        .map(Box::new)
    }
    pub fn r#struct(&mut self) -> Result<ast::Struct> {
        m! {
            r#struct <- self.consume(Keyword::Struct);
            members <- self.many_grouped(Group::Parenthesis, Symbol::Comma, Parser::struct_member);
            return ast::Struct { r#struct, members };
        }
    }
    pub fn struct_member(&mut self) -> Result<ast::StructMember> {
        m! {
            name <- self.ident();
            ty <- self.r#type();
            return ast::StructMember::Data(name, ty);
        }
    }
    pub fn expression(&mut self) -> Result<Box<ast::Expression>> {
        m! {
            open <- self.consume(TokenEnum::Open(Group::Brace));
            close <- self.consume(TokenEnum::Close(Group::Brace)).tap_none(|| self.skip_group(Group::Brace));
            return ast::Expression::Block(ast::Grouped { open, inner: (), close });
        }
        .map(Box::new)
    }
    pub fn parameter(&mut self) -> Result<ast::Parameter> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Fun) => {
                self.function_declaration().map(ast::Parameter::Lambda)
            }
            TokenEnum::Identifier => {
                m! {
                    name <- self.ident();
                    ty <- self.r#type();
                    return ast::Parameter::Data(name, ty);
                }
            }
            _ => self.error(Expected::Parameter),
        }
    }
    pub fn function_declaration(&mut self) -> Result<ast::FunctionDeclaration> {
        m! {
            fun <- self.consume(Keyword::Fun);
            name <- self.name();
            parameters <- self.when_next(TokenEnum::Open(Group::Parenthesis), |parser| parser.many_grouped(
                Group::Parenthesis,
                Symbol::Comma,
                Parser::parameter,
            ));
            returns <- self.when(Parser::starts_type, Parser::returns);
            effects <- self.when_next(TokenEnum::Keyword(Keyword::With), Parser::with_effects);
            return ast::FunctionDeclaration { fun, name, parameters, returns, effects };
        }
    }
    pub fn returns(&mut self) -> Result<ast::Returns> {
        match self.next().token {
            TokenEnum::Symbol(Symbol::Bang) => Result::new(ast::Returns::Never(self.skip())),
            _ => {
                if self.starts_type() {
                    self.r#type().map(ast::Returns::Data)
                } else {
                    self.error(Expected::Returns)
                }
            }
        }
    }
    pub fn name(&mut self) -> Result<ast::Name> {
        m! {
            ident <- self.ident();
            generics <- self.when_next(TokenEnum::Open(Group::Bracket), |parser| parser.many_grouped(
                Group::Bracket,
                Symbol::Comma,
                Parser::generic,
            ));
            return ast::Name { ident, generics };
        }
    }
    pub fn generic(&mut self) -> Result<ast::GenericParameter> {
        m! {
            name <- self.name();
            kind <- self.unless_next(&[TokenEnum::Symbol(Symbol::Comma)], Parser::kind);
            return ast::GenericParameter { name, kind };
        }
    }
    pub fn kind(&mut self) -> Result<ast::Kind> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Type) => Result::new(ast::Kind::Type(self.skip())),
            TokenEnum::Keyword(Keyword::Effect) => Result::new(ast::Kind::Effect(self.skip())),
            TokenEnum::Keyword(Keyword::Region) => Result::new(ast::Kind::Region(self.skip())),
            _ => {
                if self.starts_type() {
                    self.r#type().map(ast::Kind::Constant)
                } else {
                    self.error(Expected::Kind)
                }
            }
        }
    }

    fn consume(&mut self, token: impl Into<TokenEnum>) -> Result<ast::Token> {
        let token = token.into();
        match self.tokens.split_first().expect("ICE: consumed EOF token") {
            (next, rest) if next.token == token => {
                self.tokens = rest;
                self.last_token_end = next.span.end;
                Result::new(ast::Token(next.span))
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
    fn skip(&mut self) -> ast::Token {
        let (token, tokens) = self.tokens.split_first().expect("ICE: consumed EOF token");
        self.tokens = tokens;
        self.last_token_end = token.span.end;
        ast::Token(token.span)
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
    ) -> Result<Option<(ast::Token, T)>> {
        self.when_next(token, |parser| {
            let token = parser.skip();
            parse(parser).map(|t| (token, t))
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
                _ => {
                    self.skip();
                }
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
                _ => {
                    self.skip();
                }
            }
        }
    }
    fn many_grouped<T>(
        &mut self,
        group: Group,
        separator: Symbol,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Grouped<ast::Separated<T>>> {
        m! {
            open <- self.consume(TokenEnum::Open(group));
            inner <- self.many(separator, parse).tap_none(|| self.skip_group(group));
            close <- self.consume(TokenEnum::Close(group)).tap_none(|| self.skip_group(group));
            return ast::Grouped { open, inner, close };
        }
    }
    fn many<T>(
        &mut self,
        separator: Symbol,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Separated<T>> {
        self.many_while(separator, |_| true, parse)
    }
    fn many_while_next<T>(
        &mut self,
        separator: Symbol,
        token: impl Into<TokenEnum>,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Separated<T>> {
        let token = token.into();
        self.many_while(separator, |me| me.is_next(token), parse)
    }
    fn many_while<T>(
        &mut self,
        separator: Symbol,
        pred: impl Fn(&Self) -> bool,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Separated<T>> {
        std::iter::from_fn(|| {
            let next = self.next().token;
            let has_next = pred(self) && !matches!(next, TokenEnum::Close(_) | TokenEnum::Eof);
            has_next.then(|| {
                let parser = &mut *self;
                m! {
                    t <- parse(parser)
                        .tap_none(|| parser.skip_to_recovery(separator, &[]));
                    sep <- parser.unless_next(&[], |parser| parser.consume(separator)
                        .tap_none(|| parser.skip_to_recovery(separator, &[])).recover());
                    return (t, sep.flatten());
                }
            })
        })
        .collect::<Result<Vec<_>>>()
        .map(|elements| ast::Separated { elements })
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
