use compact_str::{CompactString, ToCompactString};
use do_notation::m;

use crate::ast;
use crate::error::{Problem, ProblemKind, Result};
use crate::module::Module;
use crate::pass::parser::err::Expected;
use crate::tokens::{Group, Keyword, Literal, Symbol, SymbolAssign, Token, TokenEnum};

pub mod err;
mod expr;

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
    pub fn character(&mut self) -> Result<ast::Character> {
        m! {
            token <- self.consume(Literal::Character);
            return ast::Character {
                token,
                value: (&self.source[token.0.inner()]).to_compact_string()
            };
        }
    }
    pub fn integer(&mut self) -> Result<ast::Integer> {
        match self.next().token {
            TokenEnum::Literal(Literal::Zero) => Result::new(ast::Integer {
                token: self.skip(),
                value: 0,
            }),
            TokenEnum::Literal(Literal::Integer) => {
                let token = self.skip();
                let value = self.source[token.0]
                    .parse()
                    .expect("ICE: could not parse lexed integer");
                Result::new(ast::Integer { token, value })
            }
            _ => self.error(Expected::Token(TokenEnum::Literal(Literal::Integer))),
        }
    }
    pub fn ident(&mut self) -> Result<ast::Identifier> {
        m! {
            token <- self.consume(TokenEnum::Identifier);
            return ast::Identifier {
                token,
                value: (&self.source[token.0]).to_compact_string()
            };
        }
    }
    pub fn ident_or_underscore(&mut self) -> Result<ast::Identifier> {
        if self.is_next(TokenEnum::Underscore) {
            Result::new(ast::Identifier {
                token: self.skip(),
                value: CompactString::new(""),
            })
        } else {
            self.ident()
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
            imports <- self.many_while_next(Symbol::Semicolon.into(), Keyword::Import, Parser::import);
            items <- self.many(Symbol::Semicolon.into(), Parser::item);
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
                    name <- self.name(false);
                    definition <- self.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::type_definition);
                    return ast::Item::Type(token, name, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Effect) => {
                m! {
                    let token = self.skip();
                    name <- self.name(false);
                    definition <- self.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::effect_definition);
                    return ast::Item::Effect(token, name, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Region) => {
                m! {
                    let token = self.skip();
                    name <- self.name(false);
                    definition <- self.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::region_definition);
                    return ast::Item::Region(token, name, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Const) => {
                m! {
                    let token = self.skip();
                    name <- self.name(false);
                    ty <- self.r#type();
                    definition <- self.consume_next(Symbol::Assign(SymbolAssign::Equals), Parser::constant_definition);
                    return ast::Item::Constant(token, name, ty, definition);
                }
            }
            TokenEnum::Keyword(Keyword::Handle) => {
                m! {
                    let token = self.skip();
                    generics <- self.when_next(TokenEnum::Open(Group::Bracket), |parser| parser.many_grouped(
                        Group::Bracket,
                        Symbol::Comma.into(),
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
            items <- self.many_grouped(Group::Brace, Symbol::Semicolon.into(), Parser::item);
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
                .require(|v| !v.is_empty(), |_| self.problem(Expected::Effect))
                .map(ast::EffectDefinition::Alias),
        }
    }
    pub fn region_definition(&mut self) -> Result<ast::RegionDefinition> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                Result::new(ast::RegionDefinition::Intrinsic(self.skip()))
            }
            _ => self.path(false).map(ast::RegionDefinition::Alias),
        }
    }
    pub fn constant_definition(&mut self) -> Result<ast::ConstantDefinition> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                Result::new(ast::ConstantDefinition::Intrinsic(self.skip()))
            }
            _ => self
                .constant(Expected::Constant)
                .map(ast::ConstantDefinition::Constant),
        }
    }
    pub fn effect_body(&mut self) -> Result<ast::EffectBody> {
        self.many_grouped(Group::Brace, Symbol::Semicolon.into(), Parser::item)
            .map(|items| ast::EffectBody { items })
    }
    pub fn function_definition(&mut self) -> Result<ast::FunctionDefinition> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Intrinsic) => {
                Result::new(ast::FunctionDefinition::Intrinsic(self.skip()))
            }
            _ => self
                .expression(true)
                .map(ast::FunctionDefinition::Expression),
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
    pub fn path_origin(&mut self) -> Result<ast::PathOrigin> {
        if self.is_next(TokenEnum::Underscore) {
            Result::new(ast::PathOrigin::Underscore(self.skip()))
        } else {
            m! {
                first <- self.ident();
                second <- self.consume_next(Symbol::Dot, Parser::ident);
                return match second {
                    Some((dot, name)) => ast::PathOrigin::Package(first, dot, name),
                    None => ast::PathOrigin::Local(first),
                };
            }
        }
    }
    pub fn path(&mut self, may_precede_type: bool) -> Result<ast::Path> {
        m! {
            origin <- self.path_origin();
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
                        parser.many_grouped(Group::Bracket, Symbol::Comma.into(), Parser::generic_argument)
                    },
                );
            return ast::Path { origin, generics };
        }
    }
    pub fn generic_argument(&mut self) -> Result<ast::GenericArgument> {
        // TODO: array constants
        match self.next().token {
            TokenEnum::Identifier | TokenEnum::Underscore => {
                m! {
                    path <- self.path(false);
                    effects <- self.when_next(Keyword::With, Parser::with_effects);
                    return ast::GenericArgument::Path(path, effects);
                }
            }
            _ if self.starts_type() => {
                m! {
                    ty <- self.r#type();
                    effects <- self.when_next(Keyword::With, Parser::with_effects);
                    return ast::GenericArgument::Type(ty, effects);
                }
            }
            _ if self.starts_constant() => self
                .constant(Expected::Constant)
                .map(ast::GenericArgument::Constant),
            _ => self.error(Expected::GenericArgument),
        }
    }
    fn starts_constant(&self) -> bool {
        matches!(
            self.next().token,
            TokenEnum::Identifier | TokenEnum::Underscore | TokenEnum::Literal(_)
        )
    }
    fn starts_type(&self) -> bool {
        matches!(
            self.next().token,
            TokenEnum::Identifier | TokenEnum::Underscore
                | TokenEnum::Symbol(Symbol::Caret)
                | TokenEnum::Open(Group::Bracket)
                // not really types, but we count them
                | TokenEnum::Symbol(Symbol::Bang)
                | TokenEnum::Keyword(Keyword::Struct)
        )
    }
    fn starts_region_kind(&self) -> bool {
        matches!(
            self.next().token,
            TokenEnum::Keyword(Keyword::Mut)
                // not really, but we count them
                | TokenEnum::Symbol(Symbol::At)
        )
    }
    fn starts_pointer_region(&self) -> bool {
        matches!(self.next().token, TokenEnum::Symbol(Symbol::At)) || self.starts_region_kind()
    }
    pub fn region_kind(&mut self) -> Result<ast::RegionKind> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Mut) => Result::new(ast::RegionKind::Mutable(self.skip())),
            _ => self.error(Expected::RegionKind),
        }
    }
    pub fn pointer_region(&mut self) -> Result<ast::PointerRegion> {
        match self.next().token {
            TokenEnum::Symbol(Symbol::At) => {
                m! {
                    let at = self.skip();
                    region <- self.path(true);
                    return ast::PointerRegion::At(at, region);
                }
            }
            _ if self.starts_region_kind() => self.region_kind().map(ast::PointerRegion::Kind),
            _ => self.error(Expected::PointerRegion),
        }
    }
    pub fn sentinel(&mut self) -> Result<ast::Sentinel> {
        m! {
            colon <- self.consume(Symbol::Colon);
            zero <- self.consume(Literal::Zero);
            return ast::Sentinel { colon, zero };
        }
    }
    pub fn array_properties(&mut self) -> Result<ast::ArrayProperties> {
        m! {
            size <- self.unless_next(&[TokenEnum::Symbol(Symbol::Colon)], |parser| parser.constant(Expected::UsizeConstant));
            sentinel <- self.when_next(Symbol::Colon, Parser::sentinel);
            let end = self.last_token_end;
            return ast::ArrayProperties { size, sentinel, end };
        }
    }
    pub fn constant(&mut self, expected: Expected) -> Result<Box<ast::Constant>> {
        match self.next().token {
            TokenEnum::Identifier | TokenEnum::Underscore => {
                self.path(false).map(ast::Constant::Path)
            }
            TokenEnum::Literal(l) => match l {
                Literal::String => self.string().map(ast::Constant::String),
                Literal::Character => self.character().map(ast::Constant::Character),
                Literal::Integer => self.integer().map(ast::Constant::Integer),
                Literal::Zero => Result::new(ast::Constant::Zero(self.skip())),
            },
            _ => self.error(expected),
        }
        .map(Box::new)
    }
    pub fn r#type(&mut self) -> Result<Box<ast::Type>> {
        match self.next().token {
            TokenEnum::Identifier | TokenEnum::Underscore => self.path(false).map(ast::Type::Path),
            TokenEnum::Symbol(Symbol::Question) => {
                // Maybe
                m! {
                    let maybe = self.skip();
                    inner <- self.r#type();
                    return ast::Type::Maybe(maybe, inner);
                }
            }
            TokenEnum::Symbol(Symbol::Caret) => {
                // Pointer
                m! {
                    let pointer = self.skip();
                    region <- self.when(Parser::starts_pointer_region, Parser::pointer_region);
                    inner <- self.r#type();
                    return ast::Type::Pointer(pointer, region, inner);
                }
            }
            TokenEnum::Open(Group::Bracket) => {
                // Array
                m! {
                    properties <- self.grouped(Group::Bracket, Parser::array_properties);
                    inner <- self.r#type();
                    return ast::Type::Array(properties, inner);
                }
            }
            _ => self.error(Expected::Type),
        }
        .map(Box::new)
    }
    pub fn r#struct(&mut self) -> Result<ast::Struct> {
        m! {
            r#struct <- self.consume(Keyword::Struct);
            members <- self.many_grouped(Group::Parenthesis, Symbol::Comma.into(), Parser::struct_member);
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
    pub fn parameter(&mut self) -> Result<ast::Parameter> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Fun) => {
                self.function_declaration().map(ast::Parameter::Lambda)
            }
            TokenEnum::Identifier | TokenEnum::Underscore => {
                m! {
                    name <- self.ident_or_underscore();
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
            name <- self.name(false);
            parameters <- self.when_next(TokenEnum::Open(Group::Parenthesis), |parser| parser.many_grouped(
                Group::Parenthesis,
                Symbol::Comma.into(),
                Parser::parameter,
            ));
            returns <- self.when(Parser::starts_type, Parser::returns);
            effects <- self.when_next(Keyword::With, Parser::with_effects);
            return ast::FunctionDeclaration { fun, name, parameters, returns, effects };
        }
    }
    pub fn returns(&mut self) -> Result<ast::Returns> {
        match self.next().token {
            TokenEnum::Identifier | TokenEnum::Underscore => {
                self.path(false).map(ast::Returns::Path)
            }
            TokenEnum::Symbol(Symbol::Bang) => Result::new(ast::Returns::Never(self.skip())),
            _ => {
                if self.starts_type() {
                    self.r#type().map(ast::Returns::Type)
                } else {
                    self.error(Expected::Returns)
                }
            }
        }
    }
    pub fn name(&mut self, underscore: bool) -> Result<ast::Name> {
        m! {
            ident <- if underscore { self.ident_or_underscore() } else { self.ident() };
            generics <- self.when_next(TokenEnum::Open(Group::Bracket), |parser| parser.many_grouped(
                Group::Bracket,
                Symbol::Comma.into(),
                Parser::generic,
            ));
            return ast::Name { ident, generics };
        }
    }
    pub fn generic(&mut self) -> Result<ast::GenericParameter> {
        match self.next().token {
            _ if self.starts_region_kind() => {
                m! {
                    kind <- self.region_kind();
                    ident <- self.ident_or_underscore();
                    return ast::GenericParameter::Region(Some(kind), ident);
                }
            }
            TokenEnum::Identifier
                // if identifier starts with lowercase letter
                if self.source.as_bytes()[self.next().span.start as usize].is_ascii_lowercase() =>
            {
                m! {
                    ident <- self.ident();
                    return ast::GenericParameter::Region(None, ident);
                }
            }
            TokenEnum::Identifier | TokenEnum::Underscore => {
                m! {
                    name <- self.name(true);
                    kind <- self.unless_next(&[TokenEnum::Symbol(Symbol::Comma)], Parser::kind);
                    return match kind {
                        Some(kind) => ast::GenericParameter::Other(name, kind),
                        None => ast::GenericParameter::Type(name),
                    };
                }
            }
            _ => {
                self.error(Expected::GenericParameter)
            }
        }
    }
    pub fn kind(&mut self) -> Result<ast::Kind> {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Type) => Result::new(ast::Kind::Type(self.skip())),
            TokenEnum::Keyword(Keyword::Effect) => Result::new(ast::Kind::Effect(self.skip())),
            TokenEnum::Keyword(Keyword::Region) => Result::new(ast::Kind::Region(self.skip())),
            TokenEnum::Keyword(Keyword::Thunk) => Result::new(ast::Kind::Thunk(self.skip())),
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
        Result::error(self.problem(expected))
    }
    fn problem(&self, expected: Expected) -> Problem {
        let next = self.next();
        let error = if next.is_eof() {
            ProblemKind::UnexpectedEOF(expected)
        } else if next.is_newline() {
            ProblemKind::UnexpectedNewline(expected)
        } else {
            ProblemKind::UnexpectedToken(expected)
        };
        error.at(self.module, &next)
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
    fn group_contains(&self, token: impl Into<TokenEnum>) -> bool {
        let token = token.into();
        let mut p = Parser {
            module: self.module,
            source: self.source,
            last_token_end: self.last_token_end,
            tokens: self.tokens,
        };
        p.skip();
        loop {
            match p.next().token {
                TokenEnum::Eof | TokenEnum::Close(_) => break false,
                TokenEnum::Open(group) => {
                    p.skip();
                    p.skip_group(group)
                }
                t if t == token => break true,
                _ => {
                    p.skip();
                }
            }
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
                _ => {
                    self.skip();
                }
            }
        }
    }
    fn skip_to_recovery(&mut self, sep: TokenEnum, until: &[TokenEnum]) {
        loop {
            match self.next().token {
                t if until.contains(&t) => {
                    break;
                }
                t if t == sep => {
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
    fn grouped<T>(
        &mut self,
        group: Group,
        parse: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<ast::Grouped<T>> {
        m! {
            open <- self.consume(TokenEnum::Open(group));
            inner <- parse(self).tap_none(|| self.skip_group(group));
            close <- self.consume(TokenEnum::Close(group)).tap_none(|| self.skip_group(group));
            return ast::Grouped { open, inner, close };
        }
    }
    fn many_grouped<T>(
        &mut self,
        group: Group,
        separator: TokenEnum,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Grouped<ast::Separated<T>>> {
        self.grouped(group, |parser| parser.many(separator, parse))
    }
    fn many<T>(
        &mut self,
        separator: TokenEnum,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Separated<T>> {
        self.many_while(separator, |_| true, parse)
    }
    fn many_while_next<T>(
        &mut self,
        separator: TokenEnum,
        token: impl Into<TokenEnum>,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Separated<T>> {
        let token = token.into();
        self.many_while(separator, |me| me.is_next(token), parse)
    }
    fn many_while<T>(
        &mut self,
        separator: TokenEnum,
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
        .map(|elements| {
            let end = self.last_token_end;
            ast::Separated { elements, end }
        })
    }
    fn many_until_seperated<T>(
        &mut self,
        separator: TokenEnum,
        until: &[TokenEnum],
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<ast::Separated<T>> {
        std::iter::from_fn(|| {
            let next = self.next().token;
            let has_next =
                !until.contains(&next) && !matches!(next, TokenEnum::Close(_) | TokenEnum::Eof);
            has_next.then(|| {
                let parser = &mut *self;
                m! {
                    t <- parse(parser)
                        .tap_none(|| parser.skip_to_recovery(separator, &[]));
                    sep <- parser.unless_next(until, |parser| parser.consume(separator)
                        .tap_none(|| parser.skip_to_recovery(separator, &[])).recover());
                    return (t, sep.flatten());
                }
            })
        })
        .collect::<Result<Vec<_>>>()
        .map(|elements| {
            let end = self.last_token_end;
            ast::Separated { elements, end }
        })
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
            has_next.then(|| {
                parse(self).tap_none(|| self.skip_to_recovery(Symbol::Semicolon.into(), until))
            })
        })
        .collect()
    }
}
