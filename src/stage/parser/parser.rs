use compact_str::format_compact;
use do_notation::m;

use super::ast;
use crate::{
    err::{ProblemKind, Result},
    module::Module,
    span::{Span, Spanned},
    stage::lexer::token::{Group, Keyword, Literal, Symbol, SymbolAssign, Token, TokenKind},
};

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
        self.consume(Literal::String)
            .map(|tok| ast::String(Spanned((&self.source[tok.span.inner()]).into(), tok.span)))
    }
    pub fn ident(&mut self) -> Result<ast::Ident> {
        self.consume(TokenKind::Identifier)
            .map(|tok| ast::Ident(Spanned((&self.source[tok.span]).into(), tok.span)))
    }
    pub fn import(&mut self) -> Result<ast::Import> {
        m! {
            _ <- self.consume(Keyword::Import);
            path <- self.string();
            ident <- self.when_next(TokenKind::Identifier, Parser::ident);
            return ast::Import { path, ident };
        }
    }
    pub fn module(&mut self) -> Result<ast::Module> {
        m! {
            imports <- self.many_while_next(Symbol::Semicolon, Keyword::Import, Parser::import);
            definitions <- self.many(Symbol::Semicolon, Parser::definition);
            return ast::Module { imports, definitions };
        }
    }
    pub fn definition(&mut self) -> Result<ast::Definition> {
        match self.next().token {
            TokenKind::Keyword(Keyword::Fun) => self.function().map(ast::Definition::Function),
            TokenKind::Keyword(Keyword::Type) => self.type_alias().map(ast::Definition::Type),
            tok => todo!("error: unknown definition with token {tok}"),
        }
    }
    pub fn function(&mut self) -> Result<ast::Function> {
        m! {
            declaration <- self.function_declaration();
            _ <- self.consume(Symbol::Assign(SymbolAssign::Equals));
            definition <- self.expression();
            return ast::Function { declaration, definition };
        }
    }
    pub fn type_alias(&mut self) -> Result<ast::TypeAlias> {
        m! {
            _ <- self.consume(Keyword::Type);
            name <- self.name();
            _ <- self.consume(Symbol::Assign(SymbolAssign::Equals));
            definition <- self.r#type();
            return ast::TypeAlias { name, definition };
        }
    }
    pub fn path(&mut self) -> Result<ast::Path> {
        m! {
            first <- self.ident();
            second <- self.when_next(Symbol::Dot, |parse| {
                parse.skip();
                parse.ident()
            });
            return match second {
                Some(name) => ast::Path { package: Some(first), name },
                None => ast::Path { package: None, name: first },
            };
        }
    }
    pub fn r#type(&mut self) -> Result<ast::Type> {
        self.spanned(|parse| match parse.next().token {
            TokenKind::Identifier => parse.path().map(|path| {
                if path.package.is_none() && path.name.as_str() == "int" {
                    ast::TypeEnum::Int
                } else {
                    ast::TypeEnum::Path(path)
                }
            }),
            TokenKind::Keyword(Keyword::Struct) => parse.r#struct().map(ast::TypeEnum::Struct),
            _ => todo!("error"),
        })
        .map(Box::new)
    }
    pub fn r#struct(&mut self) -> Result<ast::Struct> {
        m! {
            _ <- self.consume(Keyword::Struct);
            members <- self.many_grouped(Group::Parenthesis, Symbol::Colon, Parser::struct_member);
            return ast::Struct { members };
        }
    }
    pub fn struct_member(&mut self) -> Result<ast::StructMember> {
        m! {
            name <- self.ident();
            ty <- self.r#type();
            return ast::StructMember::Data(name, ty);
        }
    }
    pub fn expression(&mut self) -> Result<ast::Expression> {
        self.spanned(|parse| {
            m! {
                _ <- parse.consume(TokenKind::Open(Group::Brace));
                _ <- parse.consume(TokenKind::Close(Group::Brace)).tap_none(|| parse.skip_group(Group::Brace));
                return ast::ExpressionEnum::Block;
            }
        })
        .map(Box::new)
    }
    pub fn function_parameter(&mut self) -> Result<ast::FunctionParameter> {
        match self.next().token {
            TokenKind::Keyword(Keyword::Fun) => self
                .function_declaration()
                .map(ast::FunctionParameter::Lambda),
            TokenKind::Identifier => {
                m! {
                    name <- self.ident();
                    ty <- self.r#type();
                    return ast::FunctionParameter::Data(name, ty);
                }
            }
            _ => todo!("error"),
        }
    }
    pub fn function_declaration(&mut self) -> Result<ast::FunctionDeclaration> {
        m! {
            _ <- self.consume(Keyword::Fun);
            name <- self.name();
            parameters <- self.when_next(TokenKind::Open(Group::Parenthesis), |parser| parser.many_grouped(
                Group::Parenthesis,
                Symbol::Comma,
                Parser::function_parameter,
            ));
            returns <- self.unless_next(
                &[TokenKind::Symbol(Symbol::Assign(SymbolAssign::Equals)), TokenKind::Symbol(Symbol::Comma), TokenKind::Symbol(Symbol::Semicolon), TokenKind::Open(Group::Brace)],
                Parser::returns
            );
            return ast::FunctionDeclaration { name, parameters, returns };
        }
    }
    pub fn returns(&mut self) -> Result<ast::Returns> {
        self.spanned(|parse| {
            match parse.next().token {
                TokenKind::Symbol(Symbol::Bang) => {
                    parse.skip();
                    Result::new(ast::ReturnsEnum::Never)
                }
                _ => parse.r#type().map(ast::ReturnsEnum::Data),
                // TODO: check if next token cannot start a type, then give error
            }
        })
    }
    pub fn name(&mut self) -> Result<ast::Name> {
        m! {
            ident <- self.ident();
            generics <- self.when_next(TokenKind::Open(Group::Bracket), |parser| parser.many_grouped(
                Group::Bracket,
                Symbol::Comma,
                Parser::generic,
            ));
            return ast::Name { ident, generics };
        }
    }
    pub fn generic(&mut self) -> Result<ast::Generic> {
        m! {
            name <- self.name();
            kind <- self.unless_next(&[], Parser::kind);
            return ast::Generic { name, kind };
        }
    }
    pub fn kind(&mut self) -> Result<ast::Kind> {
        self.spanned(|parse| {
            match parse.next().token {
                TokenKind::Keyword(Keyword::Type) => {
                    parse.skip();
                    Result::new(ast::KindEnum::Type)
                }
                _ => parse.r#type().map(ast::KindEnum::Constant),
                // TODO: check if next token cannot start a type, then give error
            }
        })
    }

    fn spanned<T>(&mut self, parse: impl Fn(&mut Self) -> Result<T>) -> Result<Spanned<T>> {
        let start = self.next().span.start;
        parse(self).map(|t| Spanned(t, Span::new(start, self.last_token_end)))
    }
    fn consume(&mut self, token: impl Into<TokenKind>) -> Result<Token> {
        let token = token.into();
        match self.tokens.split_first().expect("ICE: consumed EOF token") {
            (next, rest) if next.token == token => {
                self.tokens = rest;
                self.last_token_end = next.span.end;
                Result::new(*next)
            }
            (next, _) => {
                let label = format_compact!("Expected {}", token);
                let error = if next.token == TokenKind::Eof {
                    ProblemKind::UnexpectedEOF(label)
                } else if next.token == TokenKind::Symbol(Symbol::Semicolon)
                    && next.span.start == next.span.end
                {
                    ProblemKind::UnexpectedNewline(label)
                } else {
                    ProblemKind::UnexpectedToken(label)
                };
                Result::error(error.at(self.module, next))
            }
        }
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
    fn is_next(&self, token: impl Into<TokenKind>) -> bool {
        self.next().token == token.into()
    }
    fn unless_next<T>(
        &mut self,
        tokens: &[TokenKind],
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        let next = self.next().token;
        if !tokens.contains(&next)
            && !matches!(self.next().token, TokenKind::Close(_) | TokenKind::Eof)
        {
            parse(self).map(Some)
        } else {
            Result::new(None)
        }
    }
    fn when_next<T>(
        &mut self,
        token: impl Into<TokenKind>,
        parse: impl Fn(&mut Self) -> Result<T>,
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
                TokenKind::Eof => break,
                TokenKind::Close(c) => {
                    if c == group {
                        self.skip();
                    }
                    break;
                }
                TokenKind::Open(group) => {
                    self.skip();
                    self.skip_group(group)
                }
                _ => self.skip(),
            }
        }
    }
    fn skip_to_recovery(&mut self, sep: Symbol) {
        loop {
            match self.next().token {
                TokenKind::Symbol(sym) if sym == sep => {
                    self.skip();
                    break;
                }
                TokenKind::Close(_) | TokenKind::Eof => break,
                TokenKind::Open(group) => {
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
            _ <- self.consume(TokenKind::Open(group));
            many <- self.many(separator, parse).tap_none(|| self.skip_group(group));
            _ <- self.consume(TokenKind::Close(group));
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
        token: impl Into<TokenKind>,
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
                pred(self) && !matches!(self.next().token, TokenKind::Close(_) | TokenKind::Eof);
            has_next.then(|| {
                let parser = &mut *self;
                m! {
                    t <- parse(parser)
                        .tap_none(|| parser.skip_to_recovery(separator));
                    _ <- parser.unless_next(&[], |parser| parser.consume(separator)
                        .tap_none(|| parser.skip_to_recovery(separator)).recover());
                    return t;
                }
            })
        })
        .collect()
    }
}
