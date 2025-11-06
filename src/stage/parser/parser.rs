use compact_str::format_compact;
use do_notation::m;

use super::ast;
use crate::{
    err::{LucuDiagnostic, Result, SimpleDiagnostic},
    module::Module,
    stage::lexer::{
        Lexer,
        token::{Group, Keyword, Literal, Symbol, SymbolAssign, Token, TokenKind},
    },
};

pub struct Parser<'a> {
    module: &'a Module,
    source: &'a str,
    tokens: &'a [Token],
}

impl<'a> Parser<'a> {
    pub fn new(module: &'a Module, source: &'a str, tokens: &'a [Token]) -> Self {
        Self {
            module,
            source,
            tokens,
        }
    }
    pub fn parse(module: &'a Module, source: &'a str) -> Result<ast::Module> {
        let tokens = Lexer::new(source).collect::<Box<_>>();
        Parser {
            module,
            source,
            tokens: &tokens,
        }
        .module()
    }

    pub fn string(&mut self) -> Result<ast::String> {
        self.consume(Literal::String)
            .map(|tok| ast::Spanned((&self.source[tok.span.inner()]).into(), tok.span))
    }
    pub fn ident(&mut self) -> Result<ast::Ident> {
        self.consume(TokenKind::Identifier)
            .map(|tok| ast::Spanned((&self.source[tok.span]).into(), tok.span))
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
            tok => todo!("error: unknown definition with token {tok}"),
        }
    }
    pub fn function(&mut self) -> Result<ast::Function> {
        m! {
            _ <- self.consume(Keyword::Fun);
            name <- self.ident();
            signature <- self.function_signature();
            _ <- self.consume(Symbol::Assign(SymbolAssign::Equals));
            definition <- self.expression();
            return ast::Function {
                name,
                signature,
                definition,
            };
        }
    }
    pub fn ty(&mut self) -> Result<ast::Type> {
        m! {
            _ <- self.ident().and_then(|s| if s.0 == "int" { Result::new(s) } else { todo!("unknown type") });
            return ast::Type::Int;
        }
    }
    pub fn expression(&mut self) -> Result<ast::Expression> {
        m! {
            _ <- self.consume(TokenKind::Open(Group::Brace));
            _ <- self.consume(TokenKind::Close(Group::Brace));
            return ast::Expression::Block;
        }
    }
    pub fn function_parameter(&mut self) -> Result<ast::FunctionParameter> {
        if self.is_next(Keyword::Fun) {
            self.skip();
            m! {
                name <- self.ident();
                sign <- self.function_signature();
                return ast::FunctionParameter::Lambda(name, sign);
            }
        } else {
            m! {
                name <- self.ident();
                ty <- self.ty();
                return ast::FunctionParameter::Data(name, ty);
            }
        }
    }
    pub fn function_signature(&mut self) -> Result<ast::FunctionSignature> {
        m! {
            parameters <- self.when_next(TokenKind::Open(Group::Parenthesis), |parser| parser.many_grouped(
                Group::Parenthesis,
                Symbol::Comma,
                Parser::function_parameter,
            ));
            return_ty <- self.unless_next(
                &[TokenKind::Symbol(Symbol::Assign(SymbolAssign::Equals)), TokenKind::Symbol(Symbol::Comma), TokenKind::Symbol(Symbol::Semicolon)],
                Parser::ty
            );
            return ast::FunctionSignature {
                parameters,
                return_ty,
            };
        }
    }

    fn consume(&mut self, token: impl Into<TokenKind>) -> Result<Token> {
        let token = token.into();
        match self.tokens.split_first().expect("ICE: consumed EOF token") {
            (next, rest) if next.token == token => {
                self.tokens = rest;
                Result::new(*next)
            }
            (next, _) => {
                let diagnostic = SimpleDiagnostic::new(self.module.clone(), next.span)
                    .label(format_compact!("Expected {}", token));
                if next.token == TokenKind::Eof {
                    Result::error(LucuDiagnostic::UnexpectedEOF(diagnostic))
                } else {
                    Result::error(LucuDiagnostic::UnexpectedToken(diagnostic))
                }
            }
        }
    }
    fn skip(&mut self) {
        self.tokens = self
            .tokens
            .split_first()
            .expect("ICE: consumed EOF token")
            .1;
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
        if !tokens.contains(&self.next().token)
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
        self.skip();
        loop {
            match self.next().token {
                TokenKind::Eof => break,
                TokenKind::Close(c) => {
                    if c == group {
                        self.skip();
                    }
                    break;
                }
                TokenKind::Open(group) => self.skip_group(group),
                _ => self.skip(),
            }
        }
    }
    fn skip_to_recovery(&mut self, sep: TokenKind) {
        loop {
            match self.next().token {
                tok if tok == sep => break,
                TokenKind::Close(_) | TokenKind::Eof => break,
                TokenKind::Open(group) => self.skip_group(group),
                _ => self.skip(),
            }
        }
    }
    fn many_grouped<T>(
        &mut self,
        group: Group,
        separator: impl Into<TokenKind>,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        m! {
            _ <- self.consume(TokenKind::Open(group));
            many <- self.many(separator, parse);
            _ <- self.consume(TokenKind::Close(group));
            return many;
        }
    }
    fn many<T>(
        &mut self,
        separator: impl Into<TokenKind>,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        self.many_while(separator, |_| true, parse)
    }
    fn many_while_next<T>(
        &mut self,
        separator: impl Into<TokenKind>,
        token: impl Into<TokenKind>,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        let token = token.into();
        self.many_while(separator, |me| me.is_next(token), parse)
    }
    fn many_while<T>(
        &mut self,
        separator: impl Into<TokenKind>,
        pred: impl Fn(&Self) -> bool,
        parse: impl Fn(&mut Self) -> Result<T>,
    ) -> Result<Vec<T>> {
        let separator = separator.into();

        let mut values = Vec::new();
        let mut diagnostics = im::Vector::new();

        while pred(self) && !matches!(self.next().token, TokenKind::Close(_) | TokenKind::Eof) {
            let next = parse(self);
            diagnostics.append(next.diagnostics);

            match next.value {
                Some(value) => values.push(value),
                None => self.skip_to_recovery(separator),
            }

            match self.next().token {
                TokenKind::Close(_) | TokenKind::Eof => break,
                _ => {
                    let sep = self.consume(separator);
                    diagnostics.append(sep.diagnostics);

                    if sep.value.is_none() {
                        self.skip_to_recovery(separator);
                        if self.is_next(separator) {
                            self.skip();
                        }
                    }
                }
            }
        }

        Result::new(values).prepended(diagnostics)
    }
}
