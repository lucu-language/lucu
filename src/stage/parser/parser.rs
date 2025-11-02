use compact_str::format_compact;
use do_notation::m;

use super::ast;
use crate::{
    err::{LucuDiagnostic, Result, SimpleDiagnostic},
    module::Module,
    stage::lexer::{Keyword, Literal, Symbol, Token, TokenKind},
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
            return ast::Module { imports };
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
                if next.token == TokenKind::EOF {
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
    fn skip_to_recovery(&mut self, sep: TokenKind) {
        while self.next().token != sep
            && !matches!(self.next().token, TokenKind::Close(_) | TokenKind::EOF)
        {
            self.skip();
        }
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

        while pred(self) {
            let next = parse(self);
            diagnostics.append(next.diagnostics);

            match next.value {
                Some(value) => values.push(value),
                None => self.skip_to_recovery(separator),
            }

            match self.next().token {
                TokenKind::Close(_) | TokenKind::EOF => break,
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

        Result {
            value: Some(values),
            diagnostics,
        }
    }
}
