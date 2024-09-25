use std::num::NonZeroU32;

use crate::lexer::{FullToken, Group, Symbol, Token};

use super::{Expression, List, NodeData, NodeVariant, Nodes};

pub(super) struct Parser<'a> {
    pub nodes: Nodes,
    pub errors: Vec<Error>,
    tokens: &'a [FullToken],
    pos: usize,
}

pub struct Error {
    pub error: ErrorVariant,
    pub len: u32,
    pub start: u32,
}

pub enum ErrorVariant {
    EOF,
    Unexpected(Token),
}

pub(super) type Result<T> = std::result::Result<T, Error>;

impl<'a> Parser<'a> {
    pub(super) fn new(tokens: &'a [FullToken]) -> Self {
        Self {
            nodes: Nodes::new(),
            tokens,
            pos: 0,
            errors: Vec::new(),
        }
    }
    pub(super) fn many(
        &mut self,
        variant: List,
        mut inner: impl FnMut(&mut Self) -> Result<Option<NonZeroU32>>,
    ) -> Result<NonZeroU32> {
        self.node(NodeVariant::List(variant), |parser| {
            let mut first = None;
            let mut last = None;
            while let Some(elem) = inner(parser)? {
                first = first.or(Some(elem));
                last = Some(elem);
            }
            Ok((first, last))
        })
    }
    pub(super) fn left_rec(
        &mut self,
        lhs: impl FnOnce(&mut Self) -> Result<NonZeroU32>,
        mut rhs: impl FnMut(&mut Self, Token) -> Result<Option<(Expression, Option<NonZeroU32>)>>,
    ) -> Result<NonZeroU32> {
        let mut lhs = lhs(self)?;
        let start = self.nodes[lhs.get()].start;
        loop {
            if let Some(token) = self.token_peek() {
                if let Some((variant, rhs)) = rhs(self, token.token)? {
                    lhs = self.nodes.push(NodeData {
                        variant: NodeVariant::Expression(variant),
                        len: self.position() - start,
                        start,
                        left: Some(lhs),
                        right: rhs,
                    });
                } else {
                    return Ok(lhs);
                }
            } else {
                return Ok(lhs);
            }
        }
    }
    pub(super) fn recover<T>(
        &mut self,
        token: impl Fn(Token) -> bool,
        inner: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Option<T> {
        match inner(self) {
            Ok(value) => Some(value),
            Err(e) => {
                self.errors.push(e);
                self.skip_until(token);
                None
            }
        }
    }
    pub(super) fn recover_after<T>(
        &mut self,
        token: impl Fn(Token) -> bool,
        inner: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Option<T> {
        match inner(self) {
            Ok(value) => Some(value),
            Err(e) => {
                self.errors.push(e);
                self.skip_until(token);
                self.skip();
                None
            }
        }
    }
    pub(super) fn delimited(
        &mut self,
        variant: List,
        delimiter: Symbol,
        terminal: impl Fn(Token) -> bool,
        mut inner: impl FnMut(&mut Self) -> Result<NonZeroU32>,
    ) -> NonZeroU32 {
        let mut last = false;
        self.many(variant, |parser| loop {
            if last
                || parser.token_peek().is_none()
                || parser.token_peek().is_some_and(|t| terminal(t.token))
            {
                return Ok(None);
            }
            match parser.recover(|t| t == Token::Symbol(delimiter) || terminal(t), &mut inner) {
                Some(v) => {
                    last = !parser.token_consume(Token::Symbol(delimiter));
                    return Ok(Some(v));
                }
                None => {
                    if !parser.token_consume(Token::Symbol(delimiter)) {
                        return Ok(None);
                    }
                }
            }
        })
        // as we use recover, there is no way our inner parser can fail
        .unwrap_or_else(|_| unreachable!())
    }
    pub(super) fn grouped_delimited(
        &mut self,
        variant: List,
        group: Group,
        delimiter: Symbol,
        inner: impl FnMut(&mut Self) -> Result<NonZeroU32>,
    ) -> Result<NonZeroU32> {
        self.token_expect(Token::Open(group))?;
        let list = self.delimited(variant, delimiter, |t| t == Token::Close(group), inner);
        self.recover_after(
            |t| t == Token::Close(group),
            |parser| {
                parser.token_expect(Token::Close(group))?;
                Ok(())
            },
        );
        Ok(list)
    }
    pub(super) fn grouped<T>(
        &mut self,
        group: Group,
        inner: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        self.token_expect(Token::Open(group))?;
        Ok(self.recover_after(
            |t| t == Token::Close(group),
            |parser| {
                let t = inner(parser)?;
                parser.token_expect(Token::Close(group))?;
                Ok(t)
            },
        ))
    }
    pub(super) fn check_then<T>(
        &mut self,
        token: Token,
        inner: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        if self.token_check(token) {
            Ok(Some(inner(self)?))
        } else {
            Ok(None)
        }
    }
    pub(super) fn consume_then<T>(
        &mut self,
        token: Token,
        inner: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<Option<T>> {
        if self.token_consume(token) {
            Ok(Some(inner(self)?))
        } else {
            Ok(None)
        }
    }
    pub(super) fn wrap(
        &mut self,
        variant: NodeVariant,
        inner: impl FnOnce(&mut Self) -> Result<NonZeroU32>,
    ) -> Result<NonZeroU32> {
        self.node(variant, |parser| Ok((Some(inner(parser)?), None)))
    }
    pub(super) fn peeked<A>(
        &mut self,
        variant_f: impl Fn(A) -> NodeVariant,
        default: impl FnOnce(&mut Self) -> Result<NonZeroU32>,
        inner: impl FnOnce(
            &mut Self,
            Token,
        ) -> Result<Option<(A, Option<NonZeroU32>, Option<NonZeroU32>)>>,
    ) -> Result<NonZeroU32> {
        let token = self.token_peek();
        match token {
            Some(t) => {
                let Some((variant, lhs, rhs)) = inner(self, t.token)? else {
                    return default(self);
                };

                let start = t.start;
                Ok(self.nodes.push(NodeData {
                    variant: variant_f(variant),
                    len: self.position() - start,
                    start,
                    left: lhs,
                    right: rhs,
                }))
            }
            None => default(self),
        }
    }
    pub(super) fn choice<A>(
        &mut self,
        variant_f: impl Fn(A) -> NodeVariant,
        inner: impl FnOnce(&mut Self, Token) -> Result<Option<(A, NonZeroU32, Option<NonZeroU32>)>>,
    ) -> Result<NonZeroU32> {
        let token = self.token_next()?;
        let Some((variant, lhs, rhs)) = inner(self, token.token)? else {
            return Err(Error {
                error: ErrorVariant::Unexpected(token.token),
                len: token.len as u32,
                start: token.start,
            });
        };

        let start = token.start;
        let data = &self.nodes[rhs.unwrap_or(lhs).get()];
        Ok(self.nodes.push(NodeData {
            variant: variant_f(variant),
            len: data.start + data.len - start,
            start,
            left: Some(lhs),
            right: rhs,
        }))
    }
    pub(super) fn node(
        &mut self,
        variant: NodeVariant,
        inner: impl FnOnce(&mut Self) -> Result<(Option<NonZeroU32>, Option<NonZeroU32>)>,
    ) -> Result<NonZeroU32> {
        let start = self.position();
        let (left, right) = inner(self)?;
        Ok(self.nodes.push(NodeData {
            variant,
            len: self.position() - start,
            start,
            left,
            right,
        }))
    }
    pub(super) fn leaf(&mut self, variant: NodeVariant, token: Token) -> Result<NonZeroU32> {
        let token = self.token_expect(token)?;
        Ok(self.nodes.push(NodeData {
            variant,
            len: token.len as u32,
            start: token.start,
            left: None,
            right: None,
        }))
    }
    pub(super) fn leaf_option(&mut self, variant: NodeVariant, token: Token) -> Option<NonZeroU32> {
        if let Some(token) = self.token_peek().filter(|t| t.token == token) {
            Some(self.nodes.push(NodeData {
                variant,
                len: token.len as u32,
                start: token.start,
                left: None,
                right: None,
            }))
        } else {
            None
        }
    }
    pub(super) fn token_peek(&self) -> Option<FullToken> {
        self.tokens.get(self.pos).copied()
    }
    pub(super) fn token_check(&self, token: Token) -> bool {
        self.token_peek().is_some_and(|t| t.token == token)
    }
    pub(super) fn token_next(&mut self) -> Result<FullToken> {
        let token = self.token_peek().ok_or_else(|| {
            let last = self.tokens.last().unwrap();
            Error {
                error: ErrorVariant::EOF,
                len: 0,
                start: last.start + last.len as u32,
            }
        });
        self.pos += 1;
        token
    }
    pub(super) fn token_filter(
        &mut self,
        filter: impl FnOnce(FullToken) -> bool,
    ) -> Result<FullToken> {
        let next = self.token_next()?;
        if filter(next) {
            Ok(next)
        } else {
            Err(Error {
                error: ErrorVariant::Unexpected(next.token),
                len: next.len as u32,
                start: next.start,
            })
        }
    }
    pub(super) fn token_expect(&mut self, token: Token) -> Result<FullToken> {
        self.token_filter(|t| t.token == token)
    }
    pub(super) fn token_consume(&mut self, token: Token) -> bool {
        match self.token_peek() {
            Some(v) if v.token == token => {
                self.pos += 1;
                true
            }
            _ => false,
        }
    }
    pub(super) fn skip(&mut self) {
        if self.tokens.get(self.pos).is_some() {
            self.pos += 1;
        }
    }
    pub(super) fn skip_until(&mut self, mut filter: impl FnMut(Token) -> bool) {
        loop {
            match self.token_peek() {
                Some(FullToken {
                    token: Token::Open(g),
                    ..
                }) => {
                    self.skip_to(Token::Close(g));
                    self.skip();
                }
                Some(t) if filter(t.token) => break,
                None => break,
                _ => self.skip(),
            }
        }
    }
    pub(super) fn skip_to(&mut self, token: Token) {
        self.skip_until(|t| t == token)
    }
    pub(super) fn position(&self) -> u32 {
        match self.token_peek() {
            Some(t) => t.start,
            None => {
                let last = self.tokens.last().unwrap();
                last.start + last.len as u32
            }
        }
    }
    pub(super) fn next_tokens(&self) -> impl Iterator<Item = &FullToken> {
        self.tokens[self.pos..].iter()
    }
}
