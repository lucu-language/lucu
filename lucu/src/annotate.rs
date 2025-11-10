use std::fmt;
use std::ops::Range;

use anstyle::AnsiColor;
use itertools::Itertools;
use lucu_annotate::{Annotate, Annotated, Annotation, Mark};

use crate::span::HasSpan;
use crate::stage::ast;
use crate::stage::defs::Definitions;
use crate::stage::token::{Symbol, Token, TokenKind};

pub trait AnnotateExt<'a> {
    fn mark_syntax(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>>;
    fn mark_semicolons(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>>;
    fn mark_definition_order(
        self,
        ast: &ast::Module,
        definitions: &Definitions,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>>;
}

fn tokens_in_range(tokens: &[Token], range: Range<usize>) -> &[Token] {
    // FIXME: this can be made more efficient with binary search
    let start = tokens
        .iter()
        .position(|t| t.span.start as usize >= range.start)
        .unwrap_or(tokens.len());
    let end = tokens
        .iter()
        .rposition(|t| t.span.end as usize <= range.end)
        .map(|n| n + 1)
        .unwrap_or(0);
    &tokens[start..end]
}

impl<'a, T> AnnotateExt<'a> for T
where
    T: Annotate<'a>,
{
    fn mark_syntax(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        let tokens = tokens_in_range(tokens, self.snippet().range());
        self.annotate(
            tokens
                .iter()
                .filter_map(|token| token.token.color().map(|color| color.at(token.span))),
        )
    }
    fn mark_semicolons(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        let tokens = tokens_in_range(tokens, self.snippet().range());
        self.annotate(tokens.iter().filter_map(|token| {
            (token.span.start == token.span.end
                && token.token == TokenKind::Symbol(Symbol::Semicolon))
            .then_some(InsertedSemicolon.at(token.span))
        }))
    }
    fn mark_definition_order(
        self,
        ast: &ast::Module,
        definitions: &Definitions,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        self.annotate(
            definitions
                .spans(ast)
                .enumerate()
                .map(|(idx, def)| InlinePos(idx).at(def.span()))
                .sorted(),
        )
    }
}

struct InlinePos(usize);
impl Mark for InlinePos {
    fn fmt_before(&self, _segment: &str, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let style = AnsiColor::BrightBlack.on_default();
        write!(f, "{}[{}]{:#} ", style, self.0, style)
    }
    fn fmt_after(&self, _segment: &str, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

struct InsertedSemicolon;
impl Mark for InsertedSemicolon {
    fn fmt_before(&self, _segment: &str, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let style = AnsiColor::BrightBlack.on_default();
        write!(f, "{};{:#}", style, style)
    }
    fn fmt_after(&self, _segment: &str, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Ok(())
    }
}
