use std::fmt;
use std::ops::Range;

use anstyle::{AnsiColor, Style};
use asta_annotate::ansi::MarkStyle;
use asta_annotate::{Annotate, Annotated, Annotation, Mark};
use itertools::Itertools;

use crate::ast;
use crate::ast::visit::{Ast, Combine, Visitor};
use crate::pass::defs::Definitions;
use crate::span::HasSpan;
use crate::tokens::Token;

pub trait AnnotateExt<'a> {
    fn mark_line_numbers(self) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>>;
    fn mark_syntax(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>>;
    fn mark_semicolons(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>>;
    fn mark_ast(
        self,
        ast: &ast::Module,
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
    fn mark_line_numbers(self) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        let snippet = self.snippet();
        let range = snippet.range();
        let line_starts = Iterator::chain(
            std::iter::once(0),
            snippet
                .source()
                .bytes()
                .take(range.end)
                .enumerate()
                .filter_map(|(pos, b)| (b == b'\n').then_some(pos + 1)),
        );
        self.annotate(
            line_starts
                .enumerate()
                .map(|(line, pos)| Line(line + 1).at(pos..pos)),
        )
    }
    fn mark_syntax(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        let tokens = tokens_in_range(tokens, self.snippet().range());
        self.annotate(
            tokens
                .iter()
                .filter(|token| token.span.start < token.span.end)
                .filter_map(|token| token.token.color().map(|color| color.at(token.span))),
        )
    }
    fn mark_semicolons(
        self,
        tokens: &[Token],
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        let tokens = tokens_in_range(tokens, self.snippet().range());
        self.annotate(tokens.iter().filter_map(|token| {
            token
                .is_newline()
                .then_some(InsertedSemicolon.at(token.span))
        }))
    }
    fn mark_ast(
        self,
        ast: &ast::Module,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        #[derive(Clone, Copy)]
        struct Nodes;
        impl Visitor for Nodes {
            type Output<'a> = im::Vector<Annotation<Node>>;
            fn visit_name(self, name: &ast::Name) -> Self::Output<'_> {
                name.visit(self)
            }
            fn visit_path(self, path: &ast::Path) -> Self::Output<'_> {
                path.visit(self)
            }
            fn visit(self, ast: &impl ast::visit::Ast) -> Self::Output<'_> {
                Self::Output::combine([
                    im::Vector::unit(Node(ast.node_name()).at(ast.span())),
                    ast.visit(self),
                ])
            }
        }
        self.annotate(ast.visit(Nodes))
    }
    fn mark_definition_order(
        self,
        ast: &ast::Module,
        definitions: &Definitions,
    ) -> Annotated<'a, impl Iterator<Item = Annotation<impl Mark>>> {
        self.annotate(
            definitions
                .nodes_postorder()
                .map(|node| definitions.item(node, ast))
                .enumerate()
                .map(|(idx, def)| Definition(idx).at(def.span()))
                .sorted(),
        )
    }
}

pub const LINE_STYLE: Style = AnsiColor::Blue.on_default();
pub const INLINE_STYLE: Style = AnsiColor::BrightBlack.on_default();

struct Definition(usize);
impl Mark for Definition {
    fn style(&self) -> MarkStyle {
        MarkStyle::before(INLINE_STYLE)
    }
    fn fmt_before(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] ", self.0)
    }
}

struct Line(usize);
impl Mark for Line {
    fn style(&self) -> MarkStyle {
        MarkStyle::before(LINE_STYLE)
    }
    fn fmt_before(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{: >3} | ", self.0)
    }
}

struct InsertedSemicolon;
impl Mark for InsertedSemicolon {
    fn style(&self) -> MarkStyle {
        MarkStyle::before(INLINE_STYLE)
    }
    fn fmt_before(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ";")
    }
}

#[derive(Clone, Copy)]
struct Node(&'static str);
impl Mark for Node {
    fn style(&self) -> MarkStyle {
        MarkStyle::surround(INLINE_STYLE)
    }
    fn fmt_before(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.0)
    }
    fn fmt_after(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ")")
    }
}
