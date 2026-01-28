use std::borrow::Cow;

use anstyle::{AnsiColor, Color, Style};
use line_column::line_column;
use asta_annotate::ansi::MarkStyle;
use asta_annotate::{Annotate, Mark};

use crate::annotate::AnnotateExt;
pub use crate::annotate::LINE_STYLE;
use crate::error::{ContextLevel, Diagnostic, HasProblems, Problem, ProblemLevel};
use crate::module::ModuleResolver;
use crate::pass::lexer::Lexer;
use crate::span::Span;

pub const ERROR_COLOR: Color = Color::Ansi(AnsiColor::Red);
pub const WARNING_COLOR: Color = Color::Ansi(AnsiColor::Yellow);
pub const INFO_COLOR: Color = Color::Ansi(AnsiColor::Green);

const HIGHLIGHT_BG: Color = Color::Ansi(AnsiColor::Black);
pub const ERROR_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(ERROR_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));
pub const WARNING_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(WARNING_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));
pub const INFO_HIGHLIGHT: Style = Style::new()
    .fg_color(Some(INFO_COLOR))
    .bg_color(Some(HIGHLIGHT_BG));

pub const TITLE_STYLE: Style = Style::new().bold();
pub const CONTEXT_STYLE: Style = Style::new()
    .italic()
    .fg_color(Some(Color::Ansi(AnsiColor::BrightWhite)));
pub const LABEL_STYLE: Style = Style::new();
pub const PATH_STYLE: Style = LINE_STYLE;

pub trait PrintProblems: HasProblems {
    fn print_problems(&self, resolver: &impl ModuleResolver, compact: bool) {
        for (i, problem) in self.problems().enumerate() {
            if i > 0 && compact {
                println!();
            }
            problem.print(resolver, compact);
        }
    }
}

impl<T> PrintProblems for T where T: HasProblems {}

impl Problem {
    pub fn print(&self, resolver: &impl ModuleResolver, compact: bool) {
        let header = self.header();
        let title = header.title;
        let id = header.id;
        let (name, color, highlight) = match header.level {
            ProblemLevel::Error => ("error", ERROR_COLOR, ERROR_HIGHLIGHT),
            ProblemLevel::Warning => ("warning", WARNING_COLOR, WARNING_HIGHLIGHT),
        };

        let title_kind_style = TITLE_STYLE.fg_color(Some(color));
        anstream::print!(
            "{title_kind_style}{name} {id:03}{title_kind_style:#}{TITLE_STYLE}: {title}"
        );
        if let Some(label) = self.label() {
            anstream::println!(":{TITLE_STYLE:#} {LABEL_STYLE}{label}{LABEL_STYLE:#}");
        } else {
            anstream::println!("{TITLE_STYLE:#}");
        }

        // Problem location
        let contents = resolver.contents(&self.module);
        let path = resolver.readable_path(&self.module);

        if let Some(contents) = contents.as_deref() {
            print_highlight(highlight, self.span, Some(&path), contents, compact);
        }

        // Context locations
        self.kind.context(&mut |ctx| {
            let (contents, path) = if let Some(module) = ctx.module {
                (
                    resolver.contents(&module).map(Cow::Owned),
                    Some(resolver.readable_path(&module)),
                )
            } else {
                (contents.as_deref().map(Cow::Borrowed), None)
            };

            if let Some(contents) = contents.as_deref() {
                let (name, color, highlight) = match ctx.level {
                    ContextLevel::Same => (name, color, highlight),
                    ContextLevel::Info => ("info", INFO_COLOR, INFO_HIGHLIGHT),
                };
                let context_kind_style = CONTEXT_STYLE.fg_color(Some(color));

                if let Some(label) = ctx.label {
                    anstream::println!("{context_kind_style}{name}{context_kind_style:#}{CONTEXT_STYLE}: {label}{CONTEXT_STYLE:#}");
                } else if path.is_none() {
                    anstream::println!("{LINE_STYLE} ...  {LINE_STYLE:#}");
                }

                print_highlight(highlight, ctx.span, path.as_deref(), contents,compact);
            }
        });
    }
}

fn print_highlight(
    highlight: Style,
    span: Span,
    path: Option<&str>,
    contents: &str,
    compact: bool,
) {
    struct Error(Style);
    impl Mark for Error {
        fn ignore_nested(&self) -> bool {
            true
        }
        fn style(&self) -> MarkStyle {
            self.0.into()
        }
        fn fmt_before(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, " ")
        }
        fn fmt_after(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, " ")
        }
    }

    let (line, col) = line_column(contents, span.start as usize);
    let snippet = contents.snippet().lines_containing(span);
    let tokens = Lexer::new(contents)
        .for_range(snippet.range())
        .collect::<Box<_>>();

    if let Some(path) = path {
        anstream::println!(
            "{LINE_STYLE}   /->{LINE_STYLE:#} {PATH_STYLE}{path}:{line}:{col}{PATH_STYLE:#}",
        );
    }

    if !compact {
        anstream::println!("{LINE_STYLE}    | {LINE_STYLE:#}");
    }
    anstream::println!(
        "{}",
        snippet
            .mark_line_numbers()
            .mark_syntax(&tokens)
            .mark_semicolons(&tokens)
            .annotate(std::iter::once(Error(highlight).at(span)))
    );
    if !compact {
        anstream::println!("{LINE_STYLE}    | {LINE_STYLE:#}");
    }
}
