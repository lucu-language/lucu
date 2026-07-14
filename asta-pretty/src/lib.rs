#![no_std]

use core::fmt::{self, Display};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Chunk<'text> {
    pub contents: &'text str,
    pub size: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Node<'text> {
    /// A choice between "wrapping" and "not wrapping".
    /// If the bool is set to true, and the group is "not wrapping",
    /// it will force all inner groups to also "not wrap".
    OpenGroup(bool),
    CloseGroup,

    /// All inner nodes will be indented.
    OpenIndent,
    CloseIndent,

    /// All inner nodes will be indented, if we are wrapping.
    OpenIndentOnWrap,
    CloseIndentOnWrap,

    /// A piece of text.
    Text(Chunk<'text>),
    /// A newline.
    Line,
    /// If we are "wrapping", a newline is placed after the first text.
    /// Otherwise, we place the second text.
    LineOr(Chunk<'text>, Chunk<'text>),
}

impl<'text> Chunk<'text> {
    pub const EMPTY: Self = Self::new("");
    pub const SPACE: Self = Self::new(" ");
    pub const COMMA: Self = Self::new(",");
    pub const COMMA_SPACE: Self = Self::new(", ");

    pub const fn new(contents: &'text str) -> Self {
        Self {
            contents,
            size: contents.len(),
        }
    }
    pub const fn new_sized(contents: &'text str, size: usize) -> Self {
        Self { contents, size }
    }
}

impl<'text> Node<'text> {
    pub const LN: Self = Node::LineOr(Chunk::EMPTY, Chunk::EMPTY);
    pub const LN_SPACE: Self = Node::LineOr(Chunk::EMPTY, Chunk::SPACE);
    pub const LN_COMMA_SPACE: Self = Node::LineOr(Chunk::COMMA, Chunk::COMMA_SPACE);
    pub const LN_TRAILING_COMMA: Self = Node::LineOr(Chunk::COMMA, Chunk::EMPTY);
    pub const LN_TRAILING_COMMA_SPACE: Self = Node::LineOr(Chunk::COMMA, Chunk::SPACE);

    pub const fn text(contents: &'text str) -> Self {
        Self::Text(Chunk::new(contents))
    }

    pub const fn text_sized(contents: &'text str, size: usize) -> Self {
        Self::Text(Chunk::new_sized(contents, size))
    }

    fn min_width(
        nodes: &[Self],
        indent_size: usize,
        mut current: usize,
        mut current_indent: usize,
        mut nesting: usize,
        mut wrap: u64,
        mut indent_todo: usize,
        force_nowrap: bool,
    ) -> usize {
        let mut nesting_min = nesting;
        let nesting_start = nesting;
        let mut maximum = 0;

        set_bit(&mut wrap, nesting as u8, false);
        let mut nowrap = force_nowrap.then_some(nesting);

        for &node in nodes {
            match node {
                Node::OpenGroup(_) => {
                    nesting += 1;
                }
                Node::CloseGroup => {
                    if nowrap.is_some_and(|n| n == nesting) {
                        nowrap = None;
                    }
                    if nesting == nesting_min {
                        nesting_min -= 1;
                    }
                    nesting -= 1;
                }
                Node::OpenIndent => current_indent += indent_size,
                Node::CloseIndent => {
                    current_indent -= indent_size;
                    indent_todo = indent_todo.min(current_indent);
                }
                Node::OpenIndentOnWrap => {
                    if (nesting != nesting_min || bit_set(wrap, nesting as u8)) && nowrap.is_none()
                    {
                        // Assumes that wrapping is always the better choice
                        current_indent += indent_size;
                    }
                }
                Node::CloseIndentOnWrap => {
                    if (nesting != nesting_min || bit_set(wrap, nesting as u8)) && nowrap.is_none()
                    {
                        // Assumes that wrapping is always the better choice
                        current_indent -= indent_size;
                        indent_todo = indent_todo.min(current_indent);
                    }
                }
                Node::Text(text) => {
                    if !text.contents.is_empty() {
                        current = current.saturating_add(indent_todo);
                        indent_todo = 0;
                    }
                    current = current.saturating_add(text.size)
                }
                Node::Line => {
                    maximum = maximum.max(current);
                    if nesting_min < nesting_start {
                        return maximum;
                    }
                    current = 0;
                    indent_todo = current_indent;
                }
                Node::LineOr(wrapping, nonwrapping) => {
                    if (nesting == nesting_min && !bit_set(wrap, nesting as u8)) || nowrap.is_some()
                    {
                        if !nonwrapping.contents.is_empty() {
                            current = current.saturating_add(indent_todo);
                            indent_todo = 0;
                        }
                        current = current.saturating_add(nonwrapping.size)
                    } else {
                        // Assumes that wrapping is always the better choice
                        if !wrapping.contents.is_empty() {
                            current = current.saturating_add(indent_todo);
                        }
                        maximum = maximum.max(current.saturating_add(wrapping.size));
                        if nesting_min < nesting_start {
                            return maximum;
                        }
                        current = 0;
                        indent_todo = current_indent;
                    }
                }
            }
        }
        maximum.max(current)
    }

    fn display(
        f: &mut fmt::Formatter<'_>,
        nodes: &mut &[Self],
        current: &mut usize,
        indent_size: usize,
        mut current_indent: usize,
        indent_todo: &mut usize,
        wrap: bool,
    ) -> fmt::Result {
        let mut nesting: usize = 0;

        while let Some((&next, rest)) = nodes.split_first() {
            match next {
                Node::OpenGroup(_) => {
                    nesting += 1;
                }
                Node::CloseGroup => {
                    if nesting == 0 {
                        return Ok(());
                    } else {
                        nesting -= 1;
                    }
                }
                Node::OpenIndent => current_indent += indent_size,
                Node::CloseIndent => {
                    current_indent -= indent_size;
                    *indent_todo = (*indent_todo).min(current_indent);
                }
                Node::OpenIndentOnWrap => {
                    if wrap {
                        current_indent += indent_size;
                    }
                }
                Node::CloseIndentOnWrap => {
                    if wrap {
                        current_indent -= indent_size;
                        *indent_todo = (*indent_todo).min(current_indent);
                    }
                }
                Node::Text(chunk) => {
                    if !chunk.contents.is_empty() {
                        write!(f, "{: <1$}", "", indent_todo)?;
                        *current += *indent_todo;
                        *indent_todo = 0;
                    }
                    write!(f, "{}", chunk.contents)?;
                    *current += chunk.size;
                }
                Node::Line => {
                    writeln!(f)?;
                    *current = 0;
                    *indent_todo = current_indent;
                }
                Node::LineOr(wrapping, nonwrapping) => {
                    if wrap {
                        if !wrapping.contents.is_empty() {
                            write!(f, "{: <1$}", "", *indent_todo)?;
                        }
                        writeln!(f, "{}", wrapping.contents)?;
                        *current = 0;
                        *indent_todo = current_indent;
                    } else {
                        if !nonwrapping.contents.is_empty() {
                            write!(f, "{: <1$}", "", *indent_todo)?;
                            *current += *indent_todo;
                            *indent_todo = 0;
                        }
                        write!(f, "{}", nonwrapping.contents)?;
                        *current += nonwrapping.size;
                    }
                }
            }
            *nodes = rest;
        }
        assert!(nesting == 0);
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct Text<'nodes, 'text> {
    pub nodes: &'nodes [Node<'text>],
    pub indent_size: usize,
    pub maximum_width: usize,
}

fn bit_set(bits: u64, n: u8) -> bool {
    (bits >> n) & 1 == 1
}

fn set_bit(bits: &mut u64, n: u8, set: bool) {
    if set {
        *bits |= 1 << n;
    } else {
        *bits &= u64::MAX ^ (1 << n);
    }
}

impl Display for Text<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut current = 0;
        let mut current_indent = 0;
        let mut nodes = self.nodes;

        let mut wrap: u64 = 0;
        let mut nesting: u8 = 0;

        let mut indent_todo = 0;

        while let Some((&next, rest)) = nodes.split_first() {
            match next {
                Node::OpenGroup(force) => {
                    nesting += 1;
                    if nesting >= 64 {
                        // too much nesting to keep track of
                        // we just wrap everything at this point
                        nodes = rest;
                        Node::display(
                            f,
                            &mut nodes,
                            &mut current,
                            self.indent_size,
                            current_indent,
                            &mut indent_todo,
                            true,
                        )?;
                        continue;
                    }

                    if Node::min_width(
                        rest,
                        self.indent_size,
                        current,
                        current_indent,
                        nesting as usize,
                        wrap,
                        indent_todo,
                        force,
                    ) <= self.maximum_width
                    {
                        // push nonwrap
                        set_bit(&mut wrap, nesting, false);

                        if force {
                            // display all inner nodes without wrapping
                            nodes = rest;
                            Node::display(
                                f,
                                &mut nodes,
                                &mut current,
                                self.indent_size,
                                current_indent,
                                &mut indent_todo,
                                false,
                            )?;
                            continue;
                        }
                    } else {
                        // push wrap
                        set_bit(&mut wrap, nesting, true);
                    }
                }
                Node::CloseGroup => {
                    assert!(nesting > 0);
                    nesting -= 1;
                }
                Node::OpenIndent => current_indent += self.indent_size,
                Node::CloseIndent => {
                    current_indent -= self.indent_size;
                    indent_todo = indent_todo.min(current_indent);
                }
                Node::OpenIndentOnWrap => {
                    if bit_set(wrap, nesting) {
                        current_indent += self.indent_size;
                    }
                }
                Node::CloseIndentOnWrap => {
                    if bit_set(wrap, nesting) {
                        current_indent -= self.indent_size;
                        indent_todo = indent_todo.min(current_indent);
                    }
                }
                Node::Text(chunk) => {
                    if !chunk.contents.is_empty() {
                        write!(f, "{: <1$}", "", indent_todo)?;
                        current += indent_todo;
                        indent_todo = 0;
                    }
                    write!(f, "{}", chunk.contents)?;
                    current += chunk.size;
                }
                Node::Line => {
                    writeln!(f)?;
                    current = 0;
                    indent_todo = current_indent;
                }
                Node::LineOr(wrapping, nonwrapping) => {
                    if bit_set(wrap, nesting) {
                        if !wrapping.contents.is_empty() {
                            write!(f, "{: <1$}", "", indent_todo)?;
                        }
                        writeln!(f, "{}", wrapping.contents)?;
                        current = 0;
                        indent_todo = current_indent;
                    } else {
                        if !nonwrapping.contents.is_empty() {
                            write!(f, "{: <1$}", "", indent_todo)?;
                            current += indent_todo;
                            indent_todo = 0;
                        }
                        write!(f, "{}", nonwrapping.contents)?;
                        current += nonwrapping.size;
                    }
                }
            }
            nodes = rest;
        }
        assert!(nesting == 0);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::string::ToString;

    use super::*;

    #[test]
    fn test_wrapping() {
        let nodes = [
            Node::OpenGroup(false),
            Node::text("["),
            Node::OpenIndent,
            Node::LN_SPACE,
            Node::text("hello"),
            Node::LN_COMMA_SPACE,
            Node::text("world"),
            Node::LN_TRAILING_COMMA_SPACE,
            Node::CloseIndent,
            Node::text("]"),
            Node::CloseGroup,
        ];
        let text1 = Text {
            nodes: &nodes,
            indent_size: 4,
            maximum_width: 80,
        };
        assert_eq!(text1.to_string(), "[ hello, world ]".to_string());
        let text2 = Text {
            nodes: &nodes,
            indent_size: 4,
            maximum_width: 16,
        };
        assert_eq!(text2.to_string(), "[ hello, world ]".to_string());
        let text3 = Text {
            nodes: &nodes,
            indent_size: 4,
            maximum_width: 15,
        };
        assert_eq!(
            text3.to_string(),
            "[\n    hello,\n    world,\n]".to_string()
        );
        let text4 = Text {
            nodes: &nodes,
            indent_size: 4,
            maximum_width: 8,
        };
        assert_eq!(
            text4.to_string(),
            "[\n    hello,\n    world,\n]".to_string()
        );
    }
}
