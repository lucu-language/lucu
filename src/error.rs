use std::iter;

use crate::lexer::{Group, Token};

#[derive(Debug, Clone, Copy)]
pub struct Ranged<T>(pub T, pub usize, pub usize);

impl<T> Ranged<T> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Ranged<U> {
        Ranged(f(self.0), self.1, self.2)
    }
    pub fn empty(&self) -> Ranged<()> {
        Ranged((), self.1, self.2)
    }
    pub fn with<U>(&self, val: U) -> Ranged<U> {
        Ranged(val, self.1, self.2)
    }
    pub fn clamp(self, min: usize, max: usize) -> Self {
        Ranged(self.0, self.1.clamp(min, max), self.2.clamp(min, max))
    }
}

pub enum Error {
    UnknownSymbol,
    UnclosedString,

    Unexpected(Expected),
    UnclosedGroup(Group),

    UnknownEffect,
    UnknownEffectFun(Ranged<()>, Option<Ranged<()>>),
    UnknownValue,
    UnhandledEffect,
}

pub enum Expected {
    Token(Token),
    Identifier,
    Definition,
    Expression,
}

impl From<Token> for Expected {
    fn from(value: Token) -> Self {
        Self::Token(value)
    }
}

enum Gravity {
    Whole,
    EndPlus,
}

impl Error {
    fn gravity(&self) -> Gravity {
        match self {
            Error::UnknownSymbol => Gravity::Whole,
            Error::UnclosedString => Gravity::EndPlus,
            Error::Unexpected(_) => Gravity::Whole,
            Error::UnclosedGroup(_) => Gravity::Whole,
            Error::UnknownEffect => Gravity::Whole,
            Error::UnknownValue => Gravity::Whole,
            Error::UnknownEffectFun(_, _) => Gravity::Whole,
            Error::UnhandledEffect => Gravity::Whole,
        }
    }
}

pub struct Errors {
    vec: Vec<Ranged<Error>>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
struct LinePos {
    line: usize,
    column: usize,
}

fn get_lines(file: &str, range: Ranged<()>) -> (LinePos, LinePos) {
    let start = file
        .chars()
        .take(range.1)
        .fold((0, 0), |(line, column), c| {
            if c == '\n' {
                (line + 1, 0)
            } else {
                (line, column + 1)
            }
        });
    let end =
        file.chars()
            .skip(range.1)
            .take(range.2 - range.1)
            .fold(start, |(line, column), c| {
                if c == '\n' {
                    (line + 1, 0)
                } else {
                    (line, column + 1)
                }
            });
    (
        LinePos {
            line: start.0,
            column: start.1,
        },
        LinePos {
            line: end.0,
            column: end.1,
        },
    )
}

struct Highlight {
    start: LinePos,
    end: LinePos,
    color: u8,
    gravity: Gravity,
}

impl Highlight {
    fn from_file(file: &str, range: Ranged<()>, color: u8, gravity: Gravity) -> Self {
        let (start, end) = get_lines(file, range);
        Self {
            start,
            end,
            color,
            gravity,
        }
    }
}

fn highlight(i: u8, s: &str, color: bool, bold: bool) -> String {
    if color {
        let mut bg = 31 + ((i + 4) % 14);
        if bg >= 38 {
            bg = 101 + (bg - 38);
        }
        if bold {
            format!("\x1b[{};40m{}\x1b[39;49m", bg, s)
        } else {
            format!("\x1b[1;{};40m{}\x1b[0m", bg, s)
        }
    } else {
        if bold {
            format!("'{}'", s)
        } else {
            format!("{}", s)
        }
    }
}

const LINE_TOLERANCE: usize = 3;

fn print_error(lines: &[&str], filename: &str, highlights: &[Highlight], color: bool) {
    if let Some(first) = highlights.first() {
        // print header
        if color {
            println!(
                "   \x1b[34m/->\x1b[39m {}:{}:{}",
                filename, first.start.line, first.start.column
            );
            println!("    \x1b[34m|\x1b[39m");
        } else {
            println!(
                "   /-> {}:{}:{}",
                filename, first.start.line, first.start.column
            );
            println!("    |");
        }
    }

    let mut sorted = Vec::new();
    sorted.extend(highlights.iter());
    sorted.sort_unstable_by_key(|h| h.start);

    if let Some(&first) = sorted.first() {
        let mut iter = sorted.iter().copied();
        let mut next = iter.next().unwrap_or(first);
        let mut line = first.start.line;
        loop {
            // print line number
            if color {
                print!("{:3} \x1b[34m|\x1b[39m  ", line);
            } else {
                print!("{:3} |  ", line);
            }

            // print line
            if line >= next.start.line {
                let mut note = String::new();

                // print start
                if line == next.start.line {
                    print!("{}", &lines[line][..next.start.column]);

                    if !color {
                        note.extend(iter::repeat(' ').take(next.start.column));
                    }
                }

                let opt_next = loop {
                    // print highlight
                    let start = if line == next.start.line {
                        next.start.column
                    } else {
                        0
                    };
                    let end = if line == next.end.line {
                        next.end.column
                    } else {
                        lines[line].len()
                    };

                    let str = lines[line][start..end].to_owned();
                    let str = match next.gravity {
                        Gravity::Whole => str,
                        Gravity::EndPlus => str + " ",
                    };
                    print!("{}", highlight(next.color, &str, color, false));
                    if !color {
                        let select: String = match next.gravity {
                            Gravity::Whole => {
                                if next.color == 0 {
                                    iter::repeat('^').take(end - start).collect()
                                } else {
                                    iter::repeat('-').take(end - start).collect()
                                }
                            }
                            Gravity::EndPlus => {
                                if line == next.end.line {
                                    iter::repeat('-')
                                        .take(end - start)
                                        .chain(iter::once('^'))
                                        .collect()
                                } else {
                                    iter::repeat('-').take(end - start).collect()
                                }
                            }
                        };
                        note.push_str(&select);
                    }

                    // print end
                    if line == next.end.line {
                        let start = next.end.column;
                        let opt_next = iter.next();

                        next = match opt_next {
                            Some(next) => {
                                if next.start.line == line {
                                    let end = next.start.column;
                                    print!("{}", &lines[line][start..end]);
                                    if !color {
                                        note.extend(iter::repeat(' ').take(end - start));
                                    }
                                    next
                                } else {
                                    let end = lines[line].len();
                                    print!("{}", &lines[line][start..]);
                                    if !color {
                                        note.extend(iter::repeat(' ').take(end - start));
                                    }
                                    break Some(next);
                                }
                            }
                            None => {
                                let end = lines[line].len();
                                print!("{}", &lines[line][start..]);
                                if !color {
                                    note.extend(iter::repeat(' ').take(end - start));
                                }
                                break None;
                            }
                        };
                    } else {
                        break Some(next);
                    }
                };
                println!();

                // print note
                if !note.is_empty() {
                    if color {
                        print!("    \x1b[34m|\x1b[39m  ");
                    } else {
                        print!("    |  ");
                    }
                    println!("{}", note);
                }

                next = match opt_next {
                    Some(next) => {
                        if next.start.line > line && next.start.line - line > LINE_TOLERANCE {
                            if color {
                                println!("  : \x1b[34m|\x1b[39m");
                            } else {
                                println!("  : |");
                            }
                            line = next.start.line;
                        } else {
                            line += 1;
                        }
                        next
                    }
                    None => break,
                };
            } else {
                println!("{}", &lines[line]);
                line += 1;
            }
        }
    }
}

impl Errors {
    pub fn new() -> Self {
        Self { vec: Vec::new() }
    }
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }
    pub fn push(&mut self, e: Ranged<Error>) {
        self.vec.push(e);
    }
    pub fn print(mut self, file: &str, filename: &str, color: bool) {
        // get file lines
        let lines = file.lines().collect::<Vec<_>>();

        // stable sort as the ranges may start with the same position
        self.vec.sort_by_key(|r| r.1);

        // print errors
        for err in self.vec {
            let err = err.clamp(0, file.len());
            let (start, end) = get_lines(file, err.empty());

            let str = &file[err.1..err.2];

            if color {
                print!("\x1b[1;31merror\x1b[39m: ");
            } else {
                print!("error: ");
            }
            print!(
                "{}",
                match err.0 {
                    Error::UnknownSymbol =>
                        format!("unknown symbol {}", highlight(0, str, color, true)),
                    Error::UnclosedString => "unclosed string".into(),

                    Error::Unexpected(ref e) => format!(
                        "unexpected {}, expected {}",
                        highlight(0, str, color, true),
                        match e {
                            Expected::Token(t) => t.to_string(),
                            Expected::Identifier => "identifier".into(),
                            Expected::Definition => "effect or function definition".into(),
                            Expected::Expression => "expression".into(),
                        }
                    ),
                    Error::UnclosedGroup(_) =>
                        format!("unclosed {}", highlight(0, str, color, true)),

                    Error::UnknownEffect => format!(
                        "effect {} not found in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownEffectFun(h, _) => {
                        format!(
                            "effect {} has no function {}",
                            highlight(1, &file[h.1..h.2], color, true),
                            highlight(0, str, color, true)
                        )
                    }
                    Error::UnknownValue => format!(
                        "value {} not found in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnhandledEffect => format!(
                        "effect {} is not handled in this scope",
                        highlight(0, str, color, true)
                    ),
                }
            );
            if color {
                print!("\x1b[0m");
            }
            println!();

            let mut highlights = vec![Highlight {
                start,
                end,
                color: 0,
                gravity: err.0.gravity(),
            }];
            match err.0 {
                Error::UnknownEffectFun(handler, effect) => {
                    if let Some(effect) = effect {
                        highlights.push(Highlight::from_file(file, effect, 1, Gravity::Whole));
                    }
                    highlights.push(Highlight::from_file(file, handler, 1, Gravity::Whole));
                }
                _ => (),
            }

            print_error(&lines, filename, &highlights, color);
            println!();
        }
    }
}
