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
    UnknownEffectFun(Ranged<()>),
    UnknownValue,
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
    Start,
    EndPlus,
}

impl Error {
    fn gravity(&self) -> Gravity {
        match self {
            Error::UnknownSymbol => Gravity::Start,
            Error::UnclosedString => Gravity::EndPlus,
            Error::Unexpected(_) => Gravity::Start,
            Error::UnclosedGroup(_) => Gravity::Start,
            Error::UnknownEffect => Gravity::Start,
            Error::UnknownValue => Gravity::Start,
            Error::UnknownEffectFun(_) => Gravity::Start,
        }
    }
}

pub struct Errors {
    vec: Vec<Ranged<Error>>,
}

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

            let highlight = |i: u8, s: &str, bold: bool| {
                if color {
                    let mut bg = 41 + ((i + 1) % 14);
                    if bg >= 48 {
                        bg = 101 + (bg - 48);
                    }
                    if bold {
                        format!("\x1b[{};30m {} \x1b[49;39m", bg, s)
                    } else {
                        format!("\x1b[1;{};30m {} \x1b[0m", bg, s)
                    }
                } else {
                    format!("'{}'", s)
                }
            };

            if color {
                print!("\x1b[1;31merror\x1b[39m: ");
            } else {
                print!("error: ");
            }
            print!(
                "{}",
                match err.0 {
                    Error::UnknownSymbol => format!("unknown symbol {}", highlight(0, str, true)),
                    Error::UnclosedString => "unclosed string".into(),

                    Error::Unexpected(ref e) => format!(
                        "unexpected {}, expected {}",
                        highlight(0, str, true),
                        match e {
                            Expected::Token(t) => t.to_string(),
                            Expected::Identifier => "identifier".into(),
                            Expected::Definition => "effect or function definition".into(),
                            Expected::Expression => "expression".into(),
                        }
                    ),
                    Error::UnclosedGroup(_) => format!("unclosed {}", highlight(0, str, true)),

                    Error::UnknownEffect =>
                        format!("effect {} not found in scope", highlight(0, str, true)),
                    Error::UnknownEffectFun(e) => format!(
                        "effect {} has no function {}",
                        highlight(1, &file[e.1..e.2], true),
                        highlight(0, str, true)
                    ),
                    Error::UnknownValue =>
                        format!("value {} not found in scope", highlight(0, str, true)),
                }
            );
            if color {
                print!("\x1b[0m");
            }
            println!();

            if color {
                println!(
                    "   \x1b[34m/->\x1b[39m {}:{}:{}",
                    filename, start.line, start.column
                );
                println!("    \x1b[34m|\x1b[39m");
            } else {
                println!("   /-> {}:{}:{}", filename, start.line, start.column);
                println!("    |");
            }

            for line in (start.line)..=(end.line) {
                let select_start = if line == start.line { start.column } else { 0 };
                let select_end = if line == end.line {
                    end.column
                } else {
                    lines[line].len()
                };

                if color {
                    print!(
                        "{:3} \x1b[34m|\x1b[39m  {}",
                        line,
                        &lines[line][..select_start]
                    );
                    print!(
                        "{}",
                        highlight(0, &lines[line][select_start..select_end], false)
                    );
                    print!("{}", &lines[line][select_end..]);
                    println!();
                } else {
                    println!("{:3} |  {}", line, lines[line]);

                    let select: String = match err.0.gravity() {
                        Gravity::Start => {
                            if line == start.line {
                                Iterator::chain(
                                    iter::repeat(' ').take(select_start),
                                    iter::once('^').chain(
                                        iter::repeat('-').take(select_end - select_start - 1),
                                    ),
                                )
                                .collect()
                            } else {
                                Iterator::chain(
                                    iter::repeat(' ').take(select_start),
                                    iter::repeat('-').take(select_end - select_start),
                                )
                                .collect()
                            }
                        }
                        Gravity::EndPlus => {
                            if line == end.line {
                                Iterator::chain(
                                    iter::repeat(' ').take(select_start),
                                    iter::repeat('-')
                                        .take(select_end - select_start)
                                        .chain(iter::once('^')),
                                )
                                .collect()
                            } else {
                                Iterator::chain(
                                    iter::repeat(' ').take(select_start),
                                    iter::repeat('-').take(select_end - select_start),
                                )
                                .collect()
                            }
                        }
                    };
                    println!("    |  {}", select);
                }
            }
            println!();
        }
    }
}
