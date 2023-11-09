use std::{fmt, iter::Peekable, str::Chars};

use crate::error::{Error, Errors, FileIdx, Ranged};

#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    // Keywords
    Effect,
    Fun,
    Try,
    With,
    If,
    Else,
    Yeet,
    Yeets,
    Handle,
    Let,
    Mut,
    Loop,
    Import,
    Cast,
    Const,

    // Symbols
    Semicolon,
    Dot,
    DoubleDot,
    Slash,
    Comma,
    Equals,
    Bang,
    DoubleEquals,
    Dash,
    DoubleDash,
    TripleDash,
    Arrow,
    Caret,
    Asterisk,
    Plus,
    DoublePlus,
    Less,
    Greater,
    Ampersand,
    At,
    Open(Group),
    Close(Group),

    // Literals
    String(String),
    Character(String),
    Ident(String),
    Int(Option<u64>), // possibly too large

    // Error
    UnknownSymbol,
}

pub const GENERIC: char = '`';

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Token::Effect => "'effect'".into(),
                Token::Fun => "'fun'".into(),
                Token::Try => "'try'".into(),
                Token::With => "'with'".into(),
                Token::If => "'if'".into(),
                Token::Else => "'else'".into(),
                Token::Yeet => "'fail'".into(),
                Token::Yeets => "'fails'".into(),
                Token::Handle => "'handle'".into(),
                Token::Let => "'let'".into(),
                Token::Mut => "'mut'".into(),
                Token::Loop => "'loop'".into(),
                Token::Import => "'import'".into(),
                Token::Cast => "'cast'".into(),
                Token::Const => "'const'".into(),
                Token::Semicolon => "';'".into(),
                Token::Dot => "'.'".into(),
                Token::DoubleDot => "'..'".into(),
                Token::Slash => "'/'".into(),
                Token::Comma => "','".into(),
                Token::Equals => "'='".into(),
                Token::Bang => "'!'".into(),
                Token::DoubleEquals => "'=='".into(),
                Token::Dash => "'-'".into(),
                Token::DoubleDash => "'--'".into(),
                Token::TripleDash => "'---'".into(),
                Token::Arrow => "'->'".into(),
                Token::Caret => "'^'".into(),
                Token::Asterisk => "'*'".into(),
                Token::Plus => "'+'".into(),
                Token::DoublePlus => "'++'".into(),
                Token::Less => "'<'".into(),
                Token::Greater => "'>'".into(),
                Token::Ampersand => "'&'".into(),
                Token::At => "'@'".into(),
                Token::Open(Group::Brace) => "'{'".into(),
                Token::Open(Group::Paren) => "'('".into(),
                Token::Open(Group::Bracket) => "'['".into(),
                Token::Close(Group::Brace) => "'}'".into(),
                Token::Close(Group::Paren) => "')'".into(),
                Token::Close(Group::Bracket) => "']'".into(),
                Token::String(s) => format!("\"{}\"", s),
                Token::Character(s) => format!("'{}'", s),
                Token::Ident(s) => format!("'{}'", s),
                Token::Int(i) => format!("'{}'", i.unwrap_or(u64::MAX)),
                Token::UnknownSymbol => "'ERR'".into(),
            }
        )
    }
}

impl Token {
    pub fn is_anchor(&self) -> bool {
        matches!(self, Token::Semicolon | Token::Comma | Token::Close(_))
    }

    /// if a statement line ends with this token, it must continue on the next line
    /// these include all prefix and infix operators
    pub fn unfinished_statement(&self) -> bool {
        matches!(
            self,
            Token::With
                | Token::Let
                | Token::Mut
                | Token::Else
                | Token::Dot
                | Token::Bang
                | Token::Yeet
                | Token::Try
                | Token::If
                | Token::Effect
                | Token::Fun
                | Token::Slash
                | Token::Equals
                | Token::Greater
                | Token::Less
                | Token::DoubleEquals
                | Token::Dash
                | Token::Asterisk
                | Token::Plus
                | Token::Comma
                | Token::Import
                | Token::Ampersand
                | Token::At
                | Token::Arrow
                | Token::Loop
                | Token::Cast
                | Token::Open(_)

                // prevents double semicolons
                | Token::Semicolon
        )
    }

    /// if a statement line starts with this token, it must be attached to the previous line
    /// these include all infix and suffix operators
    pub fn continues_statement(&self) -> bool {
        matches!(
            self,
            Token::Yeets
                | Token::Else
                | Token::Comma
                | Token::Close(_)
                | Token::Open(Group::Brace)
                | Token::Dot
                | Token::Slash
                | Token::Equals
                | Token::Greater
                | Token::Less
                | Token::DoubleEquals
                | Token::Dash
                | Token::Asterisk
                | Token::Plus
                | Token::Arrow

                // prevents double semicolons
                | Token::Semicolon
        )
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Group {
    Brace,
    Paren,
    Bracket,
}

pub struct Tokenizer<'a> {
    next: Peekable<Chars<'a>>,
    pos: usize,

    pub errors: &'a mut Errors,
    pub file: FileIdx,

    brace: Vec<bool>,
    prev_unfinished: bool,
    peek: Option<Ranged<Token>>,
}

impl<'a> Tokenizer<'a> {
    pub fn new(s: &'a str, file: FileIdx, errors: &'a mut Errors) -> Self {
        Self {
            next: s.chars().peekable(),
            pos: 0,
            brace: vec![],
            prev_unfinished: true,
            peek: None,
            errors,
            file,
        }
    }
    fn next_char(&mut self) -> Option<char> {
        match self.next.next() {
            Some(c) => {
                self.pos += 1;
                Some(c)
            }
            None => None,
        }
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = Ranged<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        // peeked token?
        if let Some(token) = self.peek.take() {
            self.prev_unfinished = token.0.unfinished_statement();
            return Some(token);
        }

        // remember newline between tokens
        let mut prev_newline = None;

        // get next char
        let char = loop {
            match self.next_char() {
                // skip newline
                Some('\n') => {
                    if prev_newline.is_none() {
                        prev_newline = Some(self.pos - 1);
                    }
                }
                // skip whitespace
                Some(' ') | Some('\t') | Some('\r') => {}
                // skip comment
                Some('#') => loop {
                    if prev_newline.is_none() {
                        prev_newline = Some(self.pos - 1);
                    }
                    match self.next_char() {
                        Some('\n') | None => break,
                        Some(_) => {}
                    }
                },
                Some(c) => break c,
                None => {
                    if let Some(newline) = prev_newline.filter(|_| {
                        self.brace.last().copied().unwrap_or(false) && !self.prev_unfinished
                    }) {
                        return Some(Ranged(Token::Semicolon, newline, newline + 1, self.file));
                    } else {
                        return None;
                    }
                }
            }
        };

        let pos = self.pos - 1;

        // get next token
        let token = match char {
            ';' => Token::Semicolon,
            '/' => Token::Slash,
            ',' => Token::Comma,
            '(' => Token::Open(Group::Paren),
            '[' => Token::Open(Group::Bracket),
            '{' => Token::Open(Group::Brace),
            ')' => Token::Close(Group::Paren),
            ']' => Token::Close(Group::Bracket),
            '}' => Token::Close(Group::Brace),
            '!' => Token::Bang,
            '*' => Token::Asterisk,
            '<' => Token::Less,
            '>' => Token::Greater,
            '^' => Token::Caret,
            '&' => Token::Ampersand,
            '@' => Token::At,
            '.' => match self.next.peek() {
                Some(&'.') => {
                    self.next_char();
                    Token::DoubleDot
                }
                _ => Token::Dot,
            },
            '-' => match self.next.peek() {
                Some(&'-') => {
                    self.next_char();
                    match self.next.peek() {
                        Some(&'-') => {
                            self.next_char();
                            Token::TripleDash
                        }
                        _ => Token::DoubleDash,
                    }
                }
                Some(&'>') => {
                    self.next_char();
                    Token::Arrow
                }
                _ => Token::Dash,
            },
            '+' => match self.next.peek() {
                Some(&'+') => {
                    self.next_char();
                    Token::DoublePlus
                }
                _ => Token::Plus,
            },
            '=' => {
                match self.next.peek() {
                    Some(&'=') => {
                        self.next_char();
                        Token::DoubleEquals
                    }
                    _ => {
                        // single
                        Token::Equals
                    }
                }
            }
            '"' | '\'' => {
                // string / character
                let term = char;
                let token = |s| {
                    if term == '"' {
                        Token::String(s)
                    } else {
                        Token::Character(s)
                    }
                };

                let mut full = String::new();
                loop {
                    match self.next_char() {
                        Some(c) if c == term => break token(full),
                        Some('\n') => {
                            self.errors.push(Ranged(
                                Error::UnclosedString,
                                pos,
                                self.pos - 1,
                                self.file,
                            ));
                            break token(full);
                        }
                        None => {
                            self.errors.push(Ranged(
                                Error::UnclosedString,
                                pos,
                                self.pos,
                                self.file,
                            ));
                            break token(full);
                        }

                        Some('\\') => full.push(match self.next_char() {
                            Some('n') => '\n',
                            Some('t') => '\t',
                            Some('r') => '\r',
                            Some('"') => '"',
                            Some('\'') => '\'',
                            Some('\\') => '\\',
                            Some('\n') => '\n',

                            Some(c) => {
                                self.errors.push(Ranged(
                                    Error::UnknownEscape,
                                    self.pos - 2,
                                    self.pos,
                                    self.file,
                                ));
                                c
                            }
                            None => {
                                self.errors.push(Ranged(
                                    Error::UnclosedString,
                                    pos,
                                    self.pos,
                                    self.file,
                                ));
                                break token(full);
                            }
                        }),
                        Some(c) => full.push(c),
                    }
                }
            }
            'a'..='z' | 'A'..='Z' | '_' | GENERIC => {
                // get word
                let mut word = String::new();
                word.push(char);

                loop {
                    match self.next.peek() {
                        Some(&c @ ('a'..='z' | 'A'..='Z' | '0'..='9' | '_')) => {
                            self.next_char();
                            word.push(c);
                        }
                        _ => break,
                    }
                }

                // find keyword
                match word.as_str() {
                    "effect" => Token::Effect,
                    "fun" => Token::Fun,
                    "try" => Token::Try,
                    "with" => Token::With,
                    "if" => Token::If,
                    "else" => Token::Else,
                    "yeet" | "fail" => Token::Yeet,
                    "yeets" | "fails" => Token::Yeets,
                    "handle" => Token::Handle,
                    "let" => Token::Let,
                    "mut" => Token::Mut,
                    "loop" => Token::Loop,
                    "import" => Token::Import,
                    "cast" => Token::Cast,
                    "const" => Token::Const,
                    _ => Token::Ident(word),
                }
            }
            '0'..='9' => {
                self.prev_unfinished = false;

                // number
                let mut num = u64::from(char.to_digit(10).unwrap());
                let mut too_large = false;
                loop {
                    match self.next.peek() {
                        Some(&'_') => {}
                        Some(&('0'..='9')) => {
                            // try to multiply by 10 and add the new digit
                            num = match num.checked_mul(10).and_then(|num| {
                                num.checked_add(u64::from(
                                    self.next_char().unwrap().to_digit(10).unwrap(),
                                ))
                            }) {
                                Some(num) => num,
                                None => {
                                    too_large = true;
                                    0
                                }
                            }
                        }
                        _ => break,
                    }
                }
                Token::Int(if too_large {
                    self.errors.push(Ranged(
                        Error::IntTooLarge(u64::MAX),
                        pos,
                        self.pos,
                        self.file,
                    ));
                    None
                } else {
                    Some(num)
                })
            }
            _ => {
                self.prev_unfinished = false;
                Token::UnknownSymbol
            }
        };

        match token {
            Token::Open(g) => {
                self.brace.push(g == Group::Brace);
            }
            Token::Close(_) => {
                self.brace.pop();
            }
            _ => {}
        }

        if let Some(newline) = prev_newline.filter(|_| {
            self.brace.last().copied().unwrap_or(false)
                && !self.prev_unfinished
                && !token.continues_statement()
        }) {
            self.peek = Some(Ranged(token, pos, self.pos, self.file));
            Some(Ranged(Token::Semicolon, newline, newline + 1, self.file))
        } else {
            self.prev_unfinished = token.unfinished_statement();
            Some(Ranged(token, pos, self.pos, self.file))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.next.size_hint().1)
    }
}
