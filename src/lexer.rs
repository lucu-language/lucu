use std::{fmt, iter::Peekable, str::Chars};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    // keywords
    Effect,
    Try,
    With,
    Fun,

    // symbols
    At,
    Comma,
    Equals,
    Slash,
    Semicolon,
    Doublecolon,

    // other
    Group(GroupType),
    Identifier,
    String,
}

#[derive(Debug)]
pub struct Tokens(pub Vec<Token>);

fn fmt(tokens: &[Token], f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
    let mut i = 0;
    let mut my_indent = indent;
    while i < tokens.len() {
        let tok = tokens[i];
        i += 1;

        f.write_fmt(format_args!("{:indent$}", "", indent = my_indent))?;
        my_indent = 0;

        match tok.typ {
            TokenType::Group(g) => match g {
                GroupType::Paren => {
                    f.write_str("( ")?;
                    fmt(&tokens[i..i + tok.len], f, 0)?;
                    f.write_str(") ")?;

                    i += tok.len;
                }
                GroupType::Brace => {
                    f.write_str("{\n")?;
                    fmt(&tokens[i..i + tok.len], f, indent + 2)?;
                    f.write_fmt(format_args!("{:indent$}", "", indent = indent))?;
                    f.write_str("}\n")?;

                    i += tok.len;
                    my_indent = indent;
                }
            },
            TokenType::Effect => f.write_str("effect ")?,
            TokenType::Try => f.write_str("try ")?,
            TokenType::With => f.write_str("with ")?,
            TokenType::Fun => f.write_str("fun ")?,
            TokenType::Comma => f.write_str(", ")?,
            TokenType::Equals => f.write_str("= ")?,
            TokenType::Slash => f.write_str("/ ")?,
            TokenType::Semicolon => {
                f.write_str(";\n")?;
                my_indent = indent;
            }
            TokenType::Doublecolon => f.write_str(":: ")?,
            TokenType::Identifier => f.write_str("id ")?,
            TokenType::String => f.write_str("\"...\" ")?,
            TokenType::At => f.write_str("@ ")?,
        }
    }
    Ok(())
}

impl fmt::Display for Tokens {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt(&self.0, f, 0)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum GroupType {
    Paren, // ()
    Brace, // {}
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub typ: TokenType,
    pub place: usize,
    pub len: usize,
}

struct Lexer<'a> {
    tokens: Tokens,
    source: Peekable<Chars<'a>>,
    place: usize,
}

impl Lexer<'_> {
    fn next(&mut self) -> usize {
        let p = self.place;
        self.source.next();
        self.place += 1;
        p
    }
    fn push(&mut self, typ: TokenType) -> Next {
        let place = self.next();
        self.tokens.0.push(Token { typ, place, len: 0 });
        Next::Tokens(1)
    }
}

fn subgroup(l: &mut Lexer) -> (GroupType, usize) {
    let mut len = 0;

    loop {
        match next(l) {
            Next::Tokens(num) => len += num,
            Next::Closing(typ, _) => return (typ, len),
            Next::EOF => panic!(),
        }
    }
}

enum Next {
    Tokens(usize),
    Closing(GroupType, usize),
    EOF,
}

fn next(l: &mut Lexer) -> Next {
    // skip whitespace
    loop {
        match l.source.peek() {
            Some(c) => match c {
                ' ' | '\t' | '\r' | '\n' => _ = l.next(),
                '#' => {
                    l.next();
                    while l.source.peek() != None && l.source.peek() != Some(&'\n') {
                        l.next();
                    }
                }
                _ => break,
            },
            None => break,
        }
    }

    // check symbol
    match l.source.peek() {
        Some(c) => match c {
            '{' => {
                let p = l.next();
                let i = l.tokens.0.len();
                l.tokens.0.push(Token {
                    typ: TokenType::Group(GroupType::Brace),
                    place: p,
                    len: 0,
                });

                let group = subgroup(l);
                if group.0 == GroupType::Brace {
                    l.tokens.0[i].len = group.1;
                    Next::Tokens(group.1 + 1)
                } else {
                    panic!();
                }
            }
            '(' => {
                let p = l.next();
                let i = l.tokens.0.len();
                l.tokens.0.push(Token {
                    typ: TokenType::Group(GroupType::Paren),
                    place: p,
                    len: 0,
                });

                let group = subgroup(l);
                if group.0 == GroupType::Paren {
                    l.tokens.0[i].len = group.1;
                    Next::Tokens(group.1 + 1)
                } else {
                    panic!();
                }
            }
            '}' => Next::Closing(GroupType::Brace, l.next()),
            ')' => Next::Closing(GroupType::Paren, l.next()),
            ';' => l.push(TokenType::Semicolon),
            ',' => l.push(TokenType::Comma),
            '/' => l.push(TokenType::Slash),
            '@' => l.push(TokenType::At),
            '=' => l.push(TokenType::Equals),
            ':' => {
                let p = l.next();
                if l.source.peek() == Some(&':') {
                    l.next();
                    l.tokens.0.push(Token {
                        typ: TokenType::Doublecolon,
                        place: p,
                        len: 0,
                    });
                    Next::Tokens(1)
                } else {
                    // single colon
                    todo!();
                }
            }
            '"' => {
                let p = l.next();
                let mut escaped = false;
                loop {
                    match l.source.peek() {
                        Some(&'\\') => escaped = !escaped,
                        Some(&'"') if !escaped => break,
                        Some(_) => escaped = false,
                        None => panic!(),
                    }
                    l.next();
                }
                l.next();
                l.tokens.0.push(Token {
                    typ: TokenType::String,
                    place: p,
                    len: 0,
                });
                Next::Tokens(1)
            }
            c if c.is_ascii_alphabetic() => {
                let p = l.place;
                let mut words = vec![
                    ("effect", TokenType::Effect),
                    ("try", TokenType::Try),
                    ("with", TokenType::With),
                    ("fun", TokenType::Fun),
                ];
                loop {
                    let char = match l.source.peek() {
                        None => None,
                        Some(&char) if !char.is_ascii_alphanumeric() => None,
                        Some(&char) => Some(char),
                    };
                    let Some(char) = char else {
                        if words.len() == 1 && words[0].0 == "" {
                            l.tokens.0.push(Token {
                                typ: words.remove(0).1,
                                place: p,
                                len: 0,
                            });
                        } else {
                            l.tokens.0.push(Token {
                                typ: TokenType::Identifier,
                                place: p,
                                len: 0,
                            });
                        }
                        return Next::Tokens(1);
                    };

                    // get next word
                    l.next();
                    words.retain_mut(|word| {
                        let mut chars = word.0.chars();
                        let first = chars.next();
                        word.0 = chars.as_str();

                        match first {
                            Some(c) => c == char,
                            None => false,
                        }
                    });
                }
            }
            _ => todo!(),
        },
        None => Next::EOF,
    }
}

pub fn tokenize(s: &str) -> Tokens {
    let mut lexer = Lexer {
        tokens: Tokens(vec![]),
        source: s.chars().peekable(),
        place: 0,
    };

    loop {
        match next(&mut lexer) {
            Next::Tokens(_) => (),
            Next::Closing(_, _) => panic!(),
            Next::EOF => break,
        }
    }

    lexer.tokens
}
