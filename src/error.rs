use std::{collections::HashMap, iter};

use crate::{
    lexer::{Group, Token},
    vecmap::{vecmap_index, VecMap},
};

vecmap_index!(FileIdx);

#[derive(Debug, Clone, Copy)]
pub struct Ranged<T>(pub T, pub usize, pub usize, pub FileIdx);

impl<T> Ranged<T> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Ranged<U> {
        Ranged(f(self.0), self.1, self.2, self.3)
    }
    pub fn empty(&self) -> Ranged<()> {
        Ranged((), self.1, self.2, self.3)
    }
    pub fn with<U>(&self, val: U) -> Ranged<U> {
        Ranged(val, self.1, self.2, self.3)
    }
    pub fn clamp(self, min: usize, max: usize) -> Self {
        Ranged(
            self.0,
            self.1.clamp(min, max),
            self.2.clamp(min, max),
            self.3,
        )
    }
}

pub type Range = Ranged<()>;

#[allow(dead_code)]
pub enum Error {
    // lexer
    UnknownSymbol,
    UnknownEscape,
    UnclosedString,
    IntTooLarge(u64),

    // parser
    Unexpected(Expected),
    UnclosedGroup(Group),
    UnresolvedLibrary(String),
    NoSuchDirectory(String),
    NakedRange,

    // name resolution
    UnknownEffectFun(Option<Ranged<()>>, Option<Ranged<()>>),
    UnknownField(Option<Ranged<()>>, Option<Ranged<()>>),
    UnknownPackageValue(Range),
    UnknownPackageEffect(Range),
    UnknownPackageFunction(Range),
    UnknownValue,
    UnknownFunction,
    UnknownValueOrPackage,
    UnknownEffect,
    UnknownPackage,
    UnknownType,
    UnhandledEffect,
    MultipleEffects(Vec<Ranged<()>>),

    // type analysis
    ExpectedType(Option<Ranged<()>>),
    ExpectedHandler(String),
    ExpectedFunction(String),
    ExpectedEffect(String, Option<Ranged<()>>),
    ExpectedArray(String),
    TypeMismatch(String, String),
    ParameterMismatch(usize, usize),
    NestedHandlers,
    TryReturnsHandler,
    NotEnoughInfo,

    // borrow checker
    AssignImmutable(Option<Range>),
    AssignExpression,
    AssignImmutableView(Option<Range>),
    MoveImmutableView(Option<Range>, Option<Range>),

    // invalid values
    UndefinedView(String),
    ZeroinitView(String),
    NeverValue,
}

pub enum Expected {
    Token(Token),
    Identifier,
    Definition,
    Expression,
    String,
    Type,
    ArrayKind,
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
            Error::UnclosedString => Gravity::EndPlus,
            _ => Gravity::Whole,
        }
    }
}

pub struct Errors {
    pub files: VecMap<FileIdx, File>,
    vec: Vec<Ranged<Error>>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct LinePos {
    pub line: usize,
    pub column: usize,
}

pub fn get_lines(file: &str, range: Ranged<()>) -> (LinePos, LinePos) {
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
    file: FileIdx,
    start: LinePos,
    end: LinePos,
    color: usize,
    gravity: Gravity,
}

impl Highlight {
    fn from_file(files: &VecMap<FileIdx, File>, range: Ranged<()>, color: usize) -> Self {
        let file = &files[range.3].content;
        let (start, end) = get_lines(file, range);
        Self {
            file: range.3,
            start,
            end,
            color,
            gravity: Gravity::Whole,
        }
    }
}

fn highlight(i: usize, s: &str, color: bool, bold: bool) -> String {
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

fn print_error(files: &VecMap<FileIdx, File>, highlights: &[Highlight], color: bool) {
    let mut map = HashMap::new();
    for highlight in highlights.iter() {
        if !map.contains_key(&highlight.file) {
            map.insert(highlight.file, vec![highlight]);
        } else {
            map.get_mut(&highlight.file).unwrap().push(highlight);
        }
    }

    let mut sorted_partition = Vec::new();
    sorted_partition.extend(map.into_iter());
    sorted_partition.sort_unstable_by_key(|&(f, _)| usize::from(f));

    for (idx, highlights) in sorted_partition.into_iter() {
        // get file lines
        let lines = files[idx].content.lines().collect::<Vec<_>>();
        let filename = &files[idx].name;

        if let Some(first) = highlights.first() {
            // print header
            if color {
                println!(
                    "   \x1b[34m/->\x1b[39m {}:{}:{}",
                    filename,
                    first.start.line + 1,
                    first.start.column + 1
                );
                println!("    \x1b[34m|\x1b[39m");
            } else {
                println!(
                    "   /-> {}:{}:{}",
                    filename,
                    first.start.line + 1,
                    first.start.column + 1
                );
                println!("    |");
            }
        }

        let mut sorted = highlights;
        sorted.sort_unstable_by_key(|h| h.start);

        if let Some(&first) = sorted.first() {
            let mut iter = sorted.iter().copied();
            let mut next = iter.next().unwrap_or(first);
            let mut line = first.start.line;
            loop {
                // print line number
                if color {
                    print!("{:3} \x1b[34m|\x1b[39m  ", line + 1);
                } else {
                    print!("{:3} |  ", line + 1);
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

        if color {
            println!("    \x1b[34m|\x1b[39m");
        } else {
            println!("    |");
        }
    }
}

pub struct File {
    pub content: String,
    pub name: String,
}

impl Errors {
    pub fn new() -> Self {
        Self {
            vec: Vec::new(),
            files: VecMap::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }
    pub fn push(&mut self, e: Ranged<Error>) {
        self.vec.push(e);
    }
    pub fn print(mut self, color: bool) {
        // stable sort as the ranges may start with the same position
        self.vec.sort_by_key(|r| r.1);

        // print errors
        for err in self.vec {
            let file = &self.files[err.3].content;

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
                    Error::UnknownEscape => format!(
                        "unknown escape sequence '{}'",
                        highlight(0, str, color, true)
                    ),
                    Error::IntTooLarge(max) =>
                        format!("integer literal too large: value exceeds limit of {}", max),

                    Error::Unexpected(ref e) => format!(
                        "unexpected {}, expected {}",
                        highlight(0, str, color, true),
                        match e {
                            Expected::Token(t) => t.to_string(),
                            Expected::Identifier => "identifier".into(),
                            Expected::Definition => "effect or function definition".into(),
                            Expected::Expression => "expression".into(),
                            Expected::Type => "type".into(),
                            Expected::String => "string literal".into(),
                            Expected::ArrayKind => "int literal".into(),
                        }
                    ),
                    Error::UnclosedGroup(_) =>
                        format!("unclosed {}", highlight(0, str, color, true)),
                    Error::UnresolvedLibrary(ref s) => format!("unresolved library '{}'", s),
                    Error::NoSuchDirectory(ref s) => format!("directory '{}' does not exist", s),
                    Error::NakedRange => format!("cannot use range literal as value"),

                    Error::UnknownEffect => format!(
                        "effect {} not found in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownPackage => format!(
                        "package {} not found in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownEffectFun(effect, _) => {
                        format!(
                            "effect {}has no function {}",
                            effect
                                .map(|effect| highlight(
                                    1,
                                    &self.files[effect.3].content[effect.1..effect.2],
                                    color,
                                    true
                                ) + " ")
                                .unwrap_or(String::new()),
                            highlight(0, str, color, true)
                        )
                    }
                    Error::UnknownValue => format!(
                        "value {} not found in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownFunction => format!(
                        "function {} not found in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownValueOrPackage => format!(
                        "value or package {} not found in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnhandledEffect => format!(
                        "effect {} not handled in this scope",
                        highlight(0, str, color, true)
                    ),
                    Error::MultipleEffects(_) => format!(
                        "value {} defined by multiple effects in scope",
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownField(typ, _) => format!(
                        "type {}has no field {}",
                        typ.map(|effect| highlight(
                            1,
                            &self.files[effect.3].content[effect.1..effect.2],
                            color,
                            true
                        ) + " ")
                            .unwrap_or(String::new()),
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownPackageValue(pkg) => format!(
                        "package {} has no value {}",
                        highlight(1, &self.files[pkg.3].content[pkg.1..pkg.2], color, true),
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownPackageFunction(pkg) => format!(
                        "package {} has no function {}",
                        highlight(1, &self.files[pkg.3].content[pkg.1..pkg.2], color, true),
                        highlight(0, str, color, true)
                    ),
                    Error::UnknownPackageEffect(pkg) => format!(
                        "package {} has no effect {}",
                        highlight(1, &self.files[pkg.3].content[pkg.1..pkg.2], color, true),
                        highlight(0, str, color, true)
                    ),

                    Error::UnknownType =>
                        format!("type {} not found in scope", highlight(0, str, color, true)),
                    Error::ExpectedType(_) => format!(
                        "expected a type, found value {}",
                        highlight(0, str, color, true)
                    ),
                    Error::ExpectedHandler(ref found) =>
                        format!("type mismatch: expected an effect handler, found {}", found),
                    Error::ExpectedFunction(ref found) =>
                        format!("type mismatch: expected a function, found {}", found),
                    Error::TypeMismatch(ref expected, ref found) =>
                        format!("type mismatch: expected {}, found {}", expected, found),
                    Error::ParameterMismatch(expected, ref found) =>
                        format!("expected {} argument(s), found {}", expected, found),
                    Error::ExpectedEffect(ref found, _) =>
                        format!("expected an effect type, found {}", found),
                    Error::NestedHandlers =>
                        "effect handlers may not escape other effect handlers".into(),
                    Error::TryReturnsHandler =>
                        "effect handlers may not escape try/with expressions".into(),
                    Error::ExpectedArray(ref found) =>
                        format!("expected an array type, found {}", found),
                    Error::NotEnoughInfo => format!("cannot resolve type: type annotations needed"),

                    Error::AssignImmutable(_) => "cannot assign to immutable variable".into(),
                    Error::AssignExpression => "cannot assign to expression".into(),
                    Error::AssignImmutableView(_) =>
                        format!("cannot assign to mutable variable: value is an immutable view"),
                    Error::MoveImmutableView(_, _) =>
                        format!("cannot move into mutable parameter: value is an immutable view"),

                    Error::UndefinedView(ref ty) =>
                        format!("cannot leave view type {} undefined", ty),
                    Error::ZeroinitView(ref ty) =>
                        format!("cannot zero-initialize view type {}", ty),
                    Error::NeverValue => format!("cannot create a value of type never"),
                }
            );
            if color {
                print!("\x1b[0m");
            }
            println!();

            let mut highlights = vec![Highlight {
                file: err.3,
                start,
                end,
                color: 0,
                gravity: err.0.gravity(),
            }];
            match err.0 {
                Error::ExpectedType(value) => {
                    if let Some(value) = value {
                        highlights.push(Highlight::from_file(&self.files, value, 1));
                    }
                }
                Error::ExpectedEffect(_, value) => {
                    if let Some(value) = value {
                        highlights.push(Highlight::from_file(&self.files, value, 1));
                    }
                }
                Error::UnknownEffectFun(effect, handler) => {
                    if let Some(effect) = effect {
                        highlights.push(Highlight::from_file(&self.files, effect, 1));
                    }
                    if let Some(handler) = handler {
                        highlights.push(Highlight::from_file(&self.files, handler, 1));
                    }
                }
                Error::UnknownField(ty, handler) => {
                    if let Some(effect) = ty {
                        highlights.push(Highlight::from_file(&self.files, effect, 1));
                    }
                    if let Some(handler) = handler {
                        highlights.push(Highlight::from_file(&self.files, handler, 1));
                    }
                }
                Error::UnknownPackageValue(pkg) => {
                    highlights.push(Highlight::from_file(&self.files, pkg, 1));
                }
                Error::UnknownPackageEffect(pkg) => {
                    highlights.push(Highlight::from_file(&self.files, pkg, 1));
                }
                Error::MultipleEffects(effects) => {
                    for effect in effects {
                        highlights.push(Highlight::from_file(&self.files, effect, 1));
                    }
                }
                Error::AssignImmutable(def) => {
                    if let Some(def) = def {
                        highlights.push(Highlight::from_file(&self.files, def, 1));
                    }
                }
                Error::AssignImmutableView(def) => {
                    if let Some(def) = def {
                        highlights.push(Highlight::from_file(&self.files, def, 1));
                    }
                }
                Error::MoveImmutableView(def, param) => {
                    if let Some(def) = def {
                        highlights.push(Highlight::from_file(&self.files, def, 1));
                    }
                    if let Some(param) = param {
                        highlights.push(Highlight::from_file(&self.files, param, 2));
                    }
                }
                _ => (),
            }

            print_error(&self.files, &highlights, color);
        }
    }
}
