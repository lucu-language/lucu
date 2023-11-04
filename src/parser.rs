use std::{
    borrow::Cow,
    collections::HashMap,
    matches,
    path::{Path, PathBuf},
};

use either::Either;

use crate::{
    error::{Error, Expected, FileIdx, Range, Ranged},
    lexer::{Group, Token, Tokenizer},
    vecmap::{vecmap_index, VecMap},
};

vecmap_index!(ExprIdx);
vecmap_index!(TypeIdx);
vecmap_index!(Ident);
vecmap_index!(PackageIdx);

vecmap_index!(ParamIdx);
vecmap_index!(FunIdx);
vecmap_index!(EffIdx);
vecmap_index!(EffFunIdx);

impl Default for ExprIdx {
    fn default() -> Self {
        ExprIdx(0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Assign,
    Equals,
    Less,
    Greater,
    Divide,
    Multiply,
    Subtract,
    Add,
    Index,
    Range,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    PostIncrement,
    Reference,
    Cast,
}

impl BinOp {
    fn from_token(value: &Token) -> Option<BinOp> {
        match value {
            Token::Equals => Some(BinOp::Assign),
            Token::Slash => Some(BinOp::Divide),
            Token::DoubleEquals => Some(BinOp::Equals),
            Token::Dash => Some(BinOp::Subtract),
            Token::Asterisk => Some(BinOp::Multiply),
            Token::Plus => Some(BinOp::Add),
            Token::Less => Some(BinOp::Less),
            Token::Greater => Some(BinOp::Greater),
            Token::DoubleDot => Some(BinOp::Range),
            _ => None,
        }
    }
}

#[derive(Debug, Default)]
pub enum Expression {
    Body(Body),
    Loop(ExprIdx),

    Call(ExprIdx, Vec<ExprIdx>),
    Member(ExprIdx, Ident),
    IfElse(ExprIdx, ExprIdx, Option<ExprIdx>),
    BinOp(ExprIdx, BinOp, ExprIdx),
    UnOp(ExprIdx, UnOp),
    Yeet(Option<ExprIdx>),
    Let(bool, Ident, Option<TypeIdx>, ExprIdx),

    TryWith(ExprIdx, Option<ExprIdx>),
    Handler(Handler),

    Array(Vec<ExprIdx>),
    String(String),
    Character(String),
    Int(u64),
    Ident(Ident),
    Uninit,

    #[default]
    Error, // error at parsing, coerces to any type
}

#[derive(Debug)]
pub struct Body {
    pub main: Vec<ExprIdx>,
    pub last: Option<ExprIdx>,
}

impl Body {
    fn parse_or_default(tk: &mut Tokens) -> Ranged<Expression> {
        let start = tk.pos_start();
        match Self::parse_or_skip(tk) {
            Some(body) => body.map(Expression::Body),
            None => Ranged(Expression::Error, start, start, tk.iter.file),
        }
    }
}

#[derive(Debug, Default)]
pub struct Lambda {
    pub inputs: VecMap<ParamIdx, Ident>,
    pub body: ExprIdx,
}

#[derive(Debug)]
pub enum Handler {
    Full {
        fail_type: FailType,
        effect: EffectIdent,
        functions: Vec<Function>,
    },
    Lambda(Lambda),
}

impl Handler {
    pub fn functions(
        &self,
        effect: &Effect,
    ) -> Either<
        impl Iterator<Item = (Cow<FunDecl>, ExprIdx)>,
        impl Iterator<Item = (Cow<FunDecl>, ExprIdx)>,
    > {
        match *self {
            Handler::Full { ref functions, .. } => {
                Either::Left(functions.iter().map(|f| (Cow::Borrowed(&f.decl), f.body)))
            }
            Handler::Lambda(Lambda {
                body, ref inputs, ..
            }) => {
                let mut decl: FunDecl = effect.functions.values().next().unwrap().clone();

                // set signature input names
                for (idx, &input) in inputs.iter(ParamIdx) {
                    decl.sign.inputs[idx].name = input;
                }

                Either::Right(std::iter::once((Cow::Owned(decl), body)))
            }
        }
    }
}

#[derive(Debug, Default, Clone)]
pub enum Type {
    Never,
    Path(Ident),
    Handler(Ident, FailType),

    Generic(Ident),
    GenericHandler(Ident, FailType),

    Pointer(TypeIdx),
    Const(TypeIdx),
    ConstArray(u64, TypeIdx),
    Slice(TypeIdx),

    #[default]
    Error, // error at parsing, coerces to any type
}

#[derive(Debug, Clone, Copy)]
pub enum FailType {
    Never,
    None,
    Some(TypeIdx),
}

#[derive(Debug, Clone, Copy)]
pub struct EffectIdent {
    pub package: Option<Ident>,
    pub effect: Ident,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub mutable: bool,
    pub const_generic: bool,
    pub name: Ident,
    pub ty: TypeIdx,
}

#[derive(Debug, Clone)]
pub struct FunSign {
    pub inputs: VecMap<ParamIdx, Param>,
    pub output: Option<TypeIdx>,
    pub effects: Vec<EffectIdent>,
}

#[derive(Debug, Clone)]
pub struct FunDecl {
    pub name: Ident,
    pub sign: FunSign,
    pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone)]
pub enum AttributeValue {
    String(Ranged<String>),
    Type(TypeIdx),
}

#[derive(Debug, Clone)]
pub struct Attribute {
    pub name: Ident,
    pub settings: Vec<(Ident, AttributeValue)>,
}

#[derive(Debug)]
pub struct Function {
    pub decl: FunDecl,
    pub body: ExprIdx,
}

#[derive(Debug)]
pub struct Effect {
    pub name: Ident,
    pub functions: VecMap<EffFunIdx, FunDecl>,
    pub attributes: Vec<Attribute>,
}

#[derive(Default)]
pub struct Package {
    pub effects: Vec<EffIdx>,
    pub implied: Vec<ExprIdx>,
    pub functions: Vec<FunIdx>,
    pub imports: HashMap<String, PackageIdx>,
}

pub struct Parsed {
    pub effects: VecMap<EffIdx, Effect>,
    pub functions: VecMap<FunIdx, Function>,
    pub packages: VecMap<PackageIdx, Package>,

    pub main: PackageIdx,
    pub preamble: PackageIdx,

    // package inside core of the current system
    pub system: PackageIdx,

    pub exprs: VecMap<ExprIdx, Ranged<Expression>>,
    pub types: VecMap<TypeIdx, Ranged<Type>>,
    pub idents: VecMap<Ident, Ranged<String>>,
}

impl Default for Parsed {
    fn default() -> Self {
        let mut packages = VecMap::new();
        let core = packages.push(PackageIdx, Package::default());
        let main = packages.push(PackageIdx, Package::default());
        let system = packages.push(PackageIdx, Package::default());

        let mut exprs = VecMap::new();
        exprs.push_value(Ranged(Expression::Error, 0, 0, FileIdx(0)));

        Self {
            effects: VecMap::new(),
            functions: VecMap::new(),
            packages,
            main,
            preamble: core,
            system,
            exprs,
            types: VecMap::new(),
            idents: VecMap::new(),
        }
    }
}

impl Parsed {
    pub fn for_each(
        &self,
        expr: ExprIdx,
        do_try: bool,
        do_handler: bool,
        f: &mut impl FnMut(ExprIdx),
    ) {
        f(expr);
        match self.exprs[expr].0 {
            Expression::Body(ref b) => {
                for expr in b.main.iter().copied() {
                    self.for_each(expr, do_try, do_handler, f);
                }
                if let Some(expr) = b.last {
                    self.for_each(expr, do_try, do_handler, f);
                }
            }
            Expression::Loop(expr) => {
                self.for_each(expr, do_try, do_handler, f);
            }
            Expression::Call(expr, ref args) => {
                self.for_each(expr, do_try, do_handler, f);
                for expr in args.iter().copied() {
                    self.for_each(expr, do_try, do_handler, f);
                }
            }
            Expression::Array(ref elems) => {
                for expr in elems.iter().copied() {
                    self.for_each(expr, do_try, do_handler, f);
                }
            }
            Expression::Member(expr, _) => {
                self.for_each(expr, do_try, do_handler, f);
            }
            Expression::IfElse(cond, yes, no) => {
                self.for_each(cond, do_try, do_handler, f);
                self.for_each(yes, do_try, do_handler, f);
                if let Some(no) = no {
                    self.for_each(no, do_try, do_handler, f);
                }
            }
            Expression::BinOp(left, _, right) => {
                self.for_each(left, do_try, do_handler, f);
                self.for_each(right, do_try, do_handler, f);
            }
            Expression::Yeet(expr) => {
                if let Some(expr) = expr {
                    self.for_each(expr, do_try, do_handler, f);
                }
            }
            Expression::TryWith(expr, handler) => {
                if do_try {
                    self.for_each(expr, do_try, do_handler, f);
                }
                if let Some(handler) = handler {
                    self.for_each(handler, do_try, do_handler, f);
                }
            }
            Expression::Let(_, _, _, expr) => {
                self.for_each(expr, do_try, do_handler, f);
            }
            Expression::UnOp(expr, _) => {
                self.for_each(expr, do_try, do_handler, f);
            }
            Expression::Handler(ref h) => {
                if do_handler {
                    match *h {
                        Handler::Full { ref functions, .. } => {
                            for fun in functions.iter() {
                                self.for_each(fun.body, do_try, do_handler, f);
                            }
                        }
                        Handler::Lambda(Lambda { body, .. }) => {
                            self.for_each(body, do_try, do_handler, f);
                        }
                    }
                }
            }
            Expression::String(_) => {}
            Expression::Character(_) => {}
            Expression::Int(_) => {}
            Expression::Ident(_) => {}
            Expression::Error => {}
            Expression::Uninit => {}
        }
    }
    pub fn fold<A>(&self, expr: ExprIdx, acc: A, mut f: impl FnMut(A, ExprIdx) -> A) -> A {
        let mut acc = Some(acc);
        self.for_each(expr, true, false, &mut |e| {
            acc = Some(f(acc.take().unwrap(), e))
        });
        acc.unwrap()
    }
    pub fn any(&self, expr: ExprIdx, mut f: impl FnMut(ExprIdx) -> bool) -> bool {
        self.fold(expr, false, |n, e| n || f(e))
    }
    pub fn yeets(&self, expr: ExprIdx) -> bool {
        self.any(expr, |e| matches!(self.exprs[e].0, Expression::Yeet(_)))
    }
}

struct Tokens<'a> {
    iter: Tokenizer<'a>,
    peeked: Option<Option<<Tokenizer<'a> as Iterator>::Item>>,
    last: usize,
    context: &'a mut Parsed,
    allow_lambda_args: bool,
    attributes: Option<Vec<Attribute>>,
}

impl<'a> Tokens<'a> {
    fn pos_start(&mut self) -> usize {
        self.peek().map(|p| p.1).unwrap_or(usize::MAX)
    }
    fn pos_end(&self) -> usize {
        self.last
    }
    fn peek(&mut self) -> Option<&<Tokenizer<'a> as Iterator>::Item> {
        let iter = &mut self.iter;
        self.peeked.get_or_insert_with(|| iter.next()).as_ref()
    }
    fn next(&mut self) -> Option<<Tokenizer<'a> as Iterator>::Item> {
        let tok = match self.peeked.take() {
            Some(v) => v,
            None => self.iter.next(),
        };
        self.last = tok.as_ref().map(|p| p.2).unwrap_or(usize::MAX);
        tok
    }
    fn peek_range(&mut self) -> Range {
        match self.peek() {
            Some(r) => r.empty(),
            None => Ranged((), usize::MAX, usize::MAX, self.iter.file),
        }
    }
    fn ranged<T>(&mut self, f: impl FnOnce(&mut Self) -> Option<T>) -> Option<Ranged<T>> {
        let start = self.pos_start();
        let t = f(self)?;
        Some(Ranged(t, start, self.pos_end(), self.iter.file))
    }
    fn check(&mut self, token: Token) -> Option<Ranged<()>> {
        if self.peek_check(token) {
            Some(self.next().unwrap().empty())
        } else {
            None
        }
    }
    fn peek_check(&mut self, token: Token) -> bool {
        matches!(self.peek(), Some(t) if t.0 == token)
    }
    fn expect(&mut self, token: Token) -> Option<Ranged<()>> {
        let err = match self.next() {
            Some(t) if t.0 == token => return Some(t.empty()),
            Some(ref t @ Ranged(Token::Open(group), _, _, _)) => {
                // skip entire unexpected group
                self.skip_close(t.with(group));
                t.with(Error::Unexpected(token.into()))
            }
            Some(t) => t.with(Error::Unexpected(token.into())),
            None => Ranged(
                Error::Unexpected(token.into()),
                usize::MAX,
                usize::MAX,
                self.iter.file,
            ),
        };
        self.iter.errors.push(err);
        None
    }
    fn skip_close(&mut self, group: Ranged<Group>) -> Ranged<()> {
        loop {
            match self.peek() {
                // open new group, needs to be skipped first
                Some(&Ranged(Token::Open(g), start, end, _)) => {
                    self.next();
                    self.skip_close(Ranged(g, start, end, self.iter.file));
                }

                // error on close different group
                Some(&Ranged(Token::Close(g), start, _, _)) if g != group.0 => {
                    self.iter.errors.push(group.map(Error::UnclosedGroup));
                    break Ranged((), group.1, start, self.iter.file);
                }

                // we found it
                Some(&Ranged(Token::Close(_), _, end, _)) => {
                    self.next();
                    break Ranged((), group.1, end, self.iter.file);
                }

                // skip characters
                Some(_) => {
                    self.next();
                }

                // error on unclosed group
                None => {
                    self.iter.errors.push(group.map(Error::UnclosedGroup));
                    break Ranged((), group.1, usize::MAX, self.iter.file);
                }
            }
        }
    }
    fn push_expr(&mut self, expr: Ranged<Expression>) -> ExprIdx {
        self.context.exprs.push(ExprIdx, expr)
    }
    fn push_generic_ident(&mut self, ident: Ranged<String>) -> (bool, Ident) {
        let generic = ident.0.starts_with('$');
        (generic, self.context.idents.push(Ident, ident))
    }
    fn push_ident(&mut self, ident: Ranged<String>) -> Ident {
        if ident.0.starts_with('$') {
            // TODO: error
            panic!("unexpected generic");
        }
        self.context.idents.push(Ident, ident)
    }
    fn push_type(&mut self, typ: Ranged<Type>) -> TypeIdx {
        self.context.types.push(TypeIdx, typ)
    }
    fn ident(&mut self) -> Option<Ranged<String>> {
        let err = match self.next() {
            Some(Ranged(Token::Ident(s), start, end, _)) => {
                return Some(Ranged(s, start, end, self.iter.file))
            }
            Some(t) => t.with(Error::Unexpected(Expected::Identifier)),
            None => Ranged(
                Error::Unexpected(Expected::Identifier),
                usize::MAX,
                usize::MAX,
                self.iter.file,
            ),
        };
        self.iter.errors.push(err);
        None
    }
    fn string(&mut self) -> Option<Ranged<String>> {
        let err = match self.next() {
            Some(Ranged(Token::String(s), start, end, _)) => {
                return Some(Ranged(s, start, end, self.iter.file))
            }
            Some(t) => t.with(Error::Unexpected(Expected::String)),
            None => Ranged(
                Error::Unexpected(Expected::String),
                usize::MAX,
                usize::MAX,
                self.iter.file,
            ),
        };
        self.iter.errors.push(err);
        None
    }
    fn lambdas<T>(&mut self, allow: bool, f: impl FnOnce(&mut Self) -> Option<T>) -> Option<T> {
        let old = self.allow_lambda_args;
        self.allow_lambda_args = allow;
        let val = f(self);
        self.allow_lambda_args = old;
        val
    }
    fn group_single<T>(
        &mut self,
        group: Group,
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<Ranged<T>> {
        self.lambdas(true, |tk| {
            let open = tk.expect(Token::Open(group))?;
            match f(tk) {
                Some(t) => match tk.peek() {
                    Some(c) if c.0 == Token::Close(group) => {
                        let tok = tk.next().unwrap();
                        Some(Ranged(t, open.1, tok.2, tk.iter.file))
                    }
                    None => {
                        tk.iter.errors.push(Ranged(
                            Error::UnclosedGroup(group),
                            open.1,
                            open.2,
                            tk.iter.file,
                        ));
                        Some(Ranged(t, open.1, usize::MAX, tk.iter.file))
                    }
                    _ => Some(
                        tk.skip_close(Ranged(group, open.1, open.2, tk.iter.file))
                            .with(t),
                    ),
                },
                None => {
                    tk.skip_close(Ranged(group, open.1, open.2, tk.iter.file));
                    None
                }
            }
        })
    }
    fn group(
        &mut self,
        group: Group,
        comma_separated: bool,
        mut f: impl FnMut(&mut Self) -> Option<()>,
    ) -> Option<Ranged<()>> {
        self.lambdas(true, |tk| {
            let open = tk.expect(Token::Open(group))?;
            Some(loop {
                match tk.peek() {
                    Some(t) if t.0 == Token::Close(group) => {
                        let t = tk.next().unwrap();
                        break Ranged((), open.1, t.2, tk.iter.file);
                    }
                    None => {
                        tk.iter.errors.push(Ranged(
                            Error::UnclosedGroup(group),
                            open.1,
                            open.2,
                            tk.iter.file,
                        ));
                        break Ranged((), open.1, usize::MAX, tk.iter.file);
                    }
                    _ => {
                        // parse inner
                        if f(tk).is_none() {
                            // error parsing, skip to anchor
                            loop {
                                match tk.peek() {
                                    Some(Ranged(Token::Open(g), start, end, _)) => {
                                        let g = *g;
                                        let start = *start;
                                        let end = *end;
                                        tk.next();
                                        tk.skip_close(Ranged(g, start, end, tk.iter.file));
                                    }
                                    Some(Ranged(t, ..)) if t.is_anchor() => break,
                                    None => break,
                                    _ => {
                                        tk.next();
                                    }
                                }
                            }
                        }
                        // parse comma?
                        if comma_separated {
                            match tk.peek() {
                                // we are closing next
                                Some(t) if t.0 == Token::Close(group) => {}

                                // else expect comma
                                _ => match tk.expect(Token::Comma) {
                                    Some(_) => {}
                                    None => {
                                        break tk.skip_close(Ranged(
                                            group,
                                            open.1,
                                            open.2,
                                            tk.iter.file,
                                        ))
                                    }
                                },
                            }
                        }
                    }
                }
            })
        })
    }
}

trait Parse: Sized {
    fn parse(tk: &mut Tokens) -> Option<Self>;

    // parse, and if it could not be parsed, skip to anchor tokens
    fn parse_or_skip(tk: &mut Tokens) -> Option<Ranged<Self>> {
        let start = tk.pos_start();
        match Self::parse(tk) {
            // successful parse
            Some(s) => Some(Ranged(s, start, tk.pos_end(), tk.iter.file)),

            // skip to anchor
            None => loop {
                match tk.peek() {
                    Some(Ranged(Token::Open(g), start, end, _)) => {
                        let g = *g;
                        let start = *start;
                        let end = *end;
                        tk.next();
                        tk.skip_close(Ranged(g, start, end, tk.iter.file));
                    }
                    Some(Ranged(t, ..)) if t.is_anchor() => break None,
                    None => break None,
                    _ => {
                        tk.next();
                    }
                }
            },
        }
    }
}

trait ParseDefault: Parse + Default {
    fn parse_or_default(tk: &mut Tokens) -> Ranged<Self> {
        let start = tk.pos_start();
        Self::parse_or_skip(tk).unwrap_or(Ranged(Self::default(), start, start, tk.iter.file))
    }
}

impl<T> ParseDefault for T where T: Parse + Default {}

pub fn parse_ast<'a>(
    tk: Tokenizer<'a>,
    idx: PackageIdx,
    parsed: &'a mut Parsed,
    file_path: &Path,
    lib_paths: &HashMap<&str, &Path>,
    todo_packages: &mut Vec<(PathBuf, PackageIdx)>,
) {
    let mut tk = Tokens {
        iter: tk,
        peeked: None,
        last: 0,
        context: parsed,
        allow_lambda_args: true,
        attributes: None,
    };

    // parse ast
    loop {
        match tk.peek() {
            // import
            Some(Ranged(Token::Import, ..)) => {
                tk.next();
                if let Some(string) = tk.string() {
                    // parse path
                    let split = string.0.split_once(":");
                    let (lib, path) = match split {
                        Some((lib, path)) => (Some(lib), path),
                        None => (None, string.0.as_str()),
                    };

                    // get dir path
                    let path = match lib {
                        Some(lib) => match lib_paths.get(lib) {
                            Some(root) => root.join(&path),
                            None => {
                                tk.iter
                                    .errors
                                    .push(string.with(Error::UnresolvedLibrary(lib.into())));
                                continue;
                            }
                        },
                        None => file_path.join(path),
                    };
                    // test if dir exists
                    if !path.is_dir() {
                        tk.iter.errors.push(
                            string
                                .with(Error::NoSuchDirectory(path.to_string_lossy().into_owned())),
                        );
                        continue;
                    }

                    let name = path.file_name().unwrap().to_string_lossy().into_owned();
                    let path = std::fs::canonicalize(path).unwrap();

                    // get or create package
                    let existing = todo_packages.iter().find(|(other, _)| other.eq(&path));
                    let pkg = match existing {
                        Some(&(_, pkg)) => pkg,
                        None => {
                            let pkg = tk.context.packages.push(PackageIdx, Package::default());
                            todo_packages.push((path, pkg));
                            pkg
                        }
                    };

                    // add to import list
                    tk.context.packages[idx].imports.insert(name, pkg);
                }
            }

            // effect
            Some(Ranged(Token::Effect, ..)) => {
                if let Some(Ranged(effect, ..)) = Effect::parse_or_skip(&mut tk) {
                    let eff = tk.context.effects.push(EffIdx, effect);
                    tk.context.packages[idx].effects.push(eff);
                }
            }

            // implied
            Some(Ranged(Token::Handle, ..)) => {
                if let Some(handler) = Handler::parse_or_skip(&mut tk) {
                    let expr = tk.push_expr(handler.map(Expression::Handler));
                    tk.context.packages[idx].implied.push(expr);
                }
            }

            // function
            Some(Ranged(Token::Fun, ..)) => {
                if let Some(Ranged(function, ..)) = Function::parse_or_skip(&mut tk) {
                    let fun = tk.context.functions.push(FunIdx, function);
                    tk.context.packages[idx].functions.push(fun);
                }
            }

            // attrs
            Some(Ranged(Token::At, ..)) => {
                tk.attributes = Vec::<Attribute>::parse_or_skip(&mut tk).map(|a| a.0);
            }

            // ignore semicolons
            Some(Ranged(Token::Semicolon, ..)) => {
                tk.next();
            }

            // unexpected
            Some(r) => {
                let err = r.with(Error::Unexpected(Expected::Definition));
                tk.next();
                tk.iter.errors.push(err);
            }

            // eof
            None => break,
        }
    }
}

impl Parse for Type {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        match tk.peek() {
            Some(Ranged(Token::Bang, ..)) => {
                tk.next();
                Some(Type::Never)
            }
            Some(Ranged(Token::Caret, ..)) => {
                tk.next();

                let ty = Type::parse_or_default(tk);
                let ty = tk.push_type(ty);

                Some(Type::Pointer(ty))
            }
            Some(Ranged(Token::Const, ..)) => {
                tk.next();

                let ty = Type::parse_or_default(tk);
                let ty = tk.push_type(ty);

                Some(Type::Const(ty))
            }
            Some(Ranged(Token::Open(Group::Bracket), ..)) => {
                enum ArrType {
                    Const(u64),
                    Slice,
                }

                let num = tk.group_single(Group::Bracket, |tk| match tk.peek() {
                    Some(&Ranged(Token::Close(Group::Bracket), ..)) => Some(ArrType::Slice),
                    Some(&Ranged(Token::Int(i), ..)) => Some(ArrType::Const(i?)),
                    _ => {
                        let err = tk.peek_range().with(Error::Unexpected(Expected::ArrayKind));
                        tk.iter.errors.push(err);
                        None
                    }
                });

                let ty = Type::parse_or_default(tk);
                let ty = tk.push_type(ty);

                match num {
                    Some(Ranged(num, ..)) => match num {
                        ArrType::Const(num) => Some(Type::ConstArray(num, ty)),
                        ArrType::Slice => Some(Type::Slice(ty)),
                    },
                    None => Some(Type::Error),
                }
            }
            Some(Ranged(Token::Handle, ..)) => {
                tk.next();

                let id = tk.ident()?;
                let (generic, id) = tk.push_generic_ident(id);
                let fail = FailType::parse_or_skip(tk)?.0;

                if generic {
                    Some(Type::GenericHandler(id, fail))
                } else {
                    Some(Type::Handler(id, fail))
                }
            }
            Some(Ranged(Token::Ident(_), ..)) => {
                let id = tk.ident()?;
                let (generic, id) = tk.push_generic_ident(id);

                if generic {
                    Some(Type::Generic(id))
                } else {
                    match FailType::parse_or_skip(tk)?.0 {
                        FailType::Never => Some(Type::Path(id)),
                        ty => Some(Type::Handler(id, ty)),
                    }
                }
            }
            _ => {
                let err = tk.peek_range().with(Error::Unexpected(Expected::Type));
                tk.next();
                tk.iter.errors.push(err);
                None
            }
        }
    }
}

impl Parse for FailType {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        if tk.check(Token::Yeets).is_some() {
            if tk.peek().map(|t| t.0.continues_statement()).unwrap_or(true) {
                Some(FailType::None)
            } else {
                let t = Type::parse_or_default(tk);
                let t = tk.push_type(t);
                Some(FailType::Some(t))
            }
        } else {
            Some(FailType::Never)
        }
    }
}

impl Parse for Option<TypeIdx> {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        if tk
            .peek()
            .map(|t| t.0.continues_statement() || t.0 == Token::Loop)
            .unwrap_or(true)
        {
            Some(None)
        } else {
            let t = Type::parse_or_default(tk);
            let t = tk.push_type(t);
            Some(Some(t))
        }
    }
}

impl Parse for FunSign {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut decl = FunSign {
            inputs: VecMap::new(),
            effects: Vec::new(),
            output: None,
        };

        tk.group(Group::Paren, true, |tk| {
            let mutable = tk.check(Token::Mut).is_some();
            let id = tk.ident()?;
            let (const_generic, name) = tk.push_generic_ident(id);
            let ty = Type::parse_or_default(tk);
            let ty = tk.push_type(ty);
            decl.inputs.push_value(Param {
                mutable,
                const_generic,
                name,
                ty,
            });
            Some(())
        })?;

        decl.output = Option::<TypeIdx>::parse_or_default(tk).0;

        if tk.check(Token::Slash).is_some() {
            while matches!(tk.peek(), Some(Ranged(Token::Ident(_), ..))) {
                let Some(effect) = tk.ident() else { continue };
                let effect = tk.push_ident(effect);
                let (package, effect) = if tk.check(Token::Dot).is_some() {
                    let package = effect;
                    let Some(effect) = tk.ident() else { continue };
                    let effect = tk.push_ident(effect);
                    (Some(package), effect)
                } else {
                    (None, effect)
                };
                decl.effects.push(EffectIdent { package, effect });
            }
        }

        Some(decl)
    }
}

impl Parse for FunDecl {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        tk.expect(Token::Fun)?;
        let name = tk.ident()?;

        let decl = FunDecl {
            name: tk.push_ident(name),
            sign: FunSign::parse(tk)?,
            attributes: tk.attributes.take().unwrap_or(Vec::new()),
        };

        Some(decl)
    }
}

impl Parse for Effect {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        tk.expect(Token::Effect)?;
        let name = tk.ident()?;

        let mut effect = Effect {
            name: tk.push_ident(name),
            functions: VecMap::new(),
            attributes: tk.attributes.take().unwrap_or(Vec::new()),
        };

        tk.group(Group::Brace, false, |tk| {
            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            // parse function
            tk.attributes = Vec::<Attribute>::parse_or_skip(tk).map(|a| a.0);
            let f = FunDecl::parse_or_skip(tk)?.0;
            effect.functions.push_value(f);

            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            Some(())
        })?;

        Some(effect)
    }
}

impl Parse for Vec<Attribute> {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut attrs = Vec::new();
        while tk.check(Token::At).is_some() {
            let name = tk.ident()?;
            let name = tk.push_ident(name);
            let mut settings = Vec::new();

            if tk.peek_check(Token::Open(Group::Paren)) {
                tk.group(Group::Paren, true, |tk| {
                    let name = tk.ident()?;
                    let name = tk.push_ident(name);

                    tk.expect(Token::Equals)?;

                    let val = if matches!(tk.peek(), Some(Ranged(Token::String(_), ..))) {
                        AttributeValue::String(tk.string()?)
                    } else {
                        let ty = Type::parse_or_default(tk);
                        AttributeValue::Type(tk.push_type(ty))
                    };

                    settings.push((name, val));
                    Some(())
                })?;
            }

            attrs.push(Attribute { name, settings })
        }
        Some(attrs)
    }
}

impl Parse for Function {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let decl = FunDecl::parse_or_skip(tk)?.0;

        let body = Body::parse_or_default(tk);

        Some(Function {
            decl,
            body: tk.push_expr(body),
        })
    }
}

impl Parse for Handler {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        if tk.check(Token::Fun).is_some() {
            Some(Handler::Lambda(Lambda::parse_or_skip(tk)?.0))
        } else {
            tk.expect(Token::Handle)?;
            let effect = tk.ident()?;
            let effect = tk.push_ident(effect);
            let (package, effect) = if tk.check(Token::Dot).is_some() {
                let package = effect;
                let effect = tk.ident()?;
                let effect = tk.push_ident(effect);
                (Some(package), effect)
            } else {
                (None, effect)
            };

            let mut funcs = Vec::new();

            let fail_type = FailType::parse_or_skip(tk)?.0;

            tk.group(Group::Brace, false, |tk| {
                // skip semicolons
                while tk.check(Token::Semicolon).is_some() {}

                // parse function
                let func = Function::parse_or_skip(tk)?.0;
                funcs.push(func);

                // skip semicolons
                while tk.check(Token::Semicolon).is_some() {}

                Some(())
            })?;

            Some(Handler::Full {
                effect: EffectIdent { package, effect },
                functions: funcs,
                fail_type,
            })
        }
    }
}

impl Parse for Lambda {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let start = tk.pos_start();

        let mut inputs = VecMap::new();
        let mut main = Vec::new();
        let mut last = None;

        tk.group_single(Group::Brace, |tk| {
            if matches!(tk.peek(), Some(Ranged(Token::Ident(_), ..))) {
                let id = tk.ident()?;
                let name = tk.push_ident(id);
                if matches!(tk.peek(), Some(Ranged(Token::Comma | Token::Arrow, ..))) {
                    // arguments
                    inputs.push_value(name);

                    if tk.check(Token::Comma).is_some() {
                        loop {
                            let id = tk.ident()?;
                            let name = tk.push_ident(id);

                            inputs.push_value(name);

                            if tk.check(Token::Comma).is_none() {
                                break;
                            }
                        }
                    }

                    tk.expect(Token::Arrow)?;
                } else {
                    // ident expr
                    let expr = expression_post(
                        tk,
                        Ranged(Expression::Ident(name), start, tk.pos_end(), tk.iter.file),
                        start,
                    )?;
                    let n = tk.push_expr(Ranged(expr, start, tk.pos_end(), tk.iter.file));

                    if tk.check(Token::Semicolon).is_none() {
                        last = Some(n);
                        if !tk.peek_check(Token::Close(Group::Brace)) {
                            // TODO: error
                            return None;
                        } else {
                            return Some(());
                        }
                    } else {
                        // skip semicolons
                        while tk.check(Token::Semicolon).is_some() {}
                        main.push(n);
                    }
                }
            }

            // rest of exprs
            loop {
                // skip semicolons
                while tk.check(Token::Semicolon).is_some() {}

                // parse expression
                let expr = Expression::parse_or_default(tk);
                let n = tk.push_expr(expr);

                if tk.check(Token::Semicolon).is_none() {
                    last = Some(n);
                    if !tk.peek_check(Token::Close(Group::Brace)) {
                        // TODO: error
                        return None;
                    } else {
                        return Some(());
                    }
                } else {
                    // skip semicolons
                    while tk.check(Token::Semicolon).is_some() {}
                    main.push(n);
                }
            }
        })?;

        let body = tk.push_expr(Ranged(
            Expression::Body(Body { main, last }),
            start,
            tk.pos_end(),
            tk.iter.file,
        ));

        Some(Lambda { inputs, body })
    }
}

impl Parse for Expression {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let start = tk.pos_start();
        let expr = tk.ranged(|tk| match tk.peek() {
            // uninit
            Some(Ranged(Token::TripleDash, ..)) => {
                tk.next();
                Some(Expression::Uninit)
            }

            Some(Ranged(Token::Loop, ..)) => {
                tk.next();
                let body = Body::parse_or_default(tk);
                let body = tk.push_expr(body);
                Some(Expression::Loop(body))
            }

            // try-with expression
            Some(Ranged(Token::Try, ..)) => {
                tk.next();

                // allow for try-loop
                let loop_start = tk.pos_start();
                let inner = if tk.check(Token::Loop).is_some() {
                    let body = Body::parse_or_default(tk);
                    let body = tk.push_expr(body);
                    Ranged(
                        Expression::Loop(body),
                        loop_start,
                        tk.pos_end(),
                        tk.iter.file,
                    )
                } else {
                    Body::parse_or_default(tk)
                };

                if tk.check(Token::With).is_some() {
                    let handler = Expression::parse_or_skip(tk)?;
                    let handler = tk.push_expr(handler);
                    let mut handlers = vec![handler];

                    while tk.check(Token::Comma).is_some() {
                        let handler = Expression::parse_or_skip(tk)?;
                        let handler = tk.push_expr(handler);
                        handlers.push(handler)
                    }

                    let mut expr = inner;
                    for handler in handlers.into_iter().rev() {
                        expr = Ranged(
                            Expression::TryWith(tk.push_expr(expr), Some(handler)),
                            start,
                            tk.pos_end(),
                            tk.iter.file,
                        );
                    }
                    Some(expr.0)
                } else {
                    Some(Expression::TryWith(tk.push_expr(inner), None))
                }
            }

            // with block
            Some(Ranged(Token::With, ..)) => {
                tk.next();

                let mut handlers = Vec::new();
                tk.lambdas(false, |tk| {
                    let handler = Expression::parse_or_skip(tk)?;
                    let handler = tk.push_expr(handler);
                    handlers.push(handler);

                    while tk.check(Token::Comma).is_some() {
                        let handler = Expression::parse_or_skip(tk)?;
                        let handler = tk.push_expr(handler);
                        handlers.push(handler);
                    }
                    Some(())
                })?;

                // allow for with-loop
                let loop_start = tk.pos_start();
                let inner = if tk.check(Token::Loop).is_some() {
                    let body = Body::parse_or_default(tk);
                    let body = tk.push_expr(body);
                    Ranged(
                        Expression::Loop(body),
                        loop_start,
                        tk.pos_end(),
                        tk.iter.file,
                    )
                } else {
                    Body::parse_or_default(tk)
                };

                let mut expr = inner;
                for handler in handlers.into_iter().rev() {
                    expr = Ranged(
                        Expression::TryWith(tk.push_expr(expr), Some(handler)),
                        start,
                        tk.pos_end(),
                        tk.iter.file,
                    );
                }
                Some(expr.0)
            }

            // if-(else)
            Some(Ranged(Token::If, ..)) => {
                tk.next();

                let condition = tk.lambdas(false, |tk| {
                    let condition = Expression::parse_or_default(tk);
                    let condition = tk.push_expr(condition);
                    Some(condition)
                })?;

                let yes = Body::parse_or_default(tk);
                let yes = tk.push_expr(yes);

                let no = if tk.check(Token::Else).is_some() {
                    // allow for else-if
                    let no = if tk.peek_check(Token::If) {
                        Expression::parse_or_default(tk)
                    } else {
                        Body::parse_or_default(tk)
                    };
                    Some(tk.push_expr(no))
                } else {
                    None
                };

                Some(Expression::IfElse(condition, yes, no))
            }

            // let x type = ...
            Some(Ranged(Token::Let, ..)) => {
                tk.next();

                let name = tk.ident()?;
                let name = tk.push_ident(name);

                let typ = if !tk.peek_check(Token::Equals) {
                    let ty = Type::parse_or_default(tk);
                    Some(tk.push_type(ty))
                } else {
                    None
                };

                tk.expect(Token::Equals)?;

                let value = Expression::parse_or_default(tk);
                let value = tk.push_expr(value);

                Some(Expression::Let(false, name, typ, value))
            }

            // mut x type = ...
            Some(Ranged(Token::Mut, ..)) => {
                tk.next();

                let name = tk.ident()?;
                let name = tk.push_ident(name);

                let typ = if !tk.peek_check(Token::Equals) {
                    let ty = Type::parse_or_default(tk);
                    Some(tk.push_type(ty))
                } else {
                    None
                };

                tk.expect(Token::Equals)?;

                let value = Expression::parse_or_default(tk);
                let value = tk.push_expr(value);

                Some(Expression::Let(true, name, typ, value))
            }

            // break
            Some(Ranged(Token::Yeet, ..)) => {
                tk.next();

                if matches!(
                    tk.peek(),
                    Some(Ranged(t, ..), ..) if t.continues_statement()
                ) {
                    Some(Expression::Yeet(None))
                } else {
                    let value = Expression::parse_or_default(tk);
                    let value = tk.push_expr(value);
                    Some(Expression::Yeet(Some(value)))
                }
            }

            // reference
            Some(Ranged(Token::Ampersand, ..)) => {
                tk.next();

                let right = Expression::parse_or_default(tk);
                let right = tk.push_expr(right);

                Some(Expression::UnOp(right, UnOp::Reference))
            }

            // cast
            Some(Ranged(Token::Cast, ..)) => {
                tk.next();

                let right = Expression::parse_or_default(tk);
                let right = tk.push_expr(right);

                Some(Expression::UnOp(right, UnOp::Cast))
            }

            // ident
            Some(Ranged(Token::Ident(_), ..)) => {
                let id = tk.ident()?;
                let (_, ident) = tk.push_generic_ident(id);
                Some(Expression::Ident(ident))
            }

            // handler
            Some(Ranged(Token::Handle | Token::Fun, ..)) => {
                let handler = Handler::parse_or_skip(tk)?;
                Some(Expression::Handler(handler.0))
            }

            // string
            Some(Ranged(Token::String(s), ..)) => {
                let s = s.clone();
                tk.next();
                Some(Expression::String(s))
            }

            // character
            Some(Ranged(Token::Character(s), ..)) => {
                let s = s.clone();
                tk.next();
                Some(Expression::Character(s))
            }

            // int
            Some(&Ranged(Token::Int(num), ..)) => {
                tk.next();
                Some(Expression::Int(num?))
            }

            // block
            Some(Ranged(Token::Open(Group::Brace), ..)) => Some(Body::parse_or_default(tk).0),

            // array
            Some(Ranged(Token::Open(Group::Bracket), ..)) => {
                let mut elems = Vec::new();
                tk.group(Group::Bracket, true, |tk| {
                    let expr = Expression::parse_or_default(tk);
                    elems.push(tk.push_expr(expr));
                    Some(())
                })?;
                Some(Expression::Array(elems))
            }

            // paren
            Some(Ranged(Token::Open(Group::Paren), ..)) => {
                let expr = tk
                    .group_single(Group::Paren, |tk| Some(Expression::parse_or_default(tk).0))?
                    .0;
                Some(expr)
            }

            _ => {
                let err = match tk.next() {
                    Some(t) => t.with(Error::Unexpected(Expected::Expression)),
                    None => Ranged(
                        Error::Unexpected(Expected::Expression),
                        tk.pos_end(),
                        tk.pos_end(),
                        tk.iter.file,
                    ),
                };
                tk.iter.errors.push(err);
                None
            }
        })?;

        // post-fixes
        expression_post(tk, expr, start)
    }
}

fn expression_post(
    tk: &mut Tokens<'_>,
    mut expr: Ranged<Expression>,
    start: usize,
) -> Option<Expression> {
    loop {
        match tk.peek() {
            // member
            Some(Ranged(Token::Dot, ..)) => {
                tk.next();
                let member = tk.ident()?;
                expr = Ranged(
                    Expression::Member(tk.push_expr(expr), tk.push_ident(member)),
                    start,
                    tk.pos_end(),
                    tk.iter.file,
                );
            }

            // post try/with
            Some(Ranged(Token::With, ..)) => {
                tk.next();
                let handler = Expression::parse_or_skip(tk)?;
                let handler = tk.push_expr(handler);
                let mut handlers = vec![handler];

                while tk.check(Token::Comma).is_some() {
                    let handler = Expression::parse_or_skip(tk)?;
                    let handler = tk.push_expr(handler);
                    handlers.push(handler)
                }

                for handler in handlers.into_iter().rev() {
                    expr = Ranged(
                        Expression::TryWith(tk.push_expr(expr), Some(handler)),
                        start,
                        tk.pos_end(),
                        tk.iter.file,
                    );
                }
            }

            // call
            Some(Ranged(Token::Open(Group::Paren), ..)) => {
                let mut args = Vec::new();

                // regular arguments
                tk.group(Group::Paren, true, |tk| {
                    let expr = Expression::parse_or_default(tk);
                    args.push(tk.push_expr(expr));
                    Some(())
                })?;

                // lambda arguments
                if tk.allow_lambda_args {
                    while tk.peek_check(Token::Open(Group::Brace)) {
                        let lambda = Lambda::parse_or_default(tk);
                        let handler = lambda.map(Handler::Lambda);
                        let expr = handler.map(Expression::Handler);
                        args.push(tk.push_expr(expr));
                    }
                }

                expr = Ranged(
                    Expression::Call(tk.push_expr(expr), args),
                    start,
                    tk.pos_end(),
                    tk.iter.file,
                );
            }

            // index
            Some(Ranged(Token::Open(Group::Bracket), ..)) => {
                let index = tk
                    .group_single(Group::Bracket, |tk| {
                        let expr = Expression::parse_or_default(tk);
                        Some(tk.push_expr(expr))
                    })?
                    .0;

                expr = Ranged(
                    Expression::BinOp(tk.push_expr(expr), BinOp::Index, index),
                    start,
                    tk.pos_end(),
                    tk.iter.file,
                )
            }

            // post-increment
            Some(Ranged(Token::DoublePlus, ..)) => {
                tk.next();
                expr = Ranged(
                    Expression::UnOp(tk.push_expr(expr), UnOp::PostIncrement),
                    start,
                    tk.pos_end(),
                    tk.iter.file,
                )
            }

            // binary ops
            // TODO: operator precedence
            Some(Ranged(t, ..)) => match BinOp::from_token(t) {
                Some(op) => {
                    tk.next();

                    let right = Expression::parse_or_default(tk);
                    let right = tk.push_expr(right);

                    expr = Ranged(
                        Expression::BinOp(tk.push_expr(expr), op, right),
                        start,
                        tk.pos_end(),
                        tk.iter.file,
                    )
                }
                None => break Some(expr.0),
            },

            _ => break Some(expr.0),
        }
    }
}

impl Parse for Body {
    fn parse(tk: &mut Tokens) -> Option<Self> {
        let mut main = Vec::new();
        let mut last = None;

        tk.group(Group::Brace, false, |tk| {
            // skip semicolons
            while tk.check(Token::Semicolon).is_some() {}

            // parse expression
            let expr = Expression::parse_or_default(tk);
            let n = tk.push_expr(expr);

            if tk.check(Token::Semicolon).is_none() {
                last = Some(n);
                if !tk.peek_check(Token::Close(Group::Brace)) {
                    // TODO: error
                    None
                } else {
                    Some(())
                }
            } else {
                // skip semicolons
                while tk.check(Token::Semicolon).is_some() {}
                main.push(n);
                Some(())
            }
        })?;

        Some(Body { main, last })
    }
}
