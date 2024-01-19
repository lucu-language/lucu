use std::{borrow::Cow, collections::HashMap, matches};

use either::Either;

use crate::{
    error::{FileIdx, Ranged},
    vecmap::{vecmap_index, VecMap},
};

mod parser;
pub use parser::*;

vecmap_index!(ExprIdx);
vecmap_index!(TypeIdx);
vecmap_index!(Ident);
vecmap_index!(PackageIdx);

vecmap_index!(ParamIdx);
vecmap_index!(FunIdx);
vecmap_index!(EffIdx);
vecmap_index!(EffFunIdx);

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

    As(ExprIdx, TypeIdx),
    Do(ExprIdx),

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

#[derive(Debug)]
pub struct Lambda {
    pub inputs: VecMap<ParamIdx, Ident>,
    pub body: ExprIdx,
}

#[derive(Debug)]
pub enum Handler {
    Full {
        effect: PolyIdent,
        fail_type: FailType,
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

    Path(PolyIdent),
    Generic(Ident),

    Handler(PolyIdent, FailType),
    GenericHandler(Ident, FailType),

    ConstExpr(ExprIdx),

    Pointer(TypeIdx),
    Const(TypeIdx),
    ConstArray(ExprIdx, TypeIdx),
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

#[derive(Debug, Clone)]
pub struct PackagedIdent {
    pub package: Option<Ident>,
    pub ident: Ident,
}

#[derive(Debug, Clone)]
pub struct PolyIdent {
    pub ident: PackagedIdent,
    pub params: Option<Vec<TypeIdx>>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub mutable: bool,
    pub const_generic: bool,
    pub name: Ident,
    pub ty: TypeIdx,
}

#[derive(Debug)]
pub struct PolyParam {
    pub name: Ident,
    pub ty: Option<TypeIdx>,
}

#[derive(Debug, Clone)]
pub struct FunSign {
    pub inputs: VecMap<ParamIdx, Param>,
    pub output: Option<TypeIdx>,
    pub effects: Vec<PolyIdent>,
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
    pub generics: Option<VecMap<ParamIdx, PolyParam>>,
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

pub struct Ast {
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

impl Default for Ast {
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

impl Ast {
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
            Expression::As(expr, _) => self.for_each(expr, do_try, do_handler, f),
            Expression::Do(expr) => self.for_each(expr, do_try, do_handler, f),
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
