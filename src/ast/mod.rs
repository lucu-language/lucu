use std::collections::HashMap;

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
