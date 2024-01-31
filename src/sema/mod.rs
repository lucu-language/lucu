use std::{fmt, rc::Rc};

use either::Either;

use crate::{
    ast::{EffFunIdx, EffIdx, FunIdx, ParamIdx},
    error::{Range, Ranged},
    vecmap::{vecmap_index, VecMap, VecSet},
};

vecmap_index!(GenericIdx);
vecmap_index!(HandlerIdx);
vecmap_index!(LazyIdx);

vecmap_index!(BlockIdx);
vecmap_index!(InstrIdx);

pub struct FmtType<'a>(pub &'a SemIR, pub TypeIdx);

impl fmt::Display for FmtType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'")?;
        self.1.display(self.0, &GenericParams::default(), f)?;
        write!(f, "'")?;
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct TypeIdx(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FunIdent {
    Top(FunIdx),
    Effect(EffIdx, EffFunIdx),
}

impl FunIdent {
    pub fn sign(self, ir: &SemIR) -> &FunSign {
        match self {
            FunIdent::Top(idx) => &ir.fun_sign[idx],
            FunIdent::Effect(eff, idx) => &ir.effects[eff].funs[idx],
        }
    }
    pub fn generic_indices(self, ir: &SemIR) -> impl Iterator<Item = GenericIdx> + '_ {
        (match self {
            FunIdent::Top(_) => Either::Left(std::iter::empty()),
            FunIdent::Effect(eff, _) => Either::Right(ir.effects[eff].generics.iter()),
        })
        .chain(self.sign(ir).generics.iter())
        .map(|generic| generic.idx)
    }
}

impl From<TypeIdx> for usize {
    fn from(value: TypeIdx) -> Self {
        value.0 >> 2
    }
}

impl TypeIdx {
    pub(crate) fn new(idx: usize, is_const: bool) -> Self {
        Self(idx << 2 | (if is_const { 1 } else { 0 }))
    }
    pub fn is_const(self) -> bool {
        self.0 & 1 == 1
    }
    pub fn with_const(self, is_const: bool) -> Self {
        Self::new(usize::from(self), is_const)
    }
}

mod codegen;
pub use codegen::analyze;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Value {
    Reg(BlockIdx, Option<InstrIdx>),
    Deref(Box<Value>),

    // slice, const array
    // TODO: split these into ConstantSlice, ConstantArray
    ConstantAggregate(TypeIdx, Rc<[Value]>),
    ConstantHandler(TypeIdx, Rc<[Value]>),

    // TODO: use (bool, IntSize) instead of TypeIdx
    ConstantInt(TypeIdx, bool, u64),
    // TODO: use bool instead of TypeIdx
    ConstantString(TypeIdx, Rc<[u8]>),
    ConstantBool(bool),
    ConstantNone,
    ConstantUninit(TypeIdx),
    ConstantZero(TypeIdx),
    ConstantError,
    ConstantGeneric(GenericIdx),

    Param(ParamIdx),
    EffectParam(usize),
    Capture(usize),
}

impl Value {
    pub fn is_constant(&self) -> bool {
        match self {
            Value::Reg(_, _) => false,
            Value::Deref(_) => false,
            Value::ConstantAggregate(_, val) => val.iter().all(Self::is_constant),
            Value::ConstantHandler(_, _) => false,
            Value::ConstantInt(_, _, _) => true,
            Value::ConstantString(_, _) => true,
            Value::ConstantBool(_) => true,
            Value::ConstantNone => true,
            Value::ConstantUninit(_) => true,
            Value::ConstantZero(_) => true,
            Value::ConstantError => true,
            Value::ConstantGeneric(_) => true,
            Value::Param(_) => false,
            Value::EffectParam(_) => false,
            Value::Capture(_) => false,
        }
    }
}

#[derive(Debug, Default)]
pub struct FunImpl {
    pub blocks: VecMap<BlockIdx, Block>,
}

#[derive(Debug, Default, Clone)]
pub struct Block {
    pub instructions: VecMap<InstrIdx, Instruction>,
    pub value: Option<(TypeIdx, Vec<(Value, BlockIdx)>)>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum Instruction {
    Cast(Value, TypeIdx),

    Jump(BlockIdx),
    Branch(Value, BlockIdx, BlockIdx),

    Equals(Value, Value),
    Greater(Value, Value),
    Less(Value, Value),

    Div(TypeIdx, Value, Value),
    Mul(TypeIdx, Value, Value),
    Add(TypeIdx, Value, Value),
    Sub(TypeIdx, Value, Value),

    Call(
        FunIdent,
        // generics
        GenericParams,
        // params
        Vec<Value>,
        // effect params
        // TODO: Vec<Value>, Vec<(TypeIdx, BlockIdx)>,
        Vec<(Value, Option<BlockIdx>)>,
    ),

    Yeet(Value, Option<BlockIdx>),
    Return(Value),
    Unreachable,

    Reference(Value, TypeIdx),
    Load(TypeIdx, Value),
    Store(Value, Value),

    Member(Value, u32, TypeIdx),
    AdjacentPtr(Value, Value, TypeIdx),

    LinkHandler(GenericVal<EffectIdent>, GenericVal<String>),
    AsmHandler(
        GenericVal<EffectIdent>,
        GenericVal<String>,
        GenericVal<String>,
        GenericVal<bool>,
    ),
    CompileError(GenericVal<String>),
    Syscall(Value, Value),
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name_def: Range,
    pub name: String,
    pub type_def: Range,
    pub ty: TypeIdx,
    pub mutable: bool,
    pub const_generic: Option<GenericIdx>,
}

#[derive(Debug, Clone)]
pub struct ReturnType {
    pub type_def: Option<Range>,
    pub ty: TypeIdx,
}

impl Default for ReturnType {
    fn default() -> Self {
        Self {
            type_def: None,
            ty: TypeIdx(1),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct FunSign {
    pub def: Option<Range>,
    pub name: String,
    pub generics: Generics,

    pub params: VecMap<ParamIdx, Param>,
    pub effect_stack: Vec<Ranged<(TypeIdx, GenericVal<EffectIdent>)>>,
    pub return_type: ReturnType,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Generic {
    pub idx: GenericIdx,
    pub typeof_ty: TypeIdx,
}

#[derive(Debug, Default)]
pub struct Effect {
    pub name: String,
    pub generics: Generics, // indices correspond 1-1 with ast generics

    pub funs: VecMap<EffFunIdx, FunSign>,
    pub implied: Vec<HandlerIdx>,

    pub capabilities: Vec<Capability>,
    pub foreign: Option<Foreign>,
}

#[derive(Debug, Clone)]
pub struct Capability {
    pub fun: FunIdent,
    pub generic_params: GenericParams,
    pub os: Option<String>,
    pub arch: Option<String>,
}

#[derive(Debug)]
pub struct Foreign {
    pub prefix: String,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct HandlerIdent {
    pub handler: HandlerIdx,
    pub generic_params: GenericParams,
    pub fail_type: TypeIdx,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct HandlerType {
    pub effect: GenericVal<EffectIdent>,
    pub fail_type: TypeIdx,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EffectIdent {
    pub effect: EffIdx,
    pub generic_params: GenericParams,
}

pub type Generics = Vec<Generic>;
pub type GenericParams = Vec<(GenericIdx, TypeIdx)>;

#[derive(Debug)]
pub struct Handler {
    pub debug_name: String,
    pub generics: Generics,

    pub effect: EffIdx,
    pub generic_params: GenericParams,
    pub fail: TypeIdx,

    pub captures: Vec<TypeIdx>,

    pub funs: VecMap<EffFunIdx, (FunSign, FunImpl)>,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum GenericVal<T> {
    Literal(T),
    Generic(GenericIdx),
}

impl<T> GenericVal<T> {
    pub fn literal(&self) -> Option<&T> {
        match self {
            GenericVal::Literal(t) => Some(t),
            GenericVal::Generic(_) => None,
        }
    }
    pub fn map<U>(&self, f: impl FnOnce(&T) -> U) -> GenericVal<U> {
        match *self {
            GenericVal::Literal(ref t) => GenericVal::Literal(f(t)),
            GenericVal::Generic(idx) => GenericVal::Generic(idx),
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum IntSize {
    Reg,
    Size,
    Ptr,
    Bits(u32),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum Type {
    Effect(EffectIdent),
    Handler(Lazy),

    EffectType,
    DataType,
    HandlerType(HandlerType),

    Generic(Generic),

    Pointer(TypeIdx),
    ConstArray(GenericVal<u64>, TypeIdx),
    Slice(TypeIdx),

    Integer(bool, IntSize),

    Str,
    Char,
    Bool,
    None,
    Never,
    Error,

    CompileTime(Value),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct Lazy {
    pub idx: LazyIdx,
    pub typeof_handler: TypeIdx,
}

#[derive(Debug, Clone)]
pub enum LazyValue {
    None,
    Some(GenericVal<HandlerIdent>),
    Refer(LazyIdx, Option<GenericParams>),
    EffectFunOutput(LazyIdx, EffFunIdx, GenericParams),
}

#[derive(Debug)]
pub struct SemIR {
    pub effects: VecMap<EffIdx, Effect>,
    pub fun_sign: VecMap<FunIdx, FunSign>,
    pub fun_impl: VecMap<FunIdx, FunImpl>,

    pub entry: FunIdx,
    pub foreign_handler: HandlerIdx,

    pub types: VecSet<TypeIdx, Type>,
    pub handlers: VecMap<HandlerIdx, Handler>,
    pub lazy_handlers: VecMap<LazyIdx, LazyValue>,

    pub generic_names: VecMap<GenericIdx, String>,
}

pub fn get_param(generic_params: &GenericParams, idx: GenericIdx) -> Option<TypeIdx> {
    get_value(generic_params, &idx).copied()
}

pub fn get_value<'a, K: PartialEq, V>(vec: &'a [(K, V)], key: &K) -> Option<&'a V> {
    vec.iter().find(|(k, _)| k.eq(key)).map(|(_, v)| v)
}

impl IntSize {
    fn display(&self, signed: bool, f: &mut impl fmt::Write) -> fmt::Result {
        match *self {
            IntSize::Reg => match signed {
                true => write!(f, "int"),
                false => write!(f, "uint"),
            },
            IntSize::Size => match signed {
                true => write!(f, "isize"),
                false => write!(f, "usize"),
            },
            IntSize::Ptr => match signed {
                true => write!(f, "iptr"),
                false => write!(f, "uptr"),
            },
            IntSize::Bits(bits) => match signed {
                true => write!(f, "i{}", bits),
                false => write!(f, "u{}", bits),
            },
        }
    }
}

impl LazyIdx {
    fn display(
        &self,
        typeof_handler: TypeIdx,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        write!(f, "impl ")?;
        typeof_handler.display(ir, generic_params, f)?;
        Ok(())
    }
}

impl TypeIdx {
    fn display(
        &self,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        if self.is_const() {
            write!(f, "const ")?;
        }
        match ir.types[*self] {
            Type::Handler(ref lazy) => lazy.idx.display(lazy.typeof_handler, ir, generic_params, f),
            Type::DataType => write!(f, "type"),
            Type::EffectType => write!(f, "effect"),
            Type::HandlerType(ref eff) => {
                match eff.effect {
                    GenericVal::Literal(ref eff) => {
                        write!(f, "{}", ir.effects[eff.effect].name)?;
                        // TODO: print params
                    }
                    GenericVal::Generic(idx) => write!(f, "{}", ir.generic_names[idx])?,
                }
                match ir.types[eff.fail_type] {
                    Type::Never => {}
                    _ => {
                        write!(f, " -> ")?;
                        eff.fail_type.display(ir, generic_params, f)?;
                    }
                }
                Ok(())
            }
            Type::Generic(generic) => match get_param(generic_params, generic.idx) {
                Some(ty) => ty.display(ir, generic_params, f),
                None => {
                    write!(f, "{}", ir.generic_names[generic.idx])
                }
            },
            Type::Pointer(inner) => {
                write!(f, "^")?;
                inner.display(ir, generic_params, f)
            }
            Type::ConstArray(size, inner) => {
                write!(f, "[")?;
                match size {
                    GenericVal::Literal(size) => write!(f, "{}", size)?,
                    GenericVal::Generic(idx) => write!(f, "{}", ir.generic_names[idx])?,
                }
                write!(f, "]")?;
                inner.display(ir, generic_params, f)
            }
            Type::Slice(inner) => {
                write!(f, "[]")?;
                inner.display(ir, generic_params, f)
            }
            Type::Integer(signed, size) => size.display(signed, f),
            Type::Str => write!(f, "str"),
            Type::Char => write!(f, "char"),
            Type::Bool => write!(f, "bool"),
            Type::None => write!(f, "unit"),
            Type::Never => write!(f, "never"),
            Type::Error => write!(f, "ERROR"),
            Type::Effect(ref eff) => {
                write!(f, "{}", ir.effects[eff.effect].name)?;
                // TODO: print params
                Ok(())
            }
            Type::CompileTime(ref val) => {
                val.display(ir, &ir.fun_impl[FunIdx(0)], f)?;
                Ok(())
            }
        }
    }
}

fn display_generics(
    generics: &Generics,
    ir: &SemIR,
    generic_params: &GenericParams,
    f: &mut impl fmt::Write,
) -> fmt::Result {
    let mut iter = generics.iter();
    if let Some(generic) = iter.next() {
        let idx = generic.idx;
        let next = generic.typeof_ty;

        write!(f, "<")?;
        write!(f, "{}", ir.generic_names[idx])?;
        write!(f, " ")?;
        next.display(ir, generic_params, f)?;

        for generic in iter {
            let idx = generic.idx;
            let next = generic.typeof_ty;

            write!(f, ", {}", ir.generic_names[idx])?;
            write!(f, " ")?;
            next.display(ir, generic_params, f)?;
        }
        write!(f, ">")?;
    }
    Ok(())
}

impl FunSign {
    fn display(&self, padding: &str, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let no_params = &GenericParams::default();

        write!(f, "{}fun {}", padding, self.name)?;
        display_generics(&self.generics, ir, no_params, f)?;
        write!(f, "(")?;
        if !self.params.is_empty() {
            let mut iter = self.params.values().map(|param| param.ty);

            let first = iter.next().unwrap();
            first.display(ir, no_params, f)?;
            for next in iter {
                write!(f, ", ")?;
                next.display(ir, no_params, f)?;
            }
        }
        write!(f, ")")?;
        if !matches!(ir.types[self.return_type.ty], Type::None) {
            write!(f, " ")?;
            self.return_type.ty.display(ir, no_params, f)?;
        }
        if !self.effect_stack.is_empty() {
            write!(f, " / ")?;
            let mut iter = self.effect_stack.iter();

            let first = iter.next().unwrap();
            match first.0 .1 {
                GenericVal::Literal(ref eff) => {
                    write!(f, "{}", ir.effects[eff.effect].name)?;
                    // TODO: print params
                }
                GenericVal::Generic(idx) => write!(f, "{}", ir.generic_names[idx])?,
            }
            for next in iter {
                write!(f, " ")?;
                match next.0 .1 {
                    GenericVal::Literal(ref eff) => {
                        write!(f, "{}", ir.effects[eff.effect].name)?;
                        // TODO: print params
                    }
                    GenericVal::Generic(idx) => write!(f, "{}", ir.generic_names[idx])?,
                }
            }
        }
        Ok(())
    }
}

impl Value {
    fn display(&self, ir: &SemIR, proc: &FunImpl, f: &mut impl fmt::Write) -> fmt::Result {
        match *self {
            Value::Reg(block, instr) => match instr {
                Some(instr) => {
                    write!(f, "%{}.{}", block.0, instr.0)?;
                    Ok(())
                }
                None => {
                    let vec = proc.blocks[block].value.as_ref().unwrap();
                    write!(f, "phi")?;
                    for (val, block) in &vec.1 {
                        write!(f, " B{}: ", block.0)?;
                        val.display(ir, proc, f)?;
                        write!(f, ",")?;
                    }
                    Ok(())
                }
            },
            Value::Deref(ref val) => {
                val.display(ir, proc, f)?;
                write!(f, "^")?;
                Ok(())
            }
            Value::ConstantInt(_, signed, n) => write!(f, "{}{}", if signed { "-" } else { "" }, n),
            Value::ConstantString(_, ref str) => {
                write!(f, "\"{}\"", std::str::from_utf8(str).unwrap())
            }
            Value::ConstantBool(b) => write!(f, "{}", b),
            Value::ConstantNone => write!(f, "{{}}"),
            Value::ConstantUninit(_) => write!(f, "---"),
            Value::ConstantZero(_) => write!(f, "0"),
            Value::ConstantError => write!(f, "ERR"),
            Value::ConstantAggregate(_, ref vec) => {
                write!(f, "[")?;
                for val in vec.iter() {
                    write!(f, " ")?;
                    val.display(ir, proc, f)?;
                    write!(f, ",")?;
                }
                write!(f, "]")?;
                Ok(())
            }
            Value::ConstantHandler(_, ref vec) => {
                write!(f, "[")?;
                for val in vec.iter() {
                    write!(f, " ")?;
                    val.display(ir, proc, f)?;
                    write!(f, ",")?;
                }
                write!(f, "]")?;
                Ok(())
            }
            Value::ConstantGeneric(idx) => write!(f, "{}", ir.generic_names[idx]),
            Value::Param(param) => write!(f, "%p{}", param.0),
            Value::EffectParam(param) => write!(f, "%e{}", param),
            Value::Capture(capture) => write!(f, "%c{}", capture),
        }
    }
}

impl<T: fmt::Display> GenericVal<T> {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        match self {
            GenericVal::Literal(s) => write!(f, "{}", s),
            &GenericVal::Generic(idx) => write!(f, "{}", ir.generic_names[idx]),
        }
    }
}

impl FunImpl {
    fn display(
        &self,
        padding: &str,
        ir: &SemIR,
        proc: &FunImpl,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        for (idx, block) in self.blocks.iter(BlockIdx) {
            writeln!(f, "{}B{}", padding, idx.0)?;
            for (_i, instr) in block.instructions.iter(InstrIdx) {
                write!(f, "{}  ", padding)?;
                match instr {
                    Instruction::Cast(v, t) => {
                        write!(f, "cast ")?;
                        v.display(ir, proc, f)?;
                        write!(f, " as ")?;
                        t.display(ir, &Vec::new(), f)?;
                    }
                    Instruction::Jump(block) => {
                        write!(f, "jump B{}", block.0)?;
                    }
                    Instruction::Branch(cond, yes, no) => {
                        write!(f, "branch ")?;
                        cond.display(ir, proc, f)?;
                        write!(f, " B{} else B{}", yes.0, no.0)?;
                    }
                    Instruction::Equals(a, b) => {
                        write!(f, "== ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Greater(a, b) => {
                        write!(f, "> ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Less(a, b) => {
                        write!(f, "< ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Div(_, a, b) => {
                        write!(f, "/ ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Mul(_, a, b) => {
                        write!(f, "* ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Add(_, a, b) => {
                        write!(f, "+ ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Sub(_, a, b) => {
                        write!(f, "- ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Yeet(v, _) => {
                        write!(f, "fail ")?;
                        v.display(ir, proc, f)?;
                    }
                    Instruction::Return(v) => {
                        write!(f, "return ")?;
                        v.display(ir, proc, f)?;
                    }
                    Instruction::Unreachable => {
                        write!(f, "unreachable")?;
                    }
                    Instruction::Reference(v, _) => {
                        write!(f, "alloca ")?;
                        v.display(ir, proc, f)?;
                    }
                    Instruction::Load(_, v) => {
                        write!(f, "load ")?;
                        v.display(ir, proc, f)?;
                    }
                    Instruction::Store(a, b) => {
                        write!(f, "store ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Member(v, n, _) => {
                        write!(f, "member ")?;
                        v.display(ir, proc, f)?;
                        write!(f, " {}", n)?;
                    }
                    Instruction::AdjacentPtr(a, b, _) => {
                        write!(f, "adjptr ")?;
                        a.display(ir, proc, f)?;
                        write!(f, " ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::Call(fun, _, ref args, _) => {
                        write!(f, "call {} (", fun.sign(ir).name)?;
                        for val in args {
                            val.display(ir, proc, f)?;
                            write!(f, ",")?;
                        }
                        write!(f, ")")?;
                    }
                    Instruction::Syscall(ref a, ref b) => {
                        write!(f, "syscall ")?;
                        a.display(ir, proc, f)?;
                        write!(f, ", ")?;
                        b.display(ir, proc, f)?;
                    }
                    Instruction::LinkHandler(_, ref s) => {
                        write!(f, "link ")?;
                        s.display(ir, f)?;
                    }
                    Instruction::AsmHandler(_, ref a, ref b, c) => {
                        write!(f, "asm ")?;
                        a.display(ir, f)?;
                        write!(f, ", ")?;
                        b.display(ir, f)?;
                        write!(f, ", ")?;
                        c.display(ir, f)?;
                    }
                    Instruction::CompileError(ref s) => {
                        write!(f, "err ")?;
                        s.display(ir, f)?;
                    }
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

impl Effect {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let no_params = &GenericParams::default();

        // signature
        write!(f, "effect {}", self.name)?;
        display_generics(&self.generics, ir, no_params, f)?;
        writeln!(f)?;

        // functions
        for fun in self.funs.values() {
            fun.display("  ", ir, f)?;
            writeln!(f)?;
        }

        Ok(())
    }
}

impl Handler {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        let no_params = &GenericParams::default();

        // effect signature
        write!(f, "type {} = handle", self.debug_name)?;
        display_generics(&self.generics, ir, no_params, f)?;
        write!(f, " {}", ir.effects[self.effect].name)?;
        if !self.generic_params.is_empty() {
            write!(f, "<")?;
            let mut iter = self.generic_params.iter().copied();

            let first = iter.next().unwrap();
            first.1.display(ir, no_params, f)?;
            for next in iter {
                write!(f, ", ")?;
                next.1.display(ir, no_params, f)?;
            }
            write!(f, ">")?;
        }
        writeln!(f)?;

        // captures
        for capture in self.captures.iter() {
            capture.display(ir, no_params, f)?;
            writeln!(f)?;
        }

        // funs
        for fun in self.funs.values() {
            // fun signature
            fun.0.display("  ", ir, f)?;
            writeln!(f)?;

            // fun impl
            fun.1.display("  ", ir, &fun.1, f)?;
        }
        Ok(())
    }
}

impl fmt::Display for SemIR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // effects
        for effect in self.effects.values() {
            effect.display(self, f)?;
        }
        writeln!(f)?;

        // handlers
        for handler in self.handlers.values() {
            handler.display(self, f)?;
        }
        writeln!(f)?;

        // functions
        for (fun, imp) in self.fun_sign.values().zip(self.fun_impl.values()) {
            // fun signature
            fun.display("", self, f)?;
            writeln!(f)?;

            // fun impl
            imp.display("", self, imp, f)?;
        }

        Ok(())
    }
}
