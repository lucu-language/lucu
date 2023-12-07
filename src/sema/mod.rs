use either::Either;
use std::fmt;

use crate::{
    ast::{EffFunIdx, EffIdx, FunIdx, ParamIdx},
    error::Range,
    vecmap::{vecmap_index, VecMap, VecSet},
};

vecmap_index!(TypeIdx);
vecmap_index!(GenericIdx);
vecmap_index!(AssocIdx);
vecmap_index!(HandlerIdx);
vecmap_index!(LazyIdx);

vecmap_index!(BlockIdx);
vecmap_index!(InstrIdx);
vecmap_index!(GlobalIdx);

mod codegen;
pub use codegen::analyze;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum FunctionDef {
    Top(FunIdx),
    Handler(HandlerIdx, EffFunIdx),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Value {
    Reg(BlockIdx, InstrIdx),
    Reference(BlockIdx, InstrIdx),

    ConstantAggregate(Vec<Value>),
    ConstantInt(bool, u64),
    ConstantString(String),
    ConstantBool(bool),
    ConstantType(TypeIdx),
    ConstantNone,
    ConstantUninit,
    ConstantZero,
    ConstantUnknown,

    Param(ParamIdx),
    HandlerParam(usize),
}

#[derive(Debug, Default)]
pub struct FunImpl {
    pub blocks: VecMap<BlockIdx, Block>,
}

#[derive(Debug, Default)]
pub struct Block {
    pub instructions: VecMap<InstrIdx, Instruction>,
}

#[derive(Debug)]
pub enum Instruction {
    Cast(Value, TypeIdx),

    Jump(BlockIdx),
    Branch(Value, BlockIdx, BlockIdx),
    Phi(Vec<(Value, BlockIdx)>),

    Equals(Value, Value),
    Greater(Value, Value),
    Less(Value, Value),
    Div(Value, Value),
    Mul(Value, Value),
    Add(Value, Value),
    Sub(Value, Value),

    PushHandler(Value), // handler -> bound handler
    Call(
        FunctionDef,
        // generics
        Vec<Value>,
        // params
        Vec<Value>,
        // effect params
        Vec<(Value, Option<BlockIdx>)>,
    ),
    PopHandler,

    Yeet(Value),
    Return(Value),
    Unreachable,

    Reference(Value),
    Load(Value),
    Store(Value, Value),

    Member(Value, u32),
    ElementPtr(Value, Value),
    AdjacentPtr(Value, Value),

    Trap,
    Trace(Value),
    Syscall(Value, Vec<Value>),
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name_def: Range,
    pub name: String,
    pub type_def: Range,
    pub ty: TypeIdx,
    pub mutable: bool,
}

#[derive(Debug, Default)]
pub struct ReturnType {
    pub type_def: Option<Range>,
    pub ty: TypeIdx,
}

#[derive(Debug, Default)]
pub struct FunSign {
    pub def: Option<Range>,
    pub name: String,
    pub generics: Generics,

    pub params: VecMap<ParamIdx, Param>,
    pub effect_params: Vec<Param>,
    pub return_type: ReturnType,
}

impl Default for TypeIdx {
    fn default() -> Self {
        Self(0)
    }
}

#[derive(Debug)]
pub struct AssocDef {
    pub assoc: Assoc,
    pub infer: bool,
    pub generics: Generics,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Generic {
    pub idx: GenericIdx,
    pub typeof_ty: TypeIdx,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Assoc {
    pub idx: AssocIdx,
    pub typeof_ty: TypeIdx,
}

#[derive(Debug, Default)]
pub struct Effect {
    pub name: String,
    pub generics: Generics, // indices correspond 1-1 with ast generics

    pub assocs: Vec<AssocDef>,

    pub funs: VecMap<EffFunIdx, FunSign>,
    pub implied: Vec<HandlerIdx>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct EffectIdent {
    pub effect: EffIdx,
    pub generic_params: GenericParams,
}

pub type Generics = Vec<Generic>;
pub type GenericParams = Vec<(GenericIdx, TypeIdx)>;

#[derive(Debug)]
pub struct Capture {
    pub debug_name: String,
    pub ty: TypeIdx,
}

#[derive(Debug)]
pub struct Handler {
    pub debug_name: String,
    pub generics: Generics,

    pub effect: EffIdx,
    pub generic_params: GenericParams,
    pub fail: TypeIdx,

    pub assoc_types: Vec<(AssocIdx, TypeIdx)>,

    pub captures: Vec<Capture>,
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

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum TypeConstraints {
    None,
    Handler(GenericVal<EffectIdent>, TypeIdx), // effect, fail
    BoundHandler(GenericVal<EffectIdent>),
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
    Handler {
        idx: HandlerIdx,
        generic_params: GenericParams,
        bound: bool,
    },

    LazyHandler(TypeIdx, LazyIdx),
    HandlerSelf,

    DataType(TypeConstraints),
    Effect,

    Generic(Generic),
    AssocType {
        assoc: Assoc,
        handler: TypeIdx,
        effect: EffIdx,
        generic_params: GenericParams,
    },

    Pointer(TypeIdx),
    Const(TypeIdx),
    ConstArray(GenericVal<u64>, TypeIdx),
    Slice(TypeIdx),

    Integer(bool, IntSize),

    Str,
    Char,
    Bool,
    None,
    Never,
    Unknown,
}

#[derive(Debug)]
pub struct SemIR {
    pub effects: VecMap<EffIdx, Effect>,
    pub fun_sign: VecMap<FunIdx, FunSign>,
    pub fun_impl: VecMap<FunIdx, FunImpl>,
    pub entry: Option<FunIdx>,

    pub types: VecSet<TypeIdx, Type>,
    pub handlers: VecMap<HandlerIdx, Handler>,
    pub lazy_handlers: VecMap<LazyIdx, Option<Either<HandlerIdx, LazyIdx>>>,

    pub generic_names: VecMap<GenericIdx, String>,
    pub assoc_names: VecMap<AssocIdx, String>,
}

impl TypeConstraints {
    fn display(
        &self,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        match *self {
            TypeConstraints::None => Ok(()),
            TypeConstraints::Handler(ref effect, fail) => {
                write!(f, " / handle ")?;
                match *effect {
                    GenericVal::Literal(ref effect) => {
                        write!(f, "{}", ir.effects[effect.effect].name)?;

                        if !effect.generic_params.is_empty() {
                            write!(f, "<")?;
                            let mut iter = effect.generic_params.iter().copied();

                            let first = iter.next().unwrap();
                            first.1.display(ir, generic_params, f)?;
                            for next in iter {
                                write!(f, ", ")?;
                                next.1.display(ir, generic_params, f)?;
                            }
                            write!(f, ">")?;
                        }
                    }
                    GenericVal::Generic(idx) => write!(f, "`{}", usize::from(idx))?,
                }
                match ir.types[fail] {
                    Type::Never => {}
                    Type::None => write!(f, " fails")?,
                    _ => {
                        write!(f, " fails ")?;
                        fail.display(ir, generic_params, f)?;
                    }
                }
                Ok(())
            }
            TypeConstraints::BoundHandler(ref effect) => {
                write!(f, " / bound ")?;
                match *effect {
                    GenericVal::Literal(ref effect) => {
                        write!(f, "{}", ir.effects[effect.effect].name)?;

                        if !effect.generic_params.is_empty() {
                            write!(f, "<")?;
                            let mut iter = effect.generic_params.iter().copied();

                            let first = iter.next().unwrap();
                            first.1.display(ir, generic_params, f)?;
                            for next in iter {
                                write!(f, ", ")?;
                                next.1.display(ir, generic_params, f)?;
                            }
                            write!(f, ">")?;
                        }
                    }
                    GenericVal::Generic(idx) => write!(f, "`{}", usize::from(idx))?,
                }
                Ok(())
            }
        }
    }
}

pub fn get_param(generic_params: &GenericParams, idx: GenericIdx) -> Option<TypeIdx> {
    get_value(generic_params, &idx).copied()
}

pub fn get_value<'a, K: PartialEq, V>(vec: &'a Vec<(K, V)>, key: &K) -> Option<&'a V> {
    vec.iter().find(|(k, _)| k.eq(key)).map(|(_, v)| v)
}

pub fn get_value_mut<'a, K: PartialEq, V>(vec: &'a mut Vec<(K, V)>, key: &K) -> Option<&'a mut V> {
    vec.iter_mut().find(|(k, _)| k.eq(key)).map(|(_, v)| v)
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
        typeof_ty: TypeIdx,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        match ir.lazy_handlers[*self] {
            Some(idx) => match idx {
                Either::Left(idx) => {
                    write!(f, "{}", ir.handlers[idx].debug_name)
                }
                Either::Right(idx) => idx.display(typeof_ty, ir, generic_params, f),
            },
            None => {
                write!(f, "LAZY#{}", self.0)?;
                match ir.types[typeof_ty] {
                    Type::DataType(ref costraints) => costraints.display(ir, generic_params, f),
                    _ => {
                        write!(f, " ")?;
                        typeof_ty.display(ir, generic_params, f)
                    }
                }
            }
        }
    }
}

impl TypeIdx {
    fn display(
        &self,
        ir: &SemIR,
        generic_params: &GenericParams,
        f: &mut impl fmt::Write,
    ) -> fmt::Result {
        match ir.types[*self] {
            Type::HandlerSelf => write!(f, "self"),
            Type::Handler { idx, .. } => {
                // TODO: expand
                write!(f, "{}", ir.handlers[idx].debug_name)
            }
            Type::DataType(ref constraints) => {
                write!(f, "type")?;
                constraints.display(ir, generic_params, f)
            }
            Type::AssocType {
                assoc,
                generic_params: ref params,
                ..
            } => {
                write!(f, "{}", ir.assoc_names[assoc.idx])?;
                if !params.is_empty() {
                    write!(f, "<")?;
                    let mut iter = params.iter().copied();

                    let first = iter.next().unwrap();
                    first.1.display(ir, generic_params, f)?;
                    for next in iter {
                        write!(f, ", ")?;
                        next.1.display(ir, generic_params, f)?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Type::Effect => write!(f, "effect"),
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
            Type::Const(inner) => {
                write!(f, "const ")?;
                inner.display(ir, generic_params, f)
            }
            Type::ConstArray(size, inner) => {
                write!(f, "[")?;
                match size {
                    GenericVal::Literal(size) => write!(f, "{}", size)?,
                    GenericVal::Generic(idx) => write!(f, "`{}", usize::from(idx))?,
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
            Type::None => write!(f, "void"),
            Type::Never => write!(f, "!"),
            Type::Unknown => write!(f, "UNKNOWN"),
            Type::LazyHandler(typeof_ty, idx) => idx.display(typeof_ty, ir, generic_params, f),
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
        match ir.types[next] {
            Type::DataType(ref constraints) => constraints.display(ir, generic_params, f)?,
            _ => {
                write!(f, " ")?;
                next.display(ir, generic_params, f)?;
            }
        }

        for generic in iter {
            let idx = generic.idx;
            let next = generic.typeof_ty;

            write!(f, ", {}", ir.generic_names[idx])?;
            match ir.types[next] {
                Type::DataType(ref constraints) => constraints.display(ir, generic_params, f)?,
                _ => {
                    write!(f, " ")?;
                    next.display(ir, generic_params, f)?;
                }
            }
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
        if !self.effect_params.is_empty() {
            write!(f, " / ")?;
            let mut iter = self.effect_params.iter().map(|param| param.ty);

            let first = iter.next().unwrap();
            first.display(ir, no_params, f)?;
            for next in iter {
                write!(f, " ")?;
                next.display(ir, no_params, f)?;
            }
        }
        Ok(())
    }
}

impl Value {
    fn display(&self, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        match *self {
            Value::Reg(block, instr) => write!(f, "%{}.{}", block.0, instr.0),
            Value::Reference(block, instr) => write!(f, "%{}.{}^", block.0, instr.0),
            Value::ConstantInt(signed, n) => write!(f, "{}{}", if signed { "-" } else { "" }, n),
            Value::ConstantString(ref str) => write!(f, "{}", str),
            Value::ConstantBool(b) => write!(f, "{}", b),
            Value::ConstantType(ty) => ty.display(ir, &Vec::new(), f),
            Value::ConstantNone => write!(f, "{{}}"),
            Value::ConstantUninit => write!(f, "---"),
            Value::ConstantZero => write!(f, "0"),
            Value::ConstantUnknown => write!(f, "ERR"),
            Value::ConstantAggregate(ref vec) => {
                write!(f, "[")?;
                for val in vec {
                    write!(f, " ")?;
                    val.display(ir, f)?;
                    write!(f, ",")?;
                }
                write!(f, "]")?;
                Ok(())
            }
            Value::Param(param) => write!(f, "%p{}", param.0),
            Value::HandlerParam(param) => write!(f, "%h{}", param),
        }
    }
}

impl FunImpl {
    fn display(&self, padding: &str, ir: &SemIR, f: &mut impl fmt::Write) -> fmt::Result {
        for (idx, block) in self.blocks.iter(BlockIdx) {
            writeln!(f, "{}B{}", padding, idx.0)?;
            for (i, instr) in block.instructions.iter(InstrIdx) {
                write!(f, "{}  ", padding)?;
                match instr {
                    Instruction::Cast(v, t) => {
                        write!(f, "cast ")?;
                        v.display(ir, f)?;
                        write!(f, " as ")?;
                        t.display(ir, &Vec::new(), f)?;
                    }
                    Instruction::Jump(block) => {
                        write!(f, "jump B{}", block.0)?;
                    }
                    Instruction::Branch(cond, yes, no) => {
                        write!(f, "branch ")?;
                        cond.display(ir, f)?;
                        write!(f, " B{} else B{}", yes.0, no.0)?;
                    }
                    Instruction::Phi(vec) => {
                        write!(f, "phi",)?;
                        for (val, block) in vec {
                            write!(f, " B{}: ", block.0)?;
                            val.display(ir, f)?;
                            write!(f, ",")?;
                        }
                    }
                    Instruction::Equals(a, b) => {
                        write!(f, "== ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Greater(a, b) => {
                        write!(f, "> ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Less(a, b) => {
                        write!(f, "< ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Div(a, b) => {
                        write!(f, "/ ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Mul(a, b) => {
                        write!(f, "* ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Add(a, b) => {
                        write!(f, "+ ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Sub(a, b) => {
                        write!(f, "- ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Trap => {
                        write!(f, "trap")?;
                    }
                    Instruction::Yeet(v) => {
                        write!(f, "fail ")?;
                        v.display(ir, f)?;
                    }
                    Instruction::Return(v) => {
                        write!(f, "return ")?;
                        v.display(ir, f)?;
                    }
                    Instruction::Unreachable => {
                        write!(f, "unreachable")?;
                    }
                    Instruction::Reference(v) => {
                        write!(f, "alloca ")?;
                        v.display(ir, f)?;
                    }
                    Instruction::Load(v) => {
                        write!(f, "load ")?;
                        v.display(ir, f)?;
                    }
                    Instruction::Store(a, b) => {
                        write!(f, "store ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::Member(v, n) => {
                        write!(f, "member ")?;
                        v.display(ir, f)?;
                        write!(f, " {}", n)?;
                    }
                    Instruction::ElementPtr(a, b) => {
                        write!(f, "elemptr ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }
                    Instruction::AdjacentPtr(a, b) => {
                        write!(f, "adjptr ")?;
                        a.display(ir, f)?;
                        write!(f, " ")?;
                        b.display(ir, f)?;
                    }

                    Instruction::PushHandler(_) => todo!(),
                    Instruction::Call(_, _, _, _) => todo!(),
                    Instruction::PopHandler => todo!(),
                    Instruction::Trace(_) => todo!(),
                    Instruction::Syscall(_, _) => todo!(),
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

        // assoc
        for assoc in self.assocs.iter() {
            match ir.types[assoc.assoc.typeof_ty] {
                Type::DataType(ref constraints) => {
                    write!(f, "  type {}", ir.assoc_names[assoc.assoc.idx])?;
                    display_generics(&assoc.generics, ir, no_params, f)?;
                    constraints.display(ir, no_params, f)?;
                }
                _ => {
                    write!(f, "  let {}", ir.assoc_names[assoc.assoc.idx])?;
                    display_generics(&assoc.generics, ir, no_params, f)?;
                    write!(f, " ")?;
                    assoc.assoc.typeof_ty.display(ir, no_params, f)?;
                }
            }
            writeln!(f)?;
        }

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
            write!(f, "  {} ", capture.debug_name)?;
            capture.ty.display(ir, no_params, f)?;
        }

        // assoc
        for (idx, ty) in self.assoc_types.iter().copied() {
            let def = ir.effects[self.effect]
                .assocs
                .iter()
                .find(|def| def.assoc.idx == idx)
                .unwrap();
            match ir.types[def.assoc.typeof_ty] {
                Type::DataType(ref constraints) => {
                    write!(f, "  type {}", ir.assoc_names[idx])?;
                    display_generics(&def.generics, ir, &self.generic_params, f)?;
                    constraints.display(ir, &self.generic_params, f)?;
                }
                _ => {
                    write!(f, "  let {}", ir.assoc_names[idx])?;
                    display_generics(&def.generics, ir, &self.generic_params, f)?;
                    write!(f, " ")?;
                    def.assoc.typeof_ty.display(ir, &self.generic_params, f)?;
                }
            }
            write!(f, " = ")?;
            ty.display(ir, no_params, f)?;
            writeln!(f)?;
        }

        // funs
        for fun in self.funs.values() {
            // fun signature
            fun.0.display("  ", ir, f)?;
            writeln!(f)?;

            // fun impl
            fun.1.display("  ", ir, f)?;
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
            imp.display("", self, f)?;
        }

        Ok(())
    }
}
