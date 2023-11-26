use std::{
    collections::HashSet,
    fmt::{self, Display},
    rc::Rc,
    write,
};

use crate::{
    analyzer::Val,
    vecmap::{vecmap_index, VecMap, VecSet},
};

mod codegen;
pub use codegen::*;

// TODO: remove
#[derive(Debug, Clone)]
pub enum Value {
    Value(Reg, Option<Val>),
    Reference(Reg),
    Global(Global),
}

impl Value {
    pub fn get_type(&self, ir: &IR) -> TypeIdx {
        match *self {
            Value::Value(reg, _) => ir.regs[reg],
            Value::Reference(reg) => ir.regs[reg].inner(ir),
            Value::Global(glob) => ir.globals[glob],
        }
    }
}

// TODO: remove
#[derive(Debug)]
pub struct Captures {
    pub input: Value,
    pub members: Vec<Reg>,
}

#[derive(Debug)]
pub struct ProcSign {
    pub inputs: Vec<Reg>,
    pub captures: Option<Captures>,

    pub output: TypeIdx,
    pub debug_name: String,

    pub unhandled: Vec<HandlerIdx>,
    pub handled: Vec<HandlerIdx>,
    pub redirect: Vec<(HandlerIdx, HandlerIdx)>,
}

#[derive(Debug)]
pub struct ProcForeign {
    pub inputs: Vec<TypeIdx>,
    pub output: TypeIdx,
    pub symbol: String,
}

#[derive(Debug)]
pub struct ProcImpl {
    pub blocks: VecMap<BlockIdx, Block>,
}

impl ProcImpl {
    pub fn calls(&self) -> impl Iterator<Item = ProcIdx> + '_ {
        self.blocks
            .values()
            .flat_map(|b| b.instructions.iter())
            .filter_map(|i| match i {
                &Instruction::Call(p, _, _) => Some(p),
                _ => None,
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    IntSize,
    IntPtr,
    Int8,
    Int16,
    Int32,

    Bool,

    Pointer(TypeIdx),
    ConstArray(u64, TypeIdx),
    Slice(TypeIdx),

    Aggregate(AggrIdx),

    // Handler without a try-with block purther up the stack
    NakedHandler(HandlerIdx),
    RawHandler(HandlerIdx, Rc<[usize]>),

    // Handler from a try-with block
    Handler(HandlerIdx),

    // TODO: remove
    // Temporary output value of functions that return handlers, includes eff val and failure type
    HandlerOutput(Val, TypeIdx),

    Never,
    None,
}

impl TypeIdx {
    pub fn is_never(self) -> bool {
        self == TYPE_NEVER
    }
    pub fn inner(self, ir: &IR) -> TypeIdx {
        match ir.types[self] {
            Type::Pointer(ty) => ty,
            Type::ConstArray(_, ty) => ty,
            Type::Slice(ty) => ty,
            Type::HandlerOutput(_, ty) => ty,
            Type::Handler(idx) | Type::NakedHandler(idx) | Type::RawHandler(idx, _) => {
                ir.handler_type[idx].break_ty
            }
            Type::Never => TYPE_NEVER,
            _ => unreachable!(),
        }
    }
    pub fn is_handler_of(self, ir: &IR, handler_idx: HandlerIdx) -> bool {
        match ir.types[self] {
            Type::NakedHandler(idx) | Type::RawHandler(idx, _) | Type::Handler(idx) => {
                idx == handler_idx
            }
            _ => false,
        }
    }
    pub fn is_handler(self, ir: &IR) -> bool {
        match ir.types[self] {
            Type::NakedHandler(_)
            | Type::RawHandler(_, _)
            | Type::Handler(_)
            | Type::HandlerOutput(_, _) => true,
            _ => false,
        }
    }
}

pub struct AggregateType {
    pub children: Vec<TypeIdx>,
    pub debug_name: String,
}

vecmap_index!(BlockIdx);
vecmap_index!(TypeIdx);
vecmap_index!(AggrIdx);
vecmap_index!(Reg);
vecmap_index!(Global);

impl Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "R{:02}", self.0)
    }
}

impl Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "G{:02}", self.0)
    }
}

impl Display for BlockIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "L{}", self.0)
    }
}

#[derive(Debug, Default)]
pub struct Block {
    pub instructions: Vec<Instruction>,
    pub next: Option<BlockIdx>,
}

#[derive(Debug)]
pub enum Instruction {
    Init(Reg, u64),
    InitString(Reg, String),
    Copy(Reg, Reg),
    Uninit(Reg),
    Zeroinit(Reg),
    Cast(Reg, Reg),

    // globals
    SetScopedGlobal(Global, Reg, BlockIdx),
    GetGlobal(Reg, Global),
    GetGlobalPtr(Reg, Global),

    // conditionals
    Branch(Reg, BlockIdx, BlockIdx),
    Phi(Reg, Vec<(Reg, BlockIdx)>),

    // operations (r0 = r1 op r2)
    Equals(Reg, Reg, Reg),
    Greater(Reg, Reg, Reg),
    Less(Reg, Reg, Reg),
    Div(Reg, Reg, Reg),
    Mul(Reg, Reg, Reg),
    Add(Reg, Reg, Reg),
    Sub(Reg, Reg, Reg),

    // call procedure, put return into reg, call with arguments
    Call(ProcIdx, Option<Reg>, Vec<Reg>),
    CallForeign(ProcForeignIdx, Option<Reg>, Vec<Reg>),

    // return statements
    Yeet(Option<Reg>, HandlerIdx), // break with optional value to handler
    Return(Option<Reg>),           // return with optional value
    Unreachable,

    // pointers
    Reference(Reg, Reg),
    Load(Reg, Reg),
    Store(Reg, Reg),

    // handler types
    Handler(Reg, Vec<Reg>),
    RawHandler(Reg, Reg),
    UnrawHandler(Reg, Reg),

    // aggregate types
    Aggregate(Reg, Vec<Reg>),
    Member(Reg, Reg, usize),
    ElementPtr(Reg, Reg, Reg),
    AdjacentPtr(Reg, Reg, Reg),

    // kernel operations
    Trap,
    Trace(Reg),
    Syscall(Option<Reg>, Reg, Vec<Reg>),
    GS(Reg, u64), // read value at GS register with offset into reg
}

vecmap_index!(ProcIdx);
vecmap_index!(ProcForeignIdx);
vecmap_index!(HandlerIdx);

#[derive(Debug, Clone)]
pub struct HandlerType {
    pub captures: Vec<TypeIdx>,
    pub break_ty: TypeIdx,
}
pub struct IR {
    pub proc_sign: VecMap<ProcIdx, ProcSign>,
    pub proc_impl: VecMap<ProcIdx, ProcImpl>,
    pub proc_foreign: VecMap<ProcForeignIdx, ProcForeign>,
    pub entry: ProcIdx,

    pub regs: VecMap<Reg, TypeIdx>,
    pub globals: VecMap<Global, TypeIdx>,

    pub types: VecSet<TypeIdx, Type>,
    pub handler_type: VecMap<HandlerIdx, HandlerType>,
    pub aggregates: VecMap<AggrIdx, AggregateType>,

    pub links: HashSet<String>,
}

impl Display for IR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (sign, imp) in self.proc_sign.values().zip(self.proc_impl.values()) {
            // write proc signature
            write!(f, "{}", sign.debug_name)?;

            if sign.inputs.len() > 0 {
                write!(f, " ( ")?;
                for &r in sign.inputs.iter() {
                    if r != *sign.inputs.first().unwrap() {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", r)?;
                }
                write!(f, " )")?;
            }

            if sign.unhandled.len() > 0 {
                write!(f, " / ")?;
                for handler in sign.unhandled.iter().copied() {
                    if handler != sign.unhandled.first().copied().unwrap() {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", usize::from(handler))?
                }
            }

            if sign.handled.len() > 0 {
                write!(f, " try ")?;
                for handler in sign.handled.iter().copied() {
                    if handler != sign.handled.first().copied().unwrap() {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", usize::from(handler))?
                }
            }

            write!(f, " {{\n")?;

            // write blocks
            for (i, block) in imp.blocks.values().enumerate() {
                // write label
                if i > 0 {
                    writeln!(f, "{}:", BlockIdx(i))?;
                }

                // write instructions
                for instr in block.instructions.iter() {
                    write!(f, "  ")?;
                    match *instr {
                        Instruction::Init(r, v) => writeln!(f, "{} <- {}", r, v)?,
                        Instruction::InitString(r, ref v) => writeln!(f, "{} <- \"{}\"", r, v)?,
                        Instruction::Copy(r, v) => writeln!(f, "{} <- {}", r, v)?,
                        Instruction::Cast(r, v) => writeln!(f, "{} <- cast {}", r, v)?,
                        Instruction::Uninit(r) => writeln!(f, "{} <- ---", r)?,
                        Instruction::Zeroinit(r) => writeln!(f, "{} <- {0}", r)?,
                        Instruction::Branch(r, y, n) => {
                            writeln!(f, "       jnz {}, {}, {}", r, y, n)?
                        }
                        Instruction::Phi(r, ref v) => writeln!(
                            f,
                            "{} <- phi {}",
                            r,
                            v.iter()
                                .map(|(r, b)| format!("[ {}, {} ]", r, b))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )?,
                        Instruction::Equals(out, left, right) => {
                            writeln!(f, "{} <- {} == {}", out, left, right)?
                        }
                        Instruction::Greater(out, left, right) => {
                            writeln!(f, "{} <- {} > {}", out, left, right)?
                        }
                        Instruction::Less(out, left, right) => {
                            writeln!(f, "{} <- {} < {}", out, left, right)?
                        }
                        Instruction::Div(out, left, right) => {
                            writeln!(f, "{} <- {} / {}", out, left, right)?
                        }
                        Instruction::Mul(out, left, right) => {
                            writeln!(f, "{} <- {} * {}", out, left, right)?
                        }
                        Instruction::Add(out, left, right) => {
                            writeln!(f, "{} <- {} + {}", out, left, right)?
                        }
                        Instruction::Sub(out, left, right) => {
                            writeln!(f, "{} <- {} - {}", out, left, right)?
                        }
                        Instruction::Call(proc, out, ref args) => writeln!(
                            f,
                            "{}cal {}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            self.proc_sign[proc].debug_name,
                            match args
                                .iter()
                                .map(|r| r.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                                .as_str()
                            {
                                "" => "".into(),
                                a => format!(" ( {} )", a),
                            },
                        )?,
                        Instruction::CallForeign(proc, out, ref args) => writeln!(
                            f,
                            "{}cal {}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            self.proc_foreign[proc].symbol,
                            match args
                                .iter()
                                .map(|r| r.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                                .as_str()
                            {
                                "" => "".into(),
                                a => format!(" ( {} )", a),
                            },
                        )?,
                        Instruction::Return(r) => writeln!(
                            f,
                            "       ret{}",
                            match r {
                                Some(r) => format!(" {}", r),
                                None => "".into(),
                            },
                        )?,
                        Instruction::Yeet(r, h) => writeln!(
                            f,
                            "       brk {}{}",
                            usize::from(h),
                            match r {
                                Some(r) => format!(", {}", r),
                                None => "".into(),
                            },
                        )?,
                        Instruction::Aggregate(r, ref v) | Instruction::Handler(r, ref v) => {
                            writeln!(
                                f,
                                "{} <- {{ {} }}",
                                r,
                                v.iter()
                                    .map(|r| r.to_string())
                                    .collect::<Vec<_>>()
                                    .join(", "),
                            )?
                        }
                        Instruction::Member(r, a, m) => writeln!(f, "{} <- {}.{}", r, a, m)?,
                        Instruction::Unreachable => writeln!(f, "       unreachable")?,
                        Instruction::SetScopedGlobal(g, r, e) => {
                            writeln!(f, "{} <- ssg {}, {}", g, r, e)?
                        }
                        Instruction::GetGlobal(r, g) => writeln!(f, "{} <- ggl {}", r, g)?,
                        Instruction::GetGlobalPtr(r, g) => writeln!(f, "{} <- &ggl {}", r, g)?,
                        Instruction::Reference(ptr, r) => writeln!(f, "{} <- &{}", ptr, r)?,
                        Instruction::Load(r, ptr) => writeln!(f, "{} <- load {}", r, ptr)?,
                        Instruction::Store(ptr, r) => writeln!(f, "       store {}, {}", ptr, r)?,
                        Instruction::RawHandler(r, h) => writeln!(f, "{} <- raw {}", r, h)?,
                        Instruction::UnrawHandler(r, h) => writeln!(f, "{} <- unraw {}", r, h)?,
                        Instruction::ElementPtr(r, a, m) => {
                            writeln!(f, "{} <- gep {}, 0, {}", r, a, m)?
                        }
                        Instruction::AdjacentPtr(r, a, m) => {
                            writeln!(f, "{} <- gep {}, {}", r, a, m)?
                        }
                        Instruction::Trap => writeln!(f, "       trap")?,
                        Instruction::Trace(r) => writeln!(f, "       trace {}", r)?,
                        Instruction::Syscall(out, nr, ref args) => writeln!(
                            f,
                            "{}syscall {}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            nr,
                            match args
                                .iter()
                                .map(|r| r.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                                .as_str()
                            {
                                "" => "".into(),
                                a => format!(" ( {} )", a),
                            },
                        )?,
                        Instruction::GS(reg, offset) => writeln!(f, "{} <- GS:{}", reg, offset)?,
                    }
                }

                // write next
                if let Some(b) = block.next {
                    if usize::from(b) != i + 1 {
                        writeln!(f, "         jmp L{}", usize::from(b))?;
                    }
                }
            }

            // end proc
            writeln!(f, "}}")?;
        }
        Ok(())
    }
}

const TYPE_NEVER: TypeIdx = TypeIdx(0);
const TYPE_NONE: TypeIdx = TypeIdx(1);

const TYPE_STR_SLICE: TypeIdx = TypeIdx(5);
const TYPE_BOOL: TypeIdx = TypeIdx(7);
