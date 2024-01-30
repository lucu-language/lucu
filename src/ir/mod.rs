use std::{
    collections::HashSet,
    fmt::{self, Display},
    write,
};

use crate::{
    sema::BlockIdx,
    vecmap::{vecmap_index, VecMap, VecSet},
};

mod codegen;
pub use codegen::codegen;

#[derive(Debug)]
pub struct ProcSign {
    pub debug_name: String,
    pub inputs: Vec<Reg>,
    pub output: TypeIdx,
    pub unhandled: Vec<HandlerIdx>,
}

#[derive(Debug)]
pub struct ProcForeign {
    pub inputs: Vec<TypeIdx>,
    pub output: TypeIdx,
    pub symbol: String,
}

#[derive(Debug, Default)]
pub struct ProcImpl {
    pub blocks: VecMap<BlockIdx, Block>,
}

impl ProcImpl {
    pub fn instructions(&self) -> impl Iterator<Item = &Instruction> {
        self.blocks.values().flat_map(|b| b.instructions.iter())
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
    Int64,

    Bool,

    Pointer(TypeIdx),
    ConstArray(u64, TypeIdx),
    Aggregate(AggrIdx),
    Handler(HandlerIdx, AggrIdx),

    Unit,
    Never,
}

impl TypeIdx {
    pub fn inner(self, ir: &IR) -> TypeIdx {
        match ir.types[self] {
            Type::Pointer(ty) => ty,
            Type::ConstArray(_, ty) => ty,
            Type::Never => self,
            _ => unreachable!(),
        }
    }
}

pub struct AggregateType {
    pub children: Vec<TypeIdx>,
    pub debug_name: String,
}

vecmap_index!(TypeIdx);
vecmap_index!(AggrIdx);
vecmap_index!(Reg);

impl Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "R{:02}", self.0)
    }
}

impl Display for BlockIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "L{}", self.0)
    }
}

#[derive(Debug, Default)]
pub struct Block {
    pub phis: Vec<(Reg, Vec<(Reg, BlockIdx)>)>,
    pub instructions: Vec<Instruction>,
}

#[derive(Debug)]
pub enum Instruction {
    Init(Reg, u64),
    InitString(Reg, String),
    Copy(Reg, Reg),
    Uninit(Reg),
    Zeroinit(Reg),
    Cast(Reg, Reg),

    // conditionals
    Jump(BlockIdx),
    Branch(Reg, BlockIdx, BlockIdx),

    // operations (r0 = r1 op r2)
    Equals(Reg, Reg, Reg),
    Greater(Reg, Reg, Reg),
    Less(Reg, Reg, Reg),
    Div(Reg, Reg, Reg),
    Mul(Reg, Reg, Reg),
    Add(Reg, Reg, Reg),
    Sub(Reg, Reg, Reg),

    // call procedure, put return into reg, call with arguments
    Call(ProcIdx, Option<Reg>, Vec<Reg>, Vec<(HandlerIdx, BlockIdx)>),
    CallForeign(ProcForeignIdx, Option<Reg>, Vec<Reg>),

    // return statements
    Yeet(Option<Reg>, Option<HandlerIdx>, Option<BlockIdx>), // break with optional value to handler
    Return(Option<Reg>),                                     // return with optional value
    Unreachable,

    // pointers
    Reference(Reg, Reg),
    Load(Reg, Reg),
    Store(Reg, Reg),

    // aggregate types
    Aggregate(Reg, Vec<Reg>),
    Member(Reg, Reg, usize),
    ElementPtr(Reg, Reg, usize),
    AdjacentPtr(Reg, Reg, Reg),

    // architecture-specific operations
    Syscall(Option<Reg>, Reg, Vec<Reg>),
    WasmTrap,
}

vecmap_index!(ProcIdx);
vecmap_index!(ProcForeignIdx);
vecmap_index!(HandlerIdx);

pub struct IR {
    pub proc_sign: VecMap<ProcIdx, ProcSign>,
    pub proc_impl: VecMap<ProcIdx, ProcImpl>,
    pub proc_foreign: VecMap<ProcForeignIdx, ProcForeign>,
    pub entry: ProcIdx,

    pub regs: VecMap<Reg, TypeIdx>,

    pub types: VecSet<TypeIdx, Type>,
    pub break_types: VecMap<HandlerIdx, TypeIdx>,
    pub aggregates: VecMap<AggrIdx, AggregateType>,

    pub links: HashSet<String>,
}

impl Display for IR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (sign, imp) in self.proc_sign.values().zip(self.proc_impl.values()) {
            // write proc signature
            write!(f, "{}", sign.debug_name)?;

            if !sign.inputs.is_empty() {
                write!(f, " ( ")?;
                for &r in sign.inputs.iter() {
                    if r != *sign.inputs.first().unwrap() {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", r)?;
                }
                write!(f, " )")?;
            }

            writeln!(f, " {{")?;

            // write blocks
            for (i, block) in imp.blocks.values().enumerate() {
                // write label
                if i > 0 {
                    writeln!(f, "{}:", BlockIdx(i))?;
                }

                // write phi
                for (r, phi) in block.phis.iter() {
                    writeln!(
                        f,
                        "{} <- phi {}",
                        r,
                        phi.iter()
                            .map(|(r, b)| format!("[ {}, {}, ]", r, b))
                            .collect::<Vec<_>>()
                            .join(" ")
                    )?;
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
                        Instruction::Zeroinit(r) => writeln!(f, "{} <- {{0}}", r)?,
                        Instruction::Jump(b) => writeln!(f, "       jmp {}", b)?,
                        Instruction::Branch(r, y, n) => {
                            writeln!(f, "       jnz {}, {}, {}", r, y, n)?
                        }
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
                        Instruction::Call(proc, out, ref args, _) => writeln!(
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
                        Instruction::Yeet(r, h, _) => writeln!(
                            f,
                            "       brk {:?}{}",
                            h.map(|h| usize::from(h)),
                            match r {
                                Some(r) => format!(", {}", r),
                                None => "".into(),
                            },
                        )?,
                        Instruction::Aggregate(r, ref v) => writeln!(
                            f,
                            "{} <- {{ {} }}",
                            r,
                            v.iter()
                                .map(|r| r.to_string())
                                .collect::<Vec<_>>()
                                .join(", "),
                        )?,
                        Instruction::Member(r, a, m) => writeln!(f, "{} <- {}.{}", r, a, m)?,
                        Instruction::Unreachable => writeln!(f, "       unreachable")?,
                        Instruction::Reference(ptr, r) => writeln!(f, "{} <- &{}", ptr, r)?,
                        Instruction::Load(r, ptr) => writeln!(f, "{} <- load {}", r, ptr)?,
                        Instruction::Store(ptr, r) => writeln!(f, "       store {}, {}", ptr, r)?,
                        Instruction::ElementPtr(r, a, m) => {
                            writeln!(f, "{} <- gep {}, 0, {}", r, a, m)?
                        }
                        Instruction::AdjacentPtr(r, a, m) => {
                            writeln!(f, "{} <- gep {}, {}", r, a, m)?
                        }
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
                        Instruction::WasmTrap => writeln!(f, "       wasm: unreachable")?,
                    }
                }
            }

            // end proc
            writeln!(f, "}}")?;
        }
        Ok(())
    }
}
