use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    rc::Rc,
    write,
};

use either::Either;

use crate::{
    analyzer::{self, Analysis, Definition, Val},
    parser::{self, BinOp, EffFunIdx, ExprIdx, Expression, PackageIdx, Parsed, UnOp},
    vecmap::{vecmap_index, VecMap, VecSet},
};

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
    fn cast(&self, ir: &mut IRContext, block: &mut Block, ty: TypeIdx) -> Value {
        match *self {
            Value::Value(reg, val) => {
                let new = ir.next_reg(ty);
                block.instructions.push(Instruction::Cast(new, reg));
                Value::Value(new, val)
            }
            Value::Reference(ptr) => {
                let ty = ir.insert_type(Type::Pointer(ty));
                let new = ir.next_reg(ty);
                block.instructions.push(Instruction::Cast(new, ptr));
                Value::Reference(new)
            }
            Value::Global(glob) => {
                let t = ir.insert_type(Type::Pointer(ir.ir.globals[glob]));
                let ptr = ir.next_reg(t);
                block
                    .instructions
                    .push(Instruction::GetGlobalPtr(ptr, glob));

                let t = ir.insert_type(Type::Pointer(t));
                let new = ir.next_reg(t);
                block.instructions.push(Instruction::Cast(new, ptr));
                Value::Reference(new)
            }
        }
    }
    fn non_global(&self) -> Option<&Value> {
        match self {
            Value::Global(_) => None,
            _ => Some(self),
        }
    }
    fn value(&self, ir: &mut IRContext, block: &mut Block) -> Reg {
        match *self {
            Value::Value(reg, _) => reg,
            Value::Reference(ptr) => {
                let reg = ir.next_reg(self.get_type(&ir.ir));
                block.instructions.push(Instruction::Load(reg, ptr));
                reg
            }
            Value::Global(glob) => {
                let reg = ir.next_reg(self.get_type(&ir.ir));
                block.instructions.push(Instruction::GetGlobal(reg, glob));
                reg
            }
        }
    }
    fn reference(&self, ir: &mut IRContext, scope: &mut Scope, block: &mut Block) -> Reg {
        match *self {
            Value::Value(reg, val) => {
                let ty = ir.insert_type(Type::Pointer(self.get_type(&ir.ir)));
                let ptr = ir.next_reg(ty);
                block.instructions.push(Instruction::Reference(ptr, reg));
                if let Some(val) = val {
                    scope.insert(val, Value::Reference(ptr));
                }
                ptr
            }
            Value::Reference(ptr) => ptr,
            Value::Global(glob) => {
                let ty = ir.insert_type(Type::Pointer(self.get_type(&ir.ir)));
                let reg = ir.next_reg(ty);
                block
                    .instructions
                    .push(Instruction::GetGlobalPtr(reg, glob));
                reg
            }
        }
    }
    fn register(&self) -> Reg {
        match *self {
            Value::Value(r, _) => r,
            _ => unreachable!(),
        }
    }
}

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
pub struct ProcImpl {
    pub blocks: VecMap<BlockIdx, Block>,
}

impl ProcImpl {
    fn calls(&self) -> impl Iterator<Item = ProcIdx> + '_ {
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

    // Temporary output value of functions that return handlers
    HandlerOutput,

    Never,
    None,
}

impl TypeIdx {
    fn is_never(self) -> bool {
        self == TYPE_NEVER
    }

    pub fn inner(self, ir: &IR) -> TypeIdx {
        match ir.types[self] {
            Type::Pointer(ty) => ty,
            Type::ConstArray(_, ty) => ty,
            Type::Never => TYPE_NEVER,
            _ => unreachable!(),
        }
    }
    fn is_handler(self, ir: &IRContext) -> bool {
        match ir.ir.types[self] {
            Type::NakedHandler(_)
            | Type::RawHandler(_, _)
            | Type::Handler(_)
            | Type::HandlerOutput => true,
            _ => false,
        }
    }
    fn from_type(ir: &mut IRContext, typ: analyzer::TypeIdx) -> TypeIdx {
        use analyzer::Type as T;
        match ir.asys.types[typ] {
            T::Int => ir.insert_type(Type::Int),
            T::USize => ir.insert_type(Type::IntSize),
            T::UPtr => ir.insert_type(Type::IntPtr),
            T::U8 => ir.insert_type(Type::Int8),
            T::Str => {
                let u8 = ir.insert_type(Type::Int8);
                ir.insert_type(Type::Slice(u8))
            }
            T::Bool => ir.insert_type(Type::Bool),
            T::None => ir.insert_type(Type::None),
            T::Never => ir.insert_type(Type::Never),
            T::Pointer(ty) => {
                let inner = TypeIdx::from_type(ir, ty);
                ir.insert_type(Type::Pointer(inner))
            }
            T::ConstArray(size, ty) => {
                let inner = TypeIdx::from_type(ir, ty);
                ir.insert_type(Type::ConstArray(size, inner))
            }
            T::Slice(ty) => {
                let inner = TypeIdx::from_type(ir, ty);
                ir.insert_type(Type::Slice(inner))
            }
            T::FunctionLiteral(_) => todo!(),
            T::PackageLiteral(_) => todo!(),

            // Supposed to be handled on a case-by-case basis
            T::Handler(_, _, _) => unreachable!(),
            T::Unknown => unreachable!(),
        }
    }
    fn from_return_type(ir: &mut IRContext, typ: analyzer::TypeIdx) -> TypeIdx {
        use analyzer::Type as T;
        match ir.asys.types[typ] {
            T::Handler(_, _, _) => ir.insert_type(Type::HandlerOutput),
            _ => TypeIdx::from_type(ir, typ),
        }
    }
    fn from_val(ir: &mut IRContext, val: Val) -> TypeIdx {
        match ir.asys.defs[val] {
            Definition::Parameter(_, _, _, t) => TypeIdx::from_type(ir, t),
            Definition::Variable(_, _, t) => TypeIdx::from_type(ir, t),
            Definition::EffectFunction(_, _, _) => todo!(),
            Definition::Function(_, _) => todo!(),

            // TODO: type type
            Definition::BuiltinType(_) => todo!(),
            Definition::Package(_) => todo!(),
            Definition::Effect(_) => todo!(),
        }
    }
    fn from_function(ir: &IRContext, val: Val) -> analyzer::TypeIdx {
        match ir.asys.defs[val] {
            Definition::EffectFunction(_, _, t) => t,
            Definition::Function(_, t) => t,
            _ => unreachable!(),
        }
    }
    fn from_expr(ir: &IRContext, expr: ExprIdx) -> analyzer::TypeIdx {
        ir.asys.exprs[expr]
    }
    fn into_result(self, ir: &mut IRContext) -> ExprResult {
        match self {
            TYPE_NEVER => Err(Never),
            TYPE_NONE => Ok(None),
            _ => {
                let reg = ir.next_reg(self);
                Ok(Some(Value::Value(reg, None)))
            }
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

    // return statements
    Yeet(Option<Reg>, HandlerIdx), // break with optional value to handler
    Return(Option<Reg>),           // return with optional value
    Unreachable,

    // print
    PrintNum(Reg), // print number in register
    PrintStr(Reg), // dereference register and print string

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
    Exit(u64),
    Syscall(Option<Reg>, Reg, Vec<Reg>),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ProcIdx(usize);

impl From<ProcIdx> for usize {
    fn from(value: ProcIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct HandlerIdx(usize);

impl From<HandlerIdx> for usize {
    fn from(value: HandlerIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct ProcIdent {
    fun: Either<Val, (HandlerIdx, EffFunIdx)>,
    handlers: Vec<HandlerIdx>,
    handler_params: Vec<TypeIdx>,
}

#[derive(Debug, Clone)]
struct HandlerCtx {
    effect: Val,
    global: Option<Global>,
    definition: Option<ExprIdx>,
    captures: Vec<(Val, TypeIdx, bool)>,
}

#[derive(Debug, Clone)]
pub struct HandlerType {
    pub captures: Vec<TypeIdx>,
    pub break_ty: TypeIdx,
}

struct IRContext<'a> {
    ir: IR,

    proc_map: HashMap<ProcIdent, ProcIdx>,
    implied_handlers: HashMap<Val, HandlerIdx>,

    handlers: VecMap<HandlerIdx, HandlerCtx>,

    parsed: &'a Parsed,
    asys: &'a Analysis,
}

impl<'a> IRContext<'a> {
    fn copy_reg(&mut self, reg: Reg) -> Reg {
        let typ = self.ir.regs[reg];
        self.next_reg(typ)
    }
    fn next_reg(&mut self, typ: TypeIdx) -> Reg {
        self.ir.regs.push(Reg, typ)
    }
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        self.ir.types.insert(TypeIdx, ty).clone()
    }
    fn get_in_scope(&mut self, val: Val, scope: &Scope) -> Value {
        match scope.get(val) {
            Some(r) => r.clone(),
            None => {
                let idx = self.implied_handlers[&val];
                let ty = self.insert_type(Type::NakedHandler(idx));
                let reg = self.next_reg(ty);
                Value::Value(reg, None)
            }
        }
    }
    fn new_handler(
        &mut self,
        eff_val: Val,
        global: bool,
        break_type: TypeIdx,
        definition: ExprIdx,
        scope: &Scope,
    ) -> HandlerIdx {
        let captures = match self.asys.types[self.asys.exprs[definition]] {
            analyzer::Type::Handler(_, _, def) => match def.map(|h| &self.asys.handlers[h]) {
                Some(analyzer::HandlerDef::Handler(_, captures)) => captures
                    .iter()
                    .map(|c| {
                        let ty = match scope.get(c.val) {
                            Some(reg) => reg.get_type(&self.ir),
                            None => TypeIdx::from_val(self, c.val),
                        };
                        let ty = match c.mutable {
                            true => self.insert_type(Type::Pointer(ty)),
                            false => ty,
                        };
                        (c.val, ty, c.mutable)
                    })
                    .collect(),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        // generate handler
        let global = match global {
            true => {
                let ty = self.insert_type(Type::Handler(HandlerIdx(self.handlers.len())));
                Some(self.ir.globals.push(Global, ty))
            }
            false => None,
        };
        let handler_idx = self.handlers.push(
            HandlerIdx,
            HandlerCtx {
                global,
                effect: eff_val,
                definition: Some(definition),
                captures,
            },
        );
        self.ir.handler_type.push_value(HandlerType {
            captures: self.handlers[handler_idx]
                .captures
                .iter()
                .copied()
                .map(|(_, t, _)| t)
                .collect(),
            break_ty: break_type,
        });

        handler_idx
    }
}

pub struct IR {
    pub proc_sign: VecMap<ProcIdx, ProcSign>,
    pub proc_impl: VecMap<ProcIdx, ProcImpl>,
    pub main: ProcIdx,

    pub handler_type: VecMap<HandlerIdx, HandlerType>,

    pub regs: VecMap<Reg, TypeIdx>,
    pub globals: VecMap<Global, TypeIdx>,

    pub types: VecSet<TypeIdx, Type>,

    pub aggregates: VecMap<AggrIdx, AggregateType>,
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
                        Instruction::PrintNum(r) => writeln!(f, "       putint {}", r)?,
                        Instruction::PrintStr(r) => writeln!(f, "       putstr {}", r)?,
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
                        Instruction::Exit(code) => writeln!(f, "       exit {}", code)?,
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
const TYPE_INT: TypeIdx = TypeIdx(6);
const TYPE_BOOL: TypeIdx = TypeIdx(7);

#[derive(Debug, Default)]
struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    values: HashMap<Val, Value>,
}

impl<'a> Scope<'a> {
    fn insert(&mut self, k: Val, v: Value) {
        self.values.insert(k, v);
    }
    fn get(&self, k: Val) -> Option<&Value> {
        match self.values.get(&k) {
            Some(v) => Some(v),
            None => self.parent.map(|p| p.get(k)).unwrap_or_default(),
        }
    }
}

#[derive(Debug)]
struct ProcCtx<'a> {
    proc_idx: ProcIdx,
    expr: ExprIdx,
    inside_handler: Option<HandlerIdx>,
    scope: Scope<'a>,
    handler_defs: Rc<[(ExprIdx, HandlerIdx)]>,
}

impl<'a> ProcCtx<'a> {
    fn with_expr(&mut self, expr: ExprIdx) -> &mut Self {
        self.expr = expr;
        self
    }
    fn child<T>(
        &'a self,
        expr: ExprIdx,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (HashMap<Val, Value>, T) {
        let mut child = Self {
            proc_idx: self.proc_idx,
            expr,
            inside_handler: self.inside_handler,
            scope: Scope {
                parent: Some(&self.scope),
                values: HashMap::new(),
            },
            handler_defs: self.handler_defs.clone(),
        };

        let t = f(&mut child);

        let mut values = child.scope.values;
        values.retain(|k, _| self.scope.values.contains_key(k));
        (values, t)
    }
}
type ProcTodo = Vec<ProcCtx<'static>>;

fn define_function(
    ir: &mut IRContext,
    fun: Either<Val, (HandlerIdx, EffFunIdx)>,
    debug_name: String,
    inputs: Vec<Reg>,
    output: TypeIdx,
    instructions: Vec<Instruction>,
) {
    let proc = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs,
            captures: None,
            output,
            debug_name,
            unhandled: Vec::new(),
            handled: Vec::new(),
            redirect: Vec::new(),
        },
    );
    ir.ir.proc_impl.push_value(ProcImpl {
        blocks: vec![Block {
            instructions,
            next: None,
        }]
        .into(),
    });
    ir.proc_map.insert(
        ProcIdent {
            fun,
            handlers: Vec::new(),
            handler_params: Vec::new(),
        },
        proc,
    );
}

pub fn generate_ir(ctx: &Parsed, asys: &Analysis) -> IR {
    let mut ir = IRContext {
        proc_map: HashMap::new(),
        handlers: VecMap::new(),
        implied_handlers: HashMap::new(),
        parsed: ctx,
        asys,
        ir: IR {
            proc_sign: VecMap::new(),
            proc_impl: VecMap::new(),
            main: ProcIdx(0),

            regs: VecMap::new(),
            globals: VecMap::new(),
            aggregates: VecMap::new(),

            handler_type: VecMap::new(),
            types: VecSet::new(),
        },
    };
    ir.insert_type(Type::Never);
    ir.insert_type(Type::None);

    let byte = ir.insert_type(Type::Int8);
    let byteptr = ir.insert_type(Type::Pointer(byte));
    let arrsize = ir.insert_type(Type::IntSize);

    ir.ir.aggregates.push_value(AggregateType {
        children: vec![byteptr, arrsize],
        debug_name: "str".into(),
    });
    ir.insert_type(Type::Slice(byte));
    ir.insert_type(Type::Int);
    ir.insert_type(Type::Bool);

    // define debug
    let debug_effect = get_effect(ctx, ctx.preamble, "debug");
    let debug = ir.handlers.push(
        HandlerIdx,
        HandlerCtx {
            effect: asys.values[debug_effect.name],
            global: None,
            definition: None,
            captures: Vec::new(),
        },
    );
    ir.ir.handler_type.push_value(HandlerType {
        captures: Vec::new(),
        break_ty: TYPE_NEVER,
    });

    let input = ir.next_reg(TYPE_INT);
    define_function(
        &mut ir,
        Either::Right((debug, EffFunIdx(0))),
        "putint".into(),
        vec![input],
        TYPE_NONE,
        vec![Instruction::PrintNum(input), Instruction::Return(None)],
    );

    let input = ir.next_reg(TYPE_STR_SLICE);
    define_function(
        &mut ir,
        Either::Right((debug, EffFunIdx(1))),
        "putstr".into(),
        vec![input],
        TYPE_NONE,
        vec![Instruction::PrintStr(input), Instruction::Return(None)],
    );

    // define system effect
    let sys_effect = get_effect(ctx, ctx.system, "sys");
    let sys = ir.handlers.push(
        HandlerIdx,
        HandlerCtx {
            effect: asys.values[sys_effect.name],
            global: None,
            definition: None,
            captures: Vec::new(),
        },
    );
    ir.ir.handler_type.push_value(HandlerType {
        captures: Vec::new(),
        break_ty: TYPE_NEVER,
    });

    // TODO: this is only for unix
    for n in 0..=6 {
        let nr = ir.next_reg(TYPE_INT);
        let inputs = (0..n).map(|_| ir.next_reg(TYPE_INT)).collect::<Vec<_>>();
        let output = ir.next_reg(TYPE_INT);

        define_function(
            &mut ir,
            Either::Right((sys, EffFunIdx(n))),
            format!("syscall{}", n),
            std::iter::once(nr).chain(inputs.iter().copied()).collect(),
            TYPE_INT,
            vec![
                Instruction::Syscall(Some(output), nr, inputs),
                Instruction::Return(Some(output)),
            ],
        );
    }

    // define unreachable
    // TODO: differ depending on settings
    let unreachable_fun = get_function(ctx, ctx.preamble, "unreachable");
    define_function(
        &mut ir,
        Either::Left(asys.values[unreachable_fun.decl.name]),
        "unreachable".into(),
        vec![],
        TYPE_NEVER,
        vec![Instruction::Unreachable],
    );

    // define panic
    // TODO: location
    let panic_fun = get_function(ctx, ctx.preamble, "panic");
    let input = ir.next_reg(TYPE_STR_SLICE);

    let prefix = ir.next_reg(TYPE_STR_SLICE);
    let suffix = ir.next_reg(TYPE_STR_SLICE);
    define_function(
        &mut ir,
        Either::Left(asys.values[panic_fun.decl.name]),
        "panic".into(),
        vec![input],
        TYPE_NEVER,
        vec![
            Instruction::InitString(prefix, "panic: ".into()),
            Instruction::InitString(suffix, "\n".into()),
            Instruction::PrintStr(prefix),
            Instruction::PrintStr(input),
            Instruction::PrintStr(suffix),
            Instruction::Exit(1),
            Instruction::Unreachable,
        ],
    );

    // define len
    let len_fun = get_function(ctx, ctx.preamble, "len");
    let input = ir.next_reg(TYPE_STR_SLICE);
    let output = ir.next_reg(arrsize);
    define_function(
        &mut ir,
        Either::Left(asys.values[len_fun.decl.name]),
        "len".into(),
        vec![input],
        arrsize,
        vec![
            Instruction::Member(output, input, 1),
            Instruction::Return(Some(output)),
        ],
    );

    // generate main signature
    let main = asys.main.expect("no main function");
    let fun = &ir.parsed.functions[main];
    let val = ir.asys.values[fun.decl.name];
    let mut proc_todo = Vec::new();

    ir.ir.main = generate_proc_sign(
        &mut ir,
        Some(Either::Left(val)),
        Cow::Borrowed(&[debug, sys]),
        &[],
        &Vec::new(),
        analyzer::TYPE_NONE,
        "main".into(),
        fun.body,
        None,
        &mut proc_todo,
    );

    // generate implied handlers
    for expr in ctx
        .packages
        .values()
        .flat_map(|p| p.implied.iter())
        .copied()
    {
        let ast_handler = match &ir.parsed.exprs[expr].0 {
            Expression::Handler(ast_handler) => ast_handler,
            _ => unreachable!(),
        };

        let break_type = match ir.asys.types[ir.asys.exprs[expr]] {
            analyzer::Type::Handler(_, t, _) => TypeIdx::from_type(&mut ir, t),
            _ => unreachable!(),
        };

        // get effect
        let eff_ident = ast_handler.effect.effect;
        let eff_val = ir.asys.values[eff_ident];

        let handler_idx = ir.new_handler(eff_val, false, break_type, expr, &Scope::default());

        // add handler to implied
        ir.implied_handlers.insert(eff_val, handler_idx);
    }

    // generate
    while !proc_todo.is_empty() {
        let ctx = proc_todo.remove(0);
        let proc = generate_proc_impl(&mut ir, ctx, &mut proc_todo);
        ir.ir.proc_impl.push_value(proc);
    }

    // bubble up unhandled
    let mut done = false;
    while !done {
        done = true;
        for callee in ir.ir.proc_sign.keys(ProcIdx) {
            for called in ir.ir.proc_impl[callee].calls() {
                if let Some((callee, called)) = ir.ir.proc_sign.get_mut2(callee, called) {
                    for handler in called.unhandled.iter().cloned() {
                        let handler = callee
                            .redirect
                            .iter()
                            .copied()
                            .find(|&(clone, _)| clone == handler)
                            .map(|(_, original)| original)
                            .unwrap_or(handler);
                        if !callee.handled.contains(&handler)
                            && !callee.unhandled.contains(&handler)
                        {
                            callee.unhandled.push(handler);
                            done = false;
                        }
                    }
                }
            }
        }
    }

    // return ir
    ir.ir
}

fn get_effect<'a>(ctx: &'a Parsed, package: PackageIdx, name: &str) -> &'a parser::Effect {
    ctx.packages[package]
        .effects
        .iter()
        .copied()
        .map(|i| &ctx.effects[i])
        .find(|e| ctx.idents[e.name].0.eq(name))
        .unwrap()
}

fn get_function<'a>(ctx: &'a Parsed, package: PackageIdx, name: &str) -> &'a parser::Function {
    ctx.packages[package]
        .functions
        .iter()
        .copied()
        .map(|i| &ctx.functions[i])
        .find(|f| ctx.idents[f.decl.name].0.eq(name))
        .unwrap()
}

fn get_proc(
    ir: &mut IRContext,
    val: Val,
    proc_idx: ProcIdx,
    scope: &Scope,
    param_types: Box<[TypeIdx]>,
    reg_args: Option<&mut Vec<Value>>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    match ir.asys.defs[val] {
        Definition::EffectFunction(eff_idx, eff_fun_idx, _) => {
            // get handler
            let eff_val = ir.asys.values[ir.parsed.effects[eff_idx].name];
            let handler_val = ir.get_in_scope(eff_val, scope);
            let handler_idx = match ir.ir.types[handler_val.get_type(&ir.ir)] {
                Type::NakedHandler(handler_idx) => {
                    let proc = &mut ir.ir.proc_sign[proc_idx];
                    if !proc.handled.contains(&handler_idx) {
                        proc.handled.push(handler_idx);
                    }
                    handler_idx
                }
                Type::Handler(handler_idx) => handler_idx,
                _ => panic!(),
            };

            // get closure
            if let Some(reg_args) = reg_args {
                if let Some(reg) = handler_val.non_global().cloned() {
                    reg_args.push(reg);
                }
                get_handler_proc(
                    ir,
                    handler_idx,
                    eff_fun_idx,
                    proc_idx,
                    scope,
                    param_types,
                    Some(reg_args),
                    proc_todo,
                )
            } else {
                get_handler_proc(
                    ir,
                    handler_idx,
                    eff_fun_idx,
                    proc_idx,
                    scope,
                    param_types,
                    None,
                    proc_todo,
                )
            }
        }
        Definition::Function(func_idx, _) => {
            // create proc identity
            let fun = &ir.parsed.functions[func_idx];

            let effects = fun
                .decl
                .sign
                .effects
                .iter()
                .map(|&e| {
                    let effect = ir.asys.values[e.effect];
                    let handler_val = ir.get_in_scope(effect, scope);
                    let handler_idx = match ir.ir.types[handler_val.get_type(&ir.ir)] {
                        Type::NakedHandler(handler_idx) => {
                            let proc = &mut ir.ir.proc_sign[proc_idx];
                            if !proc.handled.contains(&handler_idx) {
                                proc.handled.push(handler_idx);
                            }
                            handler_idx
                        }
                        Type::Handler(handler_idx) => handler_idx,
                        _ => panic!(),
                    };
                    handler_idx
                })
                .collect();

            let procident = ProcIdent {
                fun: Either::Left(val),
                handlers: effects,
                handler_params: param_types
                    .iter()
                    .copied()
                    .filter(|t| t.is_handler(ir))
                    .collect(),
            };

            if let Some(reg_args) = reg_args {
                reg_args.extend(procident.handlers.iter().filter_map(|&idx| {
                    scope
                        .get(ir.handlers[idx].effect)
                        .unwrap()
                        .non_global()
                        .cloned()
                }));
            }

            // get proc
            if !ir.proc_map.contains_key(&procident) {
                let handlers = &procident.handlers;

                // get params
                let params = fun
                    .decl
                    .sign
                    .inputs
                    .values()
                    .map(|param| ir.asys.values[param.name])
                    .zip(param_types.iter().copied())
                    .map(|(a, b)| (a, b, false))
                    .collect::<Vec<_>>();

                let output = TypeIdx::from_function(ir, val);

                // generate debug name
                let mut debug_name = ir.parsed.idents[fun.decl.name].0.clone();

                if handlers.len() > 0 {
                    debug_name += ".";

                    for &handler in handlers.iter() {
                        let eff_val = ir.handlers[handler].effect;
                        let eff_name = ir
                            .parsed
                            .effects
                            .values()
                            .find(|e| ir.asys.values[e.name] == eff_val)
                            .map(|e| ir.parsed.idents[e.name].0.as_str())
                            .unwrap_or("debug");

                        debug_name += eff_name;
                        debug_name += ".";
                        debug_name += usize::from(handler).to_string().as_str();
                        debug_name += ".";
                    }

                    debug_name.pop();
                }

                // generate func
                generate_proc_sign(
                    ir,
                    Some(procident.fun),
                    Cow::Owned(procident.handlers),
                    &[],
                    &params,
                    output,
                    debug_name,
                    fun.body,
                    None,
                    proc_todo,
                )
            } else {
                ir.proc_map[&procident]
            }
        }
        _ => todo!(),
    }
}

fn get_handler_proc(
    ir: &mut IRContext,
    handler_idx: HandlerIdx,
    eff_fun_idx: EffFunIdx,
    proc_idx: ProcIdx,
    scope: &Scope,
    param_types: Box<[TypeIdx]>,
    reg_args: Option<&mut Vec<Value>>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    let def = ir.handlers[handler_idx].definition;

    let eff_val = ir.handlers[handler_idx].effect;
    let effects = match ir.asys.defs[eff_val] {
        Definition::Effect(eff_idx) => {
            let decl = &ir.parsed.effects[eff_idx].functions[eff_fun_idx];
            decl.sign
                .effects
                .iter()
                .map(|&e| {
                    let effect = ir.asys.values[e.effect];
                    let handler_val = ir.get_in_scope(effect, scope);
                    let handler_idx = match ir.ir.types[handler_val.get_type(&ir.ir)] {
                        Type::NakedHandler(handler_idx) => {
                            let proc = &mut ir.ir.proc_sign[proc_idx];
                            if !proc.handled.contains(&handler_idx) {
                                proc.handled.push(handler_idx);
                            }
                            handler_idx
                        }
                        Type::Handler(handler_idx) => handler_idx,
                        _ => panic!(),
                    };
                    handler_idx
                })
                .collect()
        }
        _ => unreachable!(),
    };

    let procident = ProcIdent {
        fun: Either::Right((handler_idx, eff_fun_idx)),
        handlers: effects,
        handler_params: param_types
            .iter()
            .copied()
            .filter(|t| t.is_handler(ir))
            .collect(),
    };

    if let Some(reg_args) = reg_args {
        reg_args.extend(procident.handlers.iter().filter_map(|&idx| {
            scope
                .get(ir.handlers[idx].effect)
                .unwrap()
                .non_global()
                .cloned()
        }));
    }

    // get proc
    if !ir.proc_map.contains_key(&procident) {
        let handlers = &procident.handlers;
        let effect = match ir.asys.defs[eff_val] {
            Definition::Effect(idx) => &ir.parsed.effects[idx],
            _ => unreachable!(),
        };
        let val = ir.asys.values[effect.functions[eff_fun_idx].name];
        let ast_handler = match &ir.parsed.exprs[def.unwrap()].0 {
            Expression::Handler(handler) => handler,
            _ => unreachable!(),
        };

        let fun = ast_handler
            .functions
            .iter()
            .find(|f| ir.asys.values[f.decl.name] == val)
            .unwrap();

        // get params
        let params = fun
            .decl
            .sign
            .inputs
            .values()
            .map(|param| ir.asys.values[param.name])
            .zip(param_types.iter().copied())
            .map(|(a, b)| (a, b, false))
            .collect::<Vec<_>>();

        let output = TypeIdx::from_function(ir, val);

        // generate debug name
        let eff_name = ir.parsed.idents[effect.name].0.as_str();
        let proc_name = ir.parsed.idents[effect.functions[eff_fun_idx].name]
            .0
            .as_str();
        let mut debug_name = format!("{}.{}.{}", proc_name, eff_name, usize::from(handler_idx));

        if handlers.len() > 0 {
            debug_name += ".";

            for &handler in handlers.iter() {
                let eff_val = ir.handlers[handler].effect;
                let eff_name = ir
                    .parsed
                    .effects
                    .values()
                    .find(|e| ir.asys.values[e.name] == eff_val)
                    .map(|e| ir.parsed.idents[e.name].0.as_str())
                    .unwrap_or("debug");

                debug_name += eff_name;
                debug_name += ".";
                debug_name += usize::from(handler).to_string().as_str();
                debug_name += ".";
            }

            debug_name.pop();
        }

        // generate handler proc
        generate_proc_sign(
            ir,
            Some(procident.fun),
            Cow::Owned(procident.handlers),
            &[],
            &params,
            output,
            debug_name,
            fun.body,
            Some(handler_idx),
            proc_todo,
        )
    } else {
        ir.proc_map[&procident]
    }
}

fn generate_proc_sign(
    ir: &mut IRContext,
    ident: Option<Either<Val, (HandlerIdx, EffFunIdx)>>,
    unhandled: Cow<[HandlerIdx]>,
    handled: &[HandlerIdx],
    params: &[(Val, TypeIdx, bool)],
    output: analyzer::TypeIdx,
    debug_name: String,
    body: ExprIdx,
    inside_handler: Option<HandlerIdx>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    // get inputs
    let mut inputs = Vec::new();
    let mut scope = Scope::default();
    for (val, ty, reference) in params.iter().copied() {
        let reg = ir.next_reg(ty);
        if reference {
            scope.insert(val, Value::Reference(reg));
        } else {
            scope.insert(val, Value::Value(reg, Some(val)));
        }
        inputs.push(reg);
    }

    for idx in unhandled.iter().copied().chain(handled.iter().copied()) {
        let handler = &ir.handlers[idx];
        let global = handler.global;
        let effect = handler.effect;

        match global {
            Some(glob) => {
                scope.insert(effect, Value::Global(glob));
            }
            None => {
                let ty = ir.insert_type(Type::Handler(idx));
                let reg = ir.next_reg(ty);
                inputs.push(reg);
                scope.insert(effect, Value::Value(reg, None));
            }
        }
    }

    let captures = if let Some(idx) = inside_handler {
        let handler = &ir.handlers[idx];
        let global = handler.global;
        let effect = handler.effect;

        let mut members = Vec::new();
        for (val, ty, reference) in handler.captures.iter().copied() {
            scope.insert(
                val,
                if reference {
                    let reg = ir.ir.regs.push(Reg, ty);
                    members.push(reg);
                    Value::Reference(reg)
                } else {
                    let reg = ir.ir.regs.push(Reg, ty);
                    members.push(reg);
                    Value::Value(reg, None)
                },
            );
        }

        Some(Captures {
            input: match global {
                Some(glob) => {
                    scope.insert(effect, Value::Global(glob));
                    Value::Global(glob)
                }
                None => {
                    let ty = ir.insert_type(Type::Handler(idx));
                    let reg = ir.next_reg(ty);
                    inputs.push(reg);
                    scope.insert(effect, Value::Value(reg, None));
                    Value::Value(reg, None)
                }
            },
            members,
        })
    } else {
        None
    };

    // create handlers
    let mut handler_defs = Vec::new();
    ir.parsed.for_each(body, false, false, &mut |expr| {
        if let Expression::Handler(h) = &ir.parsed.exprs[expr].0 {
            // get break type
            let break_type = match ir.asys.types[ir.asys.exprs[expr]] {
                analyzer::Type::Handler(_, t, _) => TypeIdx::from_type(ir, t),
                _ => unreachable!(),
            };

            // create handler
            let handler = ir.new_handler(
                ir.asys.values[h.effect.effect],
                false,
                break_type,
                expr,
                &scope,
            );

            handler_defs.push((expr, handler));
        }
    });

    // create signature
    let out = TypeIdx::from_return_type(ir, output);
    let proc_idx = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output: out,
            debug_name,
            captures,
            unhandled: inside_handler
                .iter()
                .copied()
                .filter(|_| ir.parsed.yeets(body))
                .collect(),
            handled: handled
                .iter()
                .copied()
                .filter(|&h| !ir.ir.handler_type[h].break_ty.is_never())
                .collect(),
            redirect: Vec::new(),
        },
    );

    // add procident if this is a function
    if let Some(fun) = ident {
        ir.proc_map.insert(
            ProcIdent {
                fun,
                handlers: unhandled.into_owned(),
                handler_params: params
                    .iter()
                    .copied()
                    .filter_map(|(_, t, _)| if t.is_handler(ir) { Some(t) } else { None })
                    .collect(),
            },
            proc_idx,
        );
    }

    let handler_defs = Rc::from(handler_defs);
    proc_todo.push(ProcCtx {
        proc_idx,
        expr: body,
        inside_handler,
        scope: Scope {
            parent: None,
            values: scope.values.clone(),
        },
        handler_defs: Rc::clone(&handler_defs),
    });

    // get output
    if let analyzer::Type::Handler(effect, _, def) = ir.asys.types[output] {
        let handler = handler_type(ir, effect, def, proc_idx, &handler_defs, &scope, proc_todo);
        ir.ir.proc_sign[proc_idx].output = handler;
    }

    proc_idx
}

fn handler_type(
    ir: &mut IRContext,
    effect: Val,
    def: Option<analyzer::HandlerIdx>,
    proc_idx: ProcIdx,
    defs: &[(ExprIdx, HandlerIdx)],
    scope: &Scope,
    proc_todo: &mut ProcTodo,
) -> TypeIdx {
    match ir.asys.handlers[def.expect("function return handler type not filled in")] {
        analyzer::HandlerDef::Handler(expr, _) => {
            let handler_idx = defs
                .iter()
                .find(|&&(e, _)| expr == e)
                .expect("function returns handler not defined by self")
                .1;
            let mems = ir.handlers[handler_idx]
                .captures
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(i, (val, _, reference))| {
                    // it is a reference at was not given as a parameter
                    if reference && scope.get(val).is_none() {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect::<Rc<_>>();
            if mems.is_empty() {
                ir.insert_type(Type::NakedHandler(handler_idx))
            } else {
                ir.insert_type(Type::RawHandler(handler_idx, mems))
            }
        }
        analyzer::HandlerDef::Call(fun, ref exprs) => {
            let param_types = exprs
                .iter()
                .copied()
                .map(|expr| match ir.asys.types[ir.asys.exprs[expr]] {
                    analyzer::Type::Handler(effect, _, def) => {
                        // recursive call!
                        handler_type(ir, effect, def, proc_idx, defs, scope, proc_todo)
                    }
                    _ => TypeIdx::from_type(ir, ir.asys.exprs[expr]),
                })
                .collect();

            // recursive call!
            let proc = get_proc(ir, fun, proc_idx, &scope, param_types, None, proc_todo);
            ir.ir.proc_sign[proc].output
        }
        analyzer::HandlerDef::Param(p) => {
            ir.ir.regs[ir.ir.proc_sign[proc_idx].inputs[usize::from(p)]]
        }
        analyzer::HandlerDef::Signature => ir.get_in_scope(effect, scope).get_type(&ir.ir),
        analyzer::HandlerDef::Error => unreachable!(),
    }
}

fn generate_proc_impl(ir: &mut IRContext, mut ctx: ProcCtx, proc_todo: &mut ProcTodo) -> ProcImpl {
    let mut blocks = VecMap::new();
    let start = blocks.push(BlockIdx, Block::default());

    let mut end = start;
    let ret = generate_expr(ir, &mut ctx, &mut blocks, &mut end, proc_todo);

    if let Ok(ret) = ret {
        if !matches!(
            blocks[end].instructions.last(),
            Some(Instruction::Return(_) | Instruction::Yeet(_, _))
        ) {
            // add return if we haven't already
            let ret = ret.map(|ret| {
                let r = ret.value(ir, &mut blocks[end]);
                let output = ir.ir.proc_sign[ctx.proc_idx].output;

                // create raw handler if required
                if let Type::RawHandler(_, _) = ir.ir.types[output] {
                    let raw = ir.next_reg(output);
                    blocks[end]
                        .instructions
                        .push(Instruction::RawHandler(raw, r));
                    raw
                } else {
                    r
                }
            });
            blocks[end].instructions.push(Instruction::Return(ret));
        }
    }

    ProcImpl { blocks }
}

#[derive(Clone, Copy)]
struct Never;
type ExprResult = Result<Option<Value>, Never>;

fn get_captures(
    ir: &mut IRContext,
    scope: &mut Scope,
    block: &mut Block,
    expr: ExprIdx,
    exception: Option<Val>,
) -> Vec<(Val, Reg, bool)> {
    let mut captures = Vec::new();
    ir.parsed.for_each(expr, true, false, &mut |expr| {
        if let Expression::Ident(i) = ir.parsed.exprs[expr].0 {
            let val = ir.asys.values[i];

            // capture effects from (effect) functions
            let vals = match ir.asys.defs[val] {
                Definition::EffectFunction(eff_idx, eff_fun_idx, _) => {
                    let eff_val = ir.asys.values[ir.parsed.effects[eff_idx].name];
                    match ir.asys.defs[eff_val] {
                        Definition::Effect(eff_idx) => {
                            let iter = ir.parsed.effects[eff_idx].functions[eff_fun_idx]
                                .sign
                                .effects
                                .iter()
                                .copied()
                                .filter_map(|i| {
                                    let effect = ir.asys.values[i.effect];
                                    if Some(effect) == exception {
                                        None
                                    } else {
                                        Some((effect, false))
                                    }
                                });

                            if Some(eff_val) == exception {
                                iter.collect()
                            } else {
                                std::iter::once((eff_val, false)).chain(iter).collect()
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                Definition::Function(fun, _) => ir.parsed.functions[fun]
                    .decl
                    .sign
                    .effects
                    .iter()
                    .copied()
                    .filter_map(|i| {
                        let effect = ir.asys.values[i.effect];
                        if Some(effect) == exception {
                            None
                        } else {
                            Some((effect, false))
                        }
                    })
                    .collect(),
                Definition::Parameter(_, mutable, _, _) => {
                    if Some(val) == exception {
                        vec![]
                    } else {
                        vec![(val, mutable)]
                    }
                }
                Definition::Variable(mutable, _, _) => {
                    if Some(val) == exception {
                        vec![]
                    } else {
                        vec![(val, mutable)]
                    }
                }
                Definition::Effect(_) => {
                    if Some(val) == exception {
                        vec![]
                    } else {
                        vec![(val, false)]
                    }
                }
                Definition::BuiltinType(_) => vec![],
                Definition::Package(_) => vec![],
            };

            // capture vals
            for (val, mutable) in vals {
                if let Some(e) = scope.get(val).cloned() {
                    if !captures.iter().any(|&(v, _, _)| v == val) {
                        if mutable {
                            let reg = e.reference(ir, scope, block);
                            captures.push((val, reg, true));
                        } else {
                            let reg = e.value(ir, block);
                            captures.push((val, reg, false));
                        }
                    }
                }
            }
        }
    });
    captures
}

fn generate_expr(
    ir: &mut IRContext,
    ctx: &mut ProcCtx,
    blocks: &mut VecMap<BlockIdx, Block>,
    block: &mut BlockIdx,
    proc_todo: &mut ProcTodo,
) -> ExprResult {
    use Expression as E;
    match ir.parsed.exprs[ctx.expr].0 {
        E::Body(ref body) => {
            for &expr in body.main.iter() {
                generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo)?;
            }
            body.last
                .map(|expr| generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo))
                .unwrap_or(Ok(None))
        }
        E::Let(_, name, _, expr) => {
            let val = ir.asys.values[name];
            let reg = generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo)?
                .expect("let value does not return a value")
                .value(ir, &mut blocks[*block]);
            ctx.scope.insert(val, Value::Value(reg, Some(val)));
            Ok(None)
        }
        E::Call(func, ref args) => {
            // get base registers
            let mut reg_args = args
                .iter()
                .map(|&expr| {
                    generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo)
                        .map(|r| r.expect("call argument does not return a value"))
                })
                .collect::<Result<Vec<_>, _>>()?;

            // TODO: currently we assume func is an Ident expr or Effect Member expr
            let res = match ir.parsed.exprs[func].0 {
                E::Member(handler, id) => {
                    let val = ir.asys.values[id];
                    match ir.asys.types[ir.asys.exprs[handler]] {
                        analyzer::Type::PackageLiteral(_) => {
                            // function of package
                            let proc_idx = get_proc(
                                ir,
                                val,
                                ctx.proc_idx,
                                &ctx.scope,
                                reg_args.iter().map(|r| r.get_type(&ir.ir)).collect(),
                                Some(&mut reg_args),
                                proc_todo,
                            );

                            let output = ir.ir.proc_sign[proc_idx].output.into_result(ir);

                            // execute function
                            let collect = reg_args
                                .into_iter()
                                .map(|r| r.value(ir, &mut blocks[*block]))
                                .collect();
                            blocks[*block].instructions.push(Instruction::Call(
                                proc_idx,
                                output.clone().unwrap_or(None).map(|v| v.register()),
                                collect,
                            ));

                            if ir.ir.proc_sign[proc_idx].output.is_never() {
                                blocks[*block].instructions.push(Instruction::Unreachable);
                            }
                            output
                        }
                        analyzer::Type::Handler(_, _, _) => {
                            // function of handler
                            let handler_reg = generate_expr(
                                ir,
                                ctx.with_expr(handler),
                                blocks,
                                block,
                                proc_todo,
                            )?
                            .expect("member parent does not return a value");

                            let ty = &ir.ir.types[handler_reg.get_type(&ir.ir)];
                            match ty {
                                &Type::NakedHandler(handler_idx) | &Type::Handler(handler_idx) => {
                                    // add naked handler to handled
                                    if matches!(ty, Type::NakedHandler(_)) {
                                        let proc = &mut ir.ir.proc_sign[ctx.proc_idx];
                                        if !proc.handled.contains(&handler_idx) {
                                            proc.handled.push(handler_idx);
                                        }
                                    }

                                    let handler = &ir.handlers[handler_idx];
                                    let global = handler.global;

                                    // get output
                                    let eff_fun_idx = match ir.asys.defs[val] {
                                        Definition::EffectFunction(_, eff_fun_idx, _) => {
                                            eff_fun_idx
                                        }
                                        _ => panic!(),
                                    };
                                    let proc_idx = get_handler_proc(
                                        ir,
                                        handler_idx,
                                        eff_fun_idx,
                                        ctx.proc_idx,
                                        &ctx.scope,
                                        reg_args.iter().map(|r| r.get_type(&ir.ir)).collect(),
                                        Some(&mut reg_args),
                                        proc_todo,
                                    );
                                    let output = ir.ir.proc_sign[proc_idx].output.into_result(ir);

                                    // execute handler
                                    match global {
                                        Some(glob) => {
                                            let next = blocks.push(BlockIdx, Block::default());

                                            let v = handler_reg.value(ir, &mut blocks[*block]);
                                            blocks[*block]
                                                .instructions
                                                .push(Instruction::SetScopedGlobal(glob, v, next));

                                            let collect = reg_args
                                                .into_iter()
                                                .map(|r| r.value(ir, &mut blocks[*block]))
                                                .collect();
                                            blocks[*block].instructions.push(Instruction::Call(
                                                proc_idx,
                                                output
                                                    .clone()
                                                    .unwrap_or(None)
                                                    .map(|v| v.register()),
                                                collect,
                                            ));

                                            blocks[*block].next = Some(next);
                                            *block = next;
                                        }
                                        None => {
                                            reg_args.push(handler_reg);

                                            let collect = reg_args
                                                .into_iter()
                                                .map(|r| r.value(ir, &mut blocks[*block]))
                                                .collect();
                                            blocks[*block].instructions.push(Instruction::Call(
                                                proc_idx,
                                                output
                                                    .clone()
                                                    .unwrap_or(None)
                                                    .map(|v| v.register()),
                                                collect,
                                            ));
                                        }
                                    }

                                    if ir.ir.proc_sign[proc_idx].output.is_never() {
                                        blocks[*block].instructions.push(Instruction::Unreachable);
                                    }
                                    output
                                }
                                _ => todo!(),
                            }
                        }
                        _ => todo!(),
                    }
                }
                E::Ident(id) => {
                    // function of current package
                    let val = ir.asys.values[id];
                    let proc_idx = get_proc(
                        ir,
                        val,
                        ctx.proc_idx,
                        &ctx.scope,
                        reg_args.iter().map(|r| r.get_type(&ir.ir)).collect(),
                        Some(&mut reg_args),
                        proc_todo,
                    );

                    let output = ir.ir.proc_sign[proc_idx].output.into_result(ir);

                    // execute function
                    let collect = reg_args
                        .into_iter()
                        .map(|r| r.value(ir, &mut blocks[*block]))
                        .collect();
                    blocks[*block].instructions.push(Instruction::Call(
                        proc_idx,
                        output.clone().unwrap_or(None).map(|v| v.register()),
                        collect,
                    ));

                    if ir.ir.proc_sign[proc_idx].output.is_never() {
                        blocks[*block].instructions.push(Instruction::Unreachable);
                    }
                    output
                }
                _ => todo!(),
            };

            if let Ok(Some(Value::Value(r, _))) = res {
                if let Type::RawHandler(idx, _) = ir.ir.types[ir.ir.regs[r]] {
                    let ty = ir.insert_type(Type::NakedHandler(idx));
                    let unraw = ir.next_reg(ty);
                    blocks[*block]
                        .instructions
                        .push(Instruction::UnrawHandler(unraw, r));
                    Ok(Some(Value::Value(unraw, None)))
                } else {
                    res
                }
            } else {
                res
            }
        }
        E::Member(_, _) => todo!(),
        E::Loop(expr) => {
            let loop_init = blocks.push(BlockIdx, Block::default());
            let loop_start = blocks.push(BlockIdx, Block::default());
            let mut loop_end = loop_start;

            let mut phis = HashMap::new();
            let mut values = HashMap::new();
            let mut optscope = Some(&ctx.scope);
            while let Some(scope) = optscope {
                values.extend(
                    scope
                        .values
                        .iter()
                        .filter_map(|(&val, value)| match *value {
                            Value::Value(r, o) => {
                                let copy = ir.copy_reg(r);
                                phis.insert(val, (r, Value::Value(copy, o)));
                                Some((val, Value::Value(copy, o)))
                            }
                            Value::Reference(r) => {
                                let copy = ir.copy_reg(r);
                                phis.insert(val, (r, Value::Reference(copy)));
                                Some((val, Value::Reference(copy)))
                            }
                            Value::Global(_) => None,
                        }),
                );
                optscope = scope.parent;
            }

            let mut parent = Scope {
                parent: Some(&ctx.scope),
                values,
            };
            let mut child = ProcCtx {
                proc_idx: ctx.proc_idx,
                expr,
                inside_handler: ctx.inside_handler,
                scope: Scope {
                    parent: Some(&parent),
                    values: HashMap::new(),
                },
                handler_defs: Rc::clone(&ctx.handler_defs),
            };
            let _ = generate_expr(ir, &mut child, blocks, &mut loop_end, proc_todo);

            blocks[*block].next = Some(loop_init);
            blocks[loop_init].next = Some(loop_start);
            blocks[loop_end].next = Some(loop_init);

            // add phi instructions for changed values
            for (r, value) in child.scope.values.into_iter() {
                if let Some((original, copy)) = phis.remove(&r) {
                    match copy {
                        Value::Value(copy, _) => {
                            let new = value.value(ir, &mut blocks[loop_end]);
                            blocks[loop_init].instructions.push(Instruction::Phi(
                                copy,
                                vec![(original, *block), (new, loop_end)],
                            ));
                        }
                        Value::Reference(copy) => {
                            let new = value.reference(ir, &mut parent, &mut blocks[loop_end]);
                            blocks[loop_init].instructions.push(Instruction::Phi(
                                copy,
                                vec![(original, *block), (new, loop_end)],
                            ));
                        }
                        Value::Global(_) => unreachable!(),
                    }
                }
            }

            // remaining are just copies
            for (original, copy) in phis.into_values() {
                match copy {
                    Value::Value(copy, _) => {
                        blocks[loop_init]
                            .instructions
                            .push(Instruction::Copy(copy, original));
                    }
                    Value::Reference(copy) => {
                        blocks[loop_init]
                            .instructions
                            .push(Instruction::Copy(copy, original));
                    }
                    Value::Global(_) => unreachable!(),
                }
            }

            Err(Never)
        }
        E::IfElse(cond, yes, no) => {
            let cond = generate_expr(ir, ctx.with_expr(cond), blocks, block, proc_todo)?
                .expect("condition has no value")
                .value(ir, &mut blocks[*block]);

            match no {
                Some(no) => {
                    let no_start = blocks.push(BlockIdx, Block::default());

                    let mut no_end = no_start;
                    let (no_changed, no_reg) = ctx.child(no, |child| {
                        generate_expr(ir, child, blocks, &mut no_end, proc_todo)
                    });

                    let yes_start = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, no_start));

                    let mut yes_end = yes_start;
                    let (yes_changed, yes_reg) = ctx.child(yes, |child| {
                        generate_expr(ir, child, blocks, &mut yes_end, proc_todo)
                    });

                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block].next = Some(no_start);
                    blocks[yes_end].next = Some(end);
                    blocks[no_end].next = Some(end);

                    // add phi instructions for changed values
                    generate_phi(
                        ir,
                        blocks,
                        end,
                        &mut ctx.scope,
                        &[
                            Path {
                                changed: yes_changed,
                                block_end: yes_end,
                            },
                            Path {
                                changed: no_changed,
                                block_end: no_end,
                            },
                        ],
                    );
                    *block = end;

                    match (yes_reg, no_reg) {
                        (Ok(Some(yes)), Ok(Some(no))) => {
                            let yes = yes.value(ir, &mut blocks[yes_end]);
                            let no = no.value(ir, &mut blocks[no_end]);
                            if ir.ir.regs[yes] == ir.ir.regs[no] {
                                let out = ir.copy_reg(yes);
                                blocks[*block].instructions.push(Instruction::Phi(
                                    out,
                                    vec![(yes, yes_end), (no, no_end)],
                                ));
                                Ok(Some(Value::Value(out, None)))
                            } else {
                                Ok(None)
                            }
                        }
                        (Err(Never), Err(Never)) => Err(Never),
                        (Err(Never), Ok(Some(no))) => Ok(Some(no)),
                        (Ok(Some(yes)), Err(Never)) => Ok(Some(yes)),
                        _ => Ok(None),
                    }
                }
                None => {
                    let yes_start = blocks.push(BlockIdx, Block::default());
                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, end));

                    let mut yes_end = yes_start;
                    let (yes_changed, _) = ctx.child(yes, |child| {
                        generate_expr(ir, child, blocks, &mut yes_end, proc_todo)
                    });

                    blocks[*block].next = Some(end);
                    blocks[yes_end].next = Some(end);

                    // add phi instructions for changed values
                    generate_phi(
                        ir,
                        blocks,
                        end,
                        &mut ctx.scope,
                        &[
                            Path {
                                changed: yes_changed,
                                block_end: yes_end,
                            },
                            Path {
                                changed: HashMap::new(),
                                block_end: *block,
                            },
                        ],
                    );
                    *block = end;

                    Ok(None)
                }
            }
        }
        E::UnOp(uexpr, op) => match op {
            UnOp::PostIncrement => {
                let left = generate_expr(ir, ctx.with_expr(uexpr), blocks, block, proc_todo)?
                    .expect("operand has no value");

                let value = left.value(ir, &mut blocks[*block]);
                let one = ir.copy_reg(value);
                let incremented = ir.copy_reg(value);
                blocks[*block].instructions.push(Instruction::Init(one, 1));
                blocks[*block]
                    .instructions
                    .push(Instruction::Add(incremented, value, one));

                match left {
                    Value::Value(_, val) => {
                        ctx.scope.insert(
                            val.expect("left operand not tied to variable"),
                            Value::Value(incremented, val),
                        );
                    }
                    Value::Reference(ptr) => {
                        blocks[*block]
                            .instructions
                            .push(Instruction::Store(ptr, incremented));
                    }
                    Value::Global(_) => unreachable!(),
                }

                Ok(Some(Value::Value(value, None)))
            }
            UnOp::Reference => {
                let ty = TypeIdx::from_expr(ir, ctx.expr);
                let ty = TypeIdx::from_type(ir, ty);

                let right = generate_expr(ir, ctx.with_expr(uexpr), blocks, block, proc_todo)?
                    .expect("operand has no value");
                let right = right.reference(ir, &mut ctx.scope, &mut blocks[*block]);
                let right = Value::Value(right, None).cast(ir, &mut blocks[*block], ty);

                Ok(Some(right))
            }
            UnOp::Cast => {
                let ty = TypeIdx::from_expr(ir, ctx.expr);
                let ty = TypeIdx::from_type(ir, ty);

                let right = generate_expr(ir, ctx.with_expr(uexpr), blocks, block, proc_todo)?
                    .expect("operand has no value");
                let right = right.cast(ir, &mut blocks[*block], ty);

                Ok(Some(right))
            }
        },
        E::BinOp(left, op, right) => match op {
            BinOp::Assign => {
                let left = generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                    .expect("left operand has no value");

                let right = generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                    .expect("right operand has no value")
                    .value(ir, &mut blocks[*block]);

                match left {
                    Value::Value(_, val) => {
                        ctx.scope.insert(
                            val.expect("left operand not tied to variable"),
                            Value::Value(right, val),
                        );
                    }
                    Value::Reference(ptr) => {
                        blocks[*block]
                            .instructions
                            .push(Instruction::Store(ptr, right));
                    }
                    Value::Global(_) => unreachable!(),
                }
                Ok(None)
            }
            BinOp::Index => {
                let array = generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                    .expect("left operand has no value");

                match ir.parsed.exprs[right].0 {
                    E::BinOp(left, BinOp::Range, right) => {
                        // get range
                        let left =
                            generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                                .expect("range left has no value")
                                .value(ir, &mut blocks[*block]);

                        let right =
                            generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                                .expect("range right has no value")
                                .value(ir, &mut blocks[*block]);

                        // get array pointer
                        let ptr = match ir.ir.types[array.get_type(&ir.ir)] {
                            Type::Pointer(_) => array.value(ir, &mut blocks[*block]),
                            Type::ConstArray(_, elem_ty) => {
                                let full_ptr =
                                    array.reference(ir, &mut ctx.scope, &mut blocks[*block]);

                                let ptr_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let ptr = ir.next_reg(ptr_ty);

                                // TODO: should this be elementptr?
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::Cast(ptr, full_ptr));

                                ptr
                            }
                            Type::Slice(elem_ty) => {
                                let slice = array.value(ir, &mut blocks[*block]);

                                let ptr_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let ptr = ir.next_reg(ptr_ty);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::Member(ptr, slice, 0));

                                ptr
                            }
                            _ => unreachable!(),
                        };

                        // get slice start and length
                        let adjacent = ir.copy_reg(ptr);
                        blocks[*block]
                            .instructions
                            .push(Instruction::AdjacentPtr(adjacent, ptr, left));

                        let len = ir.copy_reg(left);
                        blocks[*block]
                            .instructions
                            .push(Instruction::Sub(len, right, left));

                        // create slice
                        let elem_ty = ir.ir.regs[ptr].inner(&ir.ir);
                        let slice_ty = ir.insert_type(Type::Slice(elem_ty));
                        let slice = ir.next_reg(slice_ty);
                        blocks[*block]
                            .instructions
                            .push(Instruction::Aggregate(slice, vec![adjacent, len]));

                        Ok(Some(Value::Value(slice, None)))
                    }
                    _ => {
                        let right =
                            generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                                .expect("right operand has no value")
                                .value(ir, &mut blocks[*block]);

                        match ir.ir.types[array.get_type(&ir.ir)] {
                            Type::Pointer(_) => {
                                let ptr = array.value(ir, &mut blocks[*block]);
                                let adjacent = ir.copy_reg(ptr);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::AdjacentPtr(adjacent, ptr, right));
                                Ok(Some(Value::Reference(adjacent)))
                            }
                            Type::ConstArray(_, elem_ty) => {
                                let ptr = array.reference(ir, &mut ctx.scope, &mut blocks[*block]);
                                let elem_ptr_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let elem_ptr = ir.next_reg(elem_ptr_ty);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::ElementPtr(elem_ptr, ptr, right));
                                Ok(Some(Value::Reference(elem_ptr)))
                            }
                            Type::Slice(elem_ty) => {
                                let slice = array.value(ir, &mut blocks[*block]);

                                let ptr_ty = ir.insert_type(Type::Pointer(elem_ty));
                                let ptr = ir.next_reg(ptr_ty);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::Member(ptr, slice, 0));

                                let adjacent = ir.copy_reg(ptr);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::AdjacentPtr(adjacent, ptr, right));
                                Ok(Some(Value::Reference(adjacent)))
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
            _ => {
                let left = generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                    .expect("left operand has no value")
                    .value(ir, &mut blocks[*block]);

                let right = generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                    .expect("right operand has no value")
                    .value(ir, &mut blocks[*block]);

                let out = ir.next_reg(match op {
                    BinOp::Equals | BinOp::Less | BinOp::Greater => TYPE_BOOL,
                    BinOp::Divide | BinOp::Multiply | BinOp::Subtract | BinOp::Add => {
                        ir.ir.regs[left]
                    }
                    BinOp::Range => unreachable!(),
                    BinOp::Assign | BinOp::Index => unreachable!(),
                });

                let instr = match op {
                    BinOp::Equals => Instruction::Equals(out, left, right),
                    BinOp::Divide => Instruction::Div(out, left, right),
                    BinOp::Multiply => Instruction::Mul(out, left, right),
                    BinOp::Subtract => Instruction::Sub(out, left, right),
                    BinOp::Add => Instruction::Add(out, left, right),
                    BinOp::Less => Instruction::Less(out, left, right),
                    BinOp::Greater => Instruction::Greater(out, left, right),
                    BinOp::Range => unreachable!(),
                    BinOp::Assign | BinOp::Index => unreachable!(),
                };
                blocks[*block].instructions.push(instr);

                Ok(Some(Value::Value(out, None)))
            }
        },
        E::Yeet(value) => {
            // get break value
            let reg = value
                .map(|expr| generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo))
                .unwrap_or(Ok(None))?;

            // TODO: we assume this is top level inside a handler
            let yeet = reg.map(|v| v.value(ir, &mut blocks[*block]));
            blocks[*block]
                .instructions
                .push(Instruction::Yeet(yeet, ctx.inside_handler.unwrap()));

            // break returns any type
            Err(Never)
        }
        E::Handler(_) => {
            // get handler
            let handler_idx = ctx
                .handler_defs
                .iter()
                .find(|&&(e, _)| ctx.expr == e)
                .expect("handler not generated beforehand")
                .1;
            let handler = &ir.handlers[handler_idx];
            let captures = handler
                .definition
                .map(|def| match ir.asys.types[ir.asys.exprs[def]] {
                    analyzer::Type::Handler(_, _, def) => match def.map(|h| &ir.asys.handlers[h]) {
                        Some(analyzer::HandlerDef::Handler(_, captures)) => captures
                            .iter()
                            .map(|c| {
                                let reg = ir.get_in_scope(c.val, &ctx.scope);
                                if c.mutable {
                                    reg.reference(ir, &mut ctx.scope, &mut blocks[*block])
                                } else {
                                    reg.value(ir, &mut blocks[*block])
                                }
                            })
                            .collect(),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                })
                .unwrap_or(Vec::new());

            // create handler closure
            let ty = ir.insert_type(Type::NakedHandler(handler_idx));
            let closure_reg = ir.next_reg(ty);

            blocks[*block]
                .instructions
                .push(Instruction::Handler(closure_reg, captures));

            Ok(Some(Value::Value(closure_reg, None)))
        }
        E::TryWith(body, _, handler) => {
            if let Some(handler) = handler {
                // get handler
                let closure_reg =
                    generate_expr(ir, ctx.with_expr(handler), blocks, block, proc_todo)?
                        .expect("try handler does not return a value");
                let ty = &ir.ir.types[closure_reg.get_type(&ir.ir)];
                let handler_idx = match ty {
                    &Type::NakedHandler(handler_idx) | &Type::Handler(handler_idx) => handler_idx,
                    _ => panic!(),
                };
                let naked = matches!(ty, Type::NakedHandler(_));
                let eff_val = ir.handlers[handler_idx].effect;
                let global = ir.handlers[handler_idx].global;

                // generate reset
                let reset_captures =
                    get_captures(ir, &mut ctx.scope, &mut blocks[*block], body, Some(eff_val));
                let reset_params = reset_captures
                    .iter()
                    .map(|&(v, r, m)| (v, ir.ir.regs[r], m))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.proc_sign[ctx.proc_idx];
                let debug_name = format!(
                    "{}__reset.{}",
                    proc_sign.debug_name,
                    usize::from(handler_idx)
                );

                let handlers = &[handler_idx];
                let (unhandled, handled): (Cow<[HandlerIdx]>, &[HandlerIdx]) = if naked {
                    (Cow::Borrowed(&[]), handlers)
                } else {
                    (Cow::Borrowed(handlers), &[])
                };

                let output = TypeIdx::from_expr(ir, body);
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    unhandled,
                    handled,
                    &reset_params,
                    output,
                    debug_name,
                    body,
                    None,
                    proc_todo,
                );

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r, _)| r).collect();

                // execute proc
                let output = ir.ir.proc_sign[proc_idx].output.into_result(ir);

                match global {
                    Some(glob) => {
                        let next = blocks.push(BlockIdx, Block::default());

                        let v = closure_reg.value(ir, &mut blocks[*block]);
                        blocks[*block]
                            .instructions
                            .push(Instruction::SetScopedGlobal(glob, v, next));

                        blocks[*block].instructions.push(Instruction::Call(
                            proc_idx,
                            output.clone().unwrap_or(None).map(|v| v.register()),
                            input_regs,
                        ));

                        blocks[*block].next = Some(next);
                        *block = next;
                    }
                    None => {
                        let mut input_regs = input_regs;
                        input_regs.push(closure_reg.value(ir, &mut blocks[*block]));

                        blocks[*block].instructions.push(Instruction::Call(
                            proc_idx,
                            output.clone().unwrap_or(None).map(|v| v.register()),
                            input_regs,
                        ));
                    }
                }

                if ir.ir.proc_sign[proc_idx].output.is_never() {
                    blocks[*block].instructions.push(Instruction::Unreachable);
                }
                Ok(output.unwrap_or_default())
            } else {
                // generate reset
                let reset_captures =
                    get_captures(ir, &mut ctx.scope, &mut blocks[*block], body, None);
                let reset_params = reset_captures
                    .iter()
                    .copied()
                    .map(|(v, r, m)| (v, ir.ir.regs[r], m))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.proc_sign[ctx.proc_idx];
                let debug_name = format!("{}__reset", proc_sign.debug_name);

                let output = TypeIdx::from_expr(ir, body);
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    Cow::Borrowed(&[]),
                    &[],
                    &reset_params,
                    output,
                    debug_name,
                    body,
                    None,
                    proc_todo,
                );

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r, _)| r).collect();

                // execute proc
                let output = ir.ir.proc_sign[proc_idx].output.into_result(ir);

                blocks[*block].instructions.push(Instruction::Call(
                    proc_idx,
                    output.clone().unwrap_or(None).map(|v| v.register()),
                    input_regs,
                ));
                Ok(output.unwrap_or_default())
            }
        }
        E::String(ref s) => {
            let reg = ir.next_reg(TYPE_STR_SLICE);

            blocks[*block]
                .instructions
                .push(Instruction::InitString(reg, s.clone()));

            Ok(Some(Value::Value(reg, None)))
        }
        E::Character(ref s) => {
            let ty = TypeIdx::from_expr(ir, ctx.expr);
            let ty = TypeIdx::from_type(ir, ty);
            let reg = ir.next_reg(ty);

            match ir.ir.types[ty] {
                Type::Int8 => {
                    let byte = s.bytes().next().unwrap();
                    blocks[*block]
                        .instructions
                        .push(Instruction::Init(reg, byte as u64));
                }
                _ => unreachable!(),
            }

            Ok(Some(Value::Value(reg, None)))
        }

        E::Int(i) => {
            let ty = TypeIdx::from_expr(ir, ctx.expr);
            if ir.asys.types[ty].is_int() {
                let ty = TypeIdx::from_type(ir, ty);
                let reg = ir.next_reg(ty);

                blocks[*block]
                    .instructions
                    .push(Instruction::Init(reg, i as u64));

                Ok(Some(Value::Value(reg, None)))
            } else {
                // zero init
                let ty = TypeIdx::from_type(ir, ty);
                let reg = ir.next_reg(ty);

                blocks[*block].instructions.push(Instruction::Zeroinit(reg));

                Ok(Some(Value::Value(reg, None)))
            }
        }

        E::Ident(id) => {
            let val = ir.asys.values[id];
            let mut reg = ir.get_in_scope(val, &ctx.scope);
            if let Type::Handler(idx) = ir.ir.types[reg.get_type(&ir.ir)] {
                if let analyzer::Type::Handler(_, _, def) = ir.asys.types[ir.asys.exprs[ctx.expr]] {
                    if let Some(def) = def {
                        if matches!(ir.asys.handlers[def], analyzer::HandlerDef::Signature)
                            && !ir.ir.handler_type[idx].break_ty.is_never()
                        {
                            // we clone the handler if we got it from the signature
                            // this is so the cloned handler will always be attached to the same try block
                            // no need to clone if the handler never breaks, this is only for correcting breaks
                            let cloned = ir.handlers[idx].clone();
                            let cloned = ir.handlers.push(HandlerIdx, cloned);
                            let ty = ir.ir.handler_type[idx].clone();
                            ir.ir.handler_type.push_value(ty);

                            let ty = ir.insert_type(Type::Handler(cloned));
                            reg = reg.cast(ir, &mut blocks[*block], ty);

                            // add redirect to current proc
                            let proc = &mut ir.ir.proc_sign[ctx.proc_idx];
                            if proc.handled.contains(&idx) {
                                proc.handled.push(cloned);
                            } else {
                                proc.redirect.push((cloned, idx));
                            }
                        }
                    }
                }
            }
            Ok(Some(reg))
        }
        E::Uninit => {
            let ty = TypeIdx::from_expr(ir, ctx.expr);
            let ty = TypeIdx::from_type(ir, ty);
            let reg = ir.next_reg(ty);
            blocks[*block].instructions.push(Instruction::Uninit(reg));
            Ok(Some(Value::Value(reg, None)))
        }
        E::Error => unreachable!(),
    }
}

struct Path {
    changed: HashMap<Val, Value>,
    block_end: BlockIdx,
}

fn generate_phi(
    ir: &mut IRContext,
    blocks: &mut VecMap<BlockIdx, Block>,
    block: BlockIdx,
    scope: &mut Scope,
    paths: &[Path],
) {
    let mut keys = HashSet::<Val>::new();
    for path in paths.iter() {
        keys.extend(path.changed.keys());
    }

    for val in keys.into_iter() {
        let values = paths
            .iter()
            .map(|path| match path.changed.get(&val) {
                Some(v) => v,
                None => scope.get(val).unwrap(),
            })
            .collect::<Vec<_>>();

        if values.iter().all(|v| matches!(v, Value::Value(_, _))) {
            let regs = values
                .into_iter()
                .zip(paths.iter().map(|p| p.block_end))
                .map(|(v, e)| (v.value(ir, &mut blocks[e]), e))
                .collect::<Vec<_>>();
            let new = ir.copy_reg(regs[0].0);
            blocks[block].instructions.push(Instruction::Phi(new, regs));
            scope.insert(val, Value::Value(new, Some(val)))
        } else {
            let regs = values
                .into_iter()
                .zip(paths.iter().map(|p| p.block_end))
                .map(|(v, e)| (v.reference(ir, &mut Scope::default(), &mut blocks[e]), e))
                .collect::<Vec<_>>();
            let new = ir.copy_reg(regs[0].0);
            blocks[block].instructions.push(Instruction::Phi(new, regs));
            scope.insert(val, Value::Reference(new))
        }
    }
}
