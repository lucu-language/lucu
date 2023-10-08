use std::{
    collections::HashMap,
    fmt::{self, Display},
    write,
};

use either::Either;

use crate::{
    analyzer::{self, Analysis, Definition, EffFunIdx, Val, DEBUG},
    parser::{ExprIdx, Expression, Op, ParseContext, AST},
    vecmap::VecMap,
};

#[derive(Debug)]
pub struct Captures {
    pub input: Either<Reg, Global>,
    pub members: Vec<Reg>,
}

#[derive(Debug)]
pub struct ProcSign {
    pub inputs: Vec<Reg>,
    pub captures: Option<Captures>,

    pub output: Type,
    pub debug_name: String,

    pub unhandled: Vec<HandlerIdx>,
    pub handled: Vec<HandlerIdx>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Aggregate(TypeIdx),
    Handler(HandlerIdx, TypeIdx),

    BytePointer,
    ArraySize,

    Never,
    None,
}

impl Type {
    fn is_never(&self) -> bool {
        matches!(self, Type::Never)
    }
    fn from_type(
        ir: &mut IRContext,
        typ: &analyzer::Type,
        handler: Option<&mut Option<HandlerIdx>>,
    ) -> Type {
        use analyzer::Type as T;
        match typ {
            T::Int | T::IntLiteral => Type::Int,
            T::Str | T::StrLiteral => Type::Aggregate(STR_SLICE),
            T::Bool => Type::Int,
            T::None => Type::None,
            T::Never => Type::Never,
            T::Handler(effect, break_type) => {
                let spot = handler.expect("unsupported handler type");
                let break_type = Type::from_type(ir, break_type, None);
                let idx = ir.new_handler(*effect, false, break_type);
                *spot = Some(idx);
                Type::Handler(idx, ir.handlers[idx].closure)
            }
            T::FunctionLiteral(_) => todo!(),

            T::Unknown => unreachable!(),
        }
    }
    fn from_expr(ir: &mut IRContext, expr: ExprIdx) -> Type {
        Type::from_type(ir, &ir.asys.types[expr], None)
    }
    fn from_val(ir: &mut IRContext, val: Val) -> Type {
        match &ir.asys.defs[val] {
            Definition::Parameter(_, _, t) => Type::from_type(ir, t, None),
            Definition::Variable(_, t) => Type::from_type(ir, t, None),
            Definition::EffectFunction(_, _, _) => todo!(),
            Definition::Function(_, _) => todo!(),

            // TODO: type type
            Definition::BuiltinType(_) => todo!(),
            Definition::BuiltinEffect => todo!(),
            Definition::Effect(_) => todo!(),
        }
    }
    fn from_function(
        ir: &mut IRContext,
        val: Val,
        handler: Option<&mut Option<HandlerIdx>>,
    ) -> Type {
        match &ir.asys.defs[val] {
            Definition::EffectFunction(_, _, t) => Type::from_type(ir, t, handler),
            Definition::Function(_, t) => Type::from_type(ir, t, handler),
            _ => unreachable!(),
        }
    }
    fn into_result(self, ir: &mut IRContext) -> ExprResult {
        match self {
            Type::Never => Err(Never),
            Type::None => Ok(None),
            _ => Ok(Some(ir.next_reg(self))),
        }
    }
}

pub struct AggregateType {
    pub children: Vec<Type>,
    pub debug_name: String,
}
impl AggregateType {
    fn new(debug_name: String) -> Self {
        Self {
            children: Vec::new(),
            debug_name,
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct BlockIdx(usize);

impl From<BlockIdx> for usize {
    fn from(value: BlockIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TypeIdx(usize);

impl From<TypeIdx> for usize {
    fn from(value: TypeIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Reg(usize);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Global(usize);

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

impl From<Reg> for usize {
    fn from(value: Reg) -> Self {
        value.0
    }
}

impl From<Global> for usize {
    fn from(value: Global) -> Self {
        value.0
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

    // globals
    SetScopedGlobal(Global, Reg, BlockIdx),
    GetGlobal(Reg, Global),

    // conditionals
    Branch(Reg, BlockIdx, BlockIdx),
    Phi(Reg, [(Reg, BlockIdx); 2]),

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

    // create aggregate type
    Aggregate(Reg, Vec<Reg>),
    Member(Reg, Reg, usize),
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
    fun: Val,
    handlers: Box<[HandlerIdx]>,
}

#[derive(Debug)]
struct Handler {
    effect: Val,
    closure: TypeIdx,
    global: Option<Global>,
    procs: VecMap<EffFunIdx, ProcIdx>,
}

type Scope = HashMap<Val, Either<Reg, Global>>;

struct IRContext<'a> {
    ir: IR,

    proc_map: HashMap<ProcIdent, ProcIdx>,
    handlers: VecMap<HandlerIdx, Handler>,
    implied_handlers: HashMap<Val, Global>,

    ast: &'a AST,
    ctx: &'a ParseContext,
    asys: &'a Analysis,
}

impl<'a> IRContext<'a> {
    fn copy_reg(&mut self, reg: Reg) -> Reg {
        let typ = self.ir.regs[reg];
        self.next_reg(typ)
    }
    fn next_reg(&mut self, typ: Type) -> Reg {
        self.ir.regs.push(Reg, typ)
    }
    fn get_handler(&mut self, proc: ProcIdx, eff_val: Val, scope: &Scope) -> Either<Reg, Global> {
        match scope.get(&eff_val).copied() {
            Some(r) => r,
            None => {
                let glob = self.implied_handlers[&eff_val];
                let idx = match self.ir.globals[glob] {
                    Type::Handler(idx, _) => idx,
                    _ => unreachable!(),
                };
                if !self.ir.break_types[idx].is_never() {
                    self.ir.procsign[proc].handled.push(idx);
                }
                Either::Right(glob)
            }
        }
    }
    fn new_handler(&mut self, eff_val: Val, global: bool, break_type: Type) -> HandlerIdx {
        let eff_idx = match self.asys.defs[eff_val] {
            Definition::Effect(eff_idx) => eff_idx,
            _ => panic!("handler has non-effect as effect value"),
        };
        let effect = &self.ast.effects[eff_idx];

        // generate handler
        let closure_typ = self.ir.aggregates.push(
            TypeIdx,
            AggregateType::new(format!(
                "{}.{}",
                self.ctx.idents[effect.name].0,
                self.handlers.len()
            )),
        );

        // generate handler
        let global = match global {
            true => Some(self.ir.globals.push(
                Global,
                Type::Handler(HandlerIdx(self.handlers.len()), closure_typ),
            )),
            false => None,
        };
        let handler_idx = self.handlers.push(
            HandlerIdx,
            Handler {
                closure: closure_typ,
                global,
                effect: eff_val,
                procs: VecMap::filled(effect.functions.len(), ProcIdx(usize::MAX)),
            },
        );
        self.ir.break_types.push_value(break_type);

        handler_idx
    }
    fn function_output(&mut self, val: Val) -> (Type, Option<HandlerIdx>) {
        let mut handler = None;
        let output = Type::from_function(self, val, Some(&mut handler));
        (output, handler)
    }
}

pub struct IR {
    pub procsign: VecMap<ProcIdx, ProcSign>,
    pub procimpl: VecMap<ProcIdx, ProcImpl>,
    pub main: ProcIdx,

    pub break_types: VecMap<HandlerIdx, Type>,

    pub regs: VecMap<Reg, Type>,
    pub globals: VecMap<Global, Type>,

    pub aggregates: VecMap<TypeIdx, AggregateType>,
}

impl Display for IR {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (sign, imp) in self.procsign.values().zip(self.procimpl.values()) {
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
                        Instruction::Branch(r, y, n) => {
                            writeln!(f, "       jnz {}, {}, {}", r, y, n)?
                        }
                        Instruction::Phi(r, [(r1, b1), (r2, b2)]) => {
                            writeln!(f, "{} <- phi [ {}, {} ], [ {}, {} ]", r, r1, b1, r2, b2,)?
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
                        Instruction::Call(proc, out, ref args) => writeln!(
                            f,
                            "{}cal {}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            self.procsign[proc].debug_name,
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
                        Instruction::SetScopedGlobal(g, r, e) => {
                            writeln!(f, "{} <- ssg {}, {}", g, r, e)?
                        }
                        Instruction::GetGlobal(r, g) => writeln!(f, "{} <- ggl {}", r, g)?,
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

pub const STR_SLICE: TypeIdx = TypeIdx(0);

struct ProcCtx<'a> {
    proc_idx: ProcIdx,
    expr: ExprIdx,
    inside_handler: Option<HandlerIdx>,
    output_handler: Option<HandlerIdx>,
    scope: &'a mut Scope,
}
impl<'a> ProcCtx<'a> {
    fn with_expr(&mut self, expr: ExprIdx, output_handler: Option<HandlerIdx>) -> &mut Self {
        self.expr = expr;
        self.output_handler = output_handler;
        self
    }
    fn child<'b>(&self, expr: ExprIdx, scope: &'b mut Scope) -> ProcCtx<'b> {
        scope.extend(self.scope.iter());
        ProcCtx {
            proc_idx: self.proc_idx,
            expr,
            inside_handler: self.inside_handler,
            output_handler: None,
            scope,
        }
    }
}
type ProcTodo = Vec<(
    ProcIdx,
    ExprIdx,
    Option<HandlerIdx>,
    Option<HandlerIdx>,
    Scope,
)>;

pub fn generate_ir(ast: &AST, ctx: &ParseContext, asys: &Analysis) -> IR {
    let mut ir = IRContext {
        proc_map: HashMap::new(),
        handlers: VecMap::new(),
        implied_handlers: HashMap::new(),
        ast,
        ctx,
        asys,
        ir: IR {
            procsign: VecMap::new(),
            procimpl: VecMap::new(),
            main: ProcIdx(0),

            regs: VecMap::new(),
            globals: VecMap::new(),
            aggregates: VecMap::new(),
            break_types: VecMap::new(),
        },
    };

    ir.ir.aggregates.push_value(AggregateType {
        children: vec![Type::BytePointer, Type::ArraySize],
        debug_name: "str".into(),
    });

    // define putint
    let inputs = vec![ir.next_reg(Type::Int)];
    let putint = ir.ir.procsign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output: Type::None,
            debug_name: "putint".into(),
            handled: Vec::new(),
            captures: None,
            unhandled: Vec::new(),
        },
    );
    ir.ir.procimpl.push_value(ProcImpl {
        blocks: vec![Block {
            instructions: vec![Instruction::PrintNum(Reg(0)), Instruction::Return(None)],
            next: None,
        }]
        .into(),
    });

    let inputs = vec![ir.next_reg(Type::Aggregate(STR_SLICE))];
    let putstr = ir.ir.procsign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output: Type::None,
            debug_name: "putstr".into(),
            handled: Vec::new(),
            captures: None,
            unhandled: Vec::new(),
        },
    );
    ir.ir.procimpl.push_value(ProcImpl {
        blocks: vec![Block {
            instructions: vec![Instruction::PrintStr(Reg(1)), Instruction::Return(None)],
            next: None,
        }]
        .into(),
    });

    // define debug
    let debug_closure = ir
        .ir
        .aggregates
        .push(TypeIdx, AggregateType::new("debug".into()));
    let debug_glob = ir
        .ir
        .globals
        .push(Global, Type::Handler(HandlerIdx(0), debug_closure));
    let debug = ir.handlers.push(
        HandlerIdx,
        Handler {
            effect: DEBUG,
            closure: debug_closure,
            global: Some(debug_glob),
            procs: vec![putint, putstr].into(),
        },
    );
    ir.ir.break_types.push_value(Type::Never);

    // generate main signature
    let main = asys.main.expect("no main function");
    let fun = &ir.ast.functions[main];
    let val = ir.asys.values[fun.decl.name];
    let output = Type::from_function(&mut ir, val, None);

    let params = fun
        .decl
        .sign
        .inputs
        .values()
        .map(|&(ident, _)| {
            let val = ir.asys.values[ident];
            (val, Type::from_val(&mut ir, val))
        })
        .collect::<Vec<_>>();

    let mut proc_todo = Vec::new();

    ir.ir.main = generate_proc_sign(
        &mut ir,
        Some(ProcIdent {
            fun: val,
            handlers: Box::new([debug]),
        }),
        &[],
        &params,
        output,
        "main".into(),
        fun.body,
        None,
        None,
        &mut proc_todo,
    );

    // generate implied handlers
    for expr in ast.implied.iter().copied() {
        let ast_handler = match &ir.ctx.exprs[expr].0 {
            Expression::Handler(ast_handler) => ast_handler,
            _ => unreachable!(),
        };

        let break_type = match &ir.asys.types[expr] {
            analyzer::Type::Handler(_, t) => Type::from_type(&mut ir, t, None),
            _ => unreachable!(),
        };

        // get effect
        let eff_ident = ast_handler.effect;
        let eff_val = ir.asys.values[eff_ident];

        let handler_idx = ir.new_handler(eff_val, true, break_type);

        for fun in ast_handler.functions.iter() {
            let val = ir.asys.values[fun.decl.name];
            let eff_fun_idx = match ir.asys.defs[val] {
                Definition::EffectFunction(_, eff_fun_idx, _) => eff_fun_idx,
                _ => panic!("handler has non-effect-function as a function value"),
            };

            // get params
            let params: Vec<(Val, Type)> = fun
                .decl
                .sign
                .inputs
                .values()
                .map(|&(ident, _)| {
                    let val = ir.asys.values[ident];
                    (val, Type::from_val(&mut ir, val))
                })
                .collect();

            let (output, output_handler) = ir.function_output(val);

            // generate debug name
            let eff_name = ir.ctx.idents[eff_ident].0.as_str();
            let proc_name = ir.ctx.idents[fun.decl.name].0.as_str();
            let debug_name = format!("{}.{}.{}", proc_name, eff_name, usize::from(handler_idx));

            // generate handler proc
            // TODO: add handlers of proc
            let proc_idx = generate_proc_sign(
                &mut ir,
                None,
                &[],
                &params,
                output,
                debug_name,
                fun.body,
                Some((handler_idx, &[])),
                output_handler,
                &mut proc_todo,
            );

            // add to handler
            ir.handlers[handler_idx].procs[eff_fun_idx] = proc_idx;
        }

        // add handler to implied
        ir.implied_handlers
            .insert(eff_val, ir.handlers[handler_idx].global.unwrap());
    }

    // generate
    while !proc_todo.is_empty() {
        let mut first = proc_todo.remove(0);
        let proc = generate_proc_impl(
            &mut ir,
            ProcCtx {
                proc_idx: first.0,
                expr: first.1,
                inside_handler: first.2,
                output_handler: first.3,
                scope: &mut first.4,
            },
            &mut proc_todo,
        );
        ir.ir.procimpl.push_value(proc);
    }

    // bubble up unhandled
    let mut done = false;
    while !done {
        done = true;
        for idx in ir.ir.procsign.keys(ProcIdx) {
            for called in ir.ir.procimpl[idx].calls() {
                // TODO: don't clone here
                for handler in ir.ir.procsign[called].unhandled.clone().into_iter() {
                    let callee = &mut ir.ir.procsign[idx];
                    if !callee.handled.contains(&handler) && !callee.unhandled.contains(&handler) {
                        callee.unhandled.push(handler);
                        done = false;
                    }
                }
            }
        }
    }

    // return ir
    ir.ir
}

fn generate_proc_sign(
    ir: &mut IRContext,
    ident: Option<ProcIdent>,
    handles: &[HandlerIdx],
    params: &[(Val, Type)],
    output: Type,
    debug_name: String,
    body: ExprIdx,
    captures: Option<(HandlerIdx, &[(Val, Reg)])>,
    output_handler: Option<HandlerIdx>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    // get inputs
    let mut inputs = Vec::new();
    let mut scope = Scope::new();
    for (val, typ) in params.iter().copied() {
        let reg = ir.next_reg(typ);
        scope.insert(val, Either::Left(reg));
        inputs.push(reg);
    }

    for idx in ident
        .iter()
        .flat_map(|ident| ident.handlers.iter().copied())
        .chain(handles.iter().copied())
    {
        let handler = &ir.handlers[idx];

        match handler.global {
            Some(glob) => {
                scope.insert(handler.effect, Either::Right(glob));
            }
            None => {
                let reg = ir.ir.regs.push(Reg, Type::Handler(idx, handler.closure));
                inputs.push(reg);
                scope.insert(handler.effect, Either::Left(reg));
            }
        }
    }

    let handler = captures.map(|(h, _)| h);
    let captures = if let Some((idx, captures)) = captures {
        let mut members = Vec::new();
        for &(val, reg) in captures {
            let typ = ir.ir.regs[reg];
            let reg = ir.ir.regs.push(Reg, typ);
            members.push(reg);
            scope.insert(val, Either::Left(reg));
        }

        let handler = &ir.handlers[idx];
        Some(Captures {
            input: match handler.global {
                Some(glob) => {
                    scope.insert(handler.effect, Either::Right(glob));
                    Either::Right(glob)
                }
                None => {
                    let reg = ir.ir.regs.push(Reg, Type::Handler(idx, handler.closure));
                    inputs.push(reg);
                    scope.insert(handler.effect, Either::Left(reg));
                    Either::Left(reg)
                }
            },
            members,
        })
    } else {
        None
    };

    // create signature
    let proc_idx = ir.ir.procsign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output,
            debug_name,
            captures,
            unhandled: handler
                .iter()
                .copied()
                .filter(|_| ir.ctx.yeets(body))
                .collect(),
            handled: handles
                .iter()
                .copied()
                .filter(|&h| !ir.ir.break_types[h].is_never())
                .collect(),
        },
    );

    // add procint if this is a function
    if let Some(ident) = ident {
        ir.proc_map.insert(ident, proc_idx);
    }

    proc_todo.push((proc_idx, body, handler, output_handler, scope));
    proc_idx
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
            blocks[end].instructions.push(Instruction::Return(ret));
        }
    }

    ProcImpl { blocks }
}

#[derive(Clone, Copy)]
struct Never;
type ExprResult = Result<Option<Reg>, Never>;

fn get_captures(
    ir: &mut IRContext,
    scope: &Scope,
    block: &mut Block,
    expr: ExprIdx,
    exception: Option<Val>,
) -> Vec<(Val, Reg)> {
    let mut captures = Vec::new();
    ir.ctx.for_each(expr, |e| {
        if let Expression::Ident(i) = *e {
            let val = ir.asys.values[i];

            // capture effects from (effect) functions
            let vals = match ir.asys.defs[val] {
                Definition::EffectFunction(effect, _, _) => {
                    // TODO: capture effect function effects
                    if Some(effect) == exception {
                        vec![]
                    } else {
                        vec![effect]
                    }
                }
                Definition::Function(fun, _) => ir.ast.functions[fun]
                    .decl
                    .sign
                    .effects
                    .iter()
                    .copied()
                    .filter_map(|i| {
                        let effect = ir.asys.values[i];
                        if Some(effect) == exception {
                            None
                        } else {
                            Some(effect)
                        }
                    })
                    .collect(),
                _ => {
                    if Some(val) == exception {
                        vec![]
                    } else {
                        vec![val]
                    }
                }
            };

            // capture vals
            for val in vals {
                if let Some(e) = scope.get(&val).copied() {
                    if !captures.iter().any(|&(v, _)| v == val) {
                        match e {
                            Either::Left(reg) => captures.push((val, reg)),
                            Either::Right(glob) => {
                                let reg = ir.next_reg(ir.ir.globals[glob]);
                                block.instructions.push(Instruction::GetGlobal(reg, glob));
                                captures.push((val, reg));
                            }
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
    let output_handler = ctx.output_handler;
    use Expression as E;
    match ir.ctx.exprs[ctx.expr].0 {
        E::Body(ref body) => {
            for &expr in body.main.iter() {
                generate_expr(ir, ctx.with_expr(expr, None), blocks, block, proc_todo)?;
            }
            body.last
                .map(|expr| {
                    generate_expr(
                        ir,
                        ctx.with_expr(expr, output_handler),
                        blocks,
                        block,
                        proc_todo,
                    )
                })
                .unwrap_or(Ok(None))
        }
        E::Let(name, _, expr) => {
            let val = ir.asys.values[name];
            let reg = generate_expr(ir, ctx.with_expr(expr, None), blocks, block, proc_todo)?
                .expect("let value does not return a value");
            ctx.scope.insert(val, Either::Left(reg));
            Ok(None)
        }
        E::Call(func, ref args) => {
            // get base registers
            let mut reg_args = args
                .iter()
                .map(|&expr| {
                    generate_expr(ir, ctx.with_expr(expr, None), blocks, block, proc_todo)
                        .map(|r| r.expect("call argument does not return a value"))
                })
                .collect::<Result<Vec<_>, _>>()?;

            // TODO: currently we assume func is an Ident expr or Effect Member expr
            match ir.ctx.exprs[func].0 {
                E::Member(handler, id) => {
                    let val = ir.asys.values[id];

                    // get handler
                    let handler_reg =
                        generate_expr(ir, ctx.with_expr(handler, None), blocks, block, proc_todo)?
                            .expect("member parent does not return a value");

                    match ir.ir.regs[handler_reg] {
                        Type::Handler(handler_idx, _) => {
                            let handler = &ir.handlers[handler_idx];
                            let global = handler.global;

                            // get output
                            let eff_fun_idx = match ir.asys.defs[val] {
                                Definition::EffectFunction(_, eff_fun_idx, _) => eff_fun_idx,
                                _ => panic!(),
                            };
                            let proc_idx = handler.procs[eff_fun_idx];
                            let typ = ir.ir.procsign[proc_idx].output;
                            let output = typ.into_result(ir);

                            // execute handler
                            match global {
                                Some(glob) => {
                                    let next = blocks.push(BlockIdx, Block::default());

                                    blocks[*block]
                                        .instructions
                                        .push(Instruction::SetScopedGlobal(
                                            glob,
                                            handler_reg,
                                            next,
                                        ));

                                    blocks[*block].instructions.push(Instruction::Call(
                                        proc_idx,
                                        output.unwrap_or(None),
                                        reg_args,
                                    ));

                                    blocks[*block].next = Some(next);
                                    *block = next;
                                }
                                None => {
                                    reg_args.push(handler_reg);

                                    blocks[*block].instructions.push(Instruction::Call(
                                        proc_idx,
                                        output.unwrap_or(None),
                                        reg_args,
                                    ));
                                }
                            }

                            if typ.is_never() {
                                blocks[*block].instructions.push(Instruction::Unreachable);
                            }
                            output
                        }
                        _ => todo!(),
                    }
                }
                E::Ident(id) => {
                    let val = ir.asys.values[id];

                    // check handlers
                    match ir.asys.defs[val] {
                        Definition::EffectFunction(eff_val, eff_fun_idx, _) => {
                            // get handler
                            let handler_val = ir.get_handler(ctx.proc_idx, eff_val, ctx.scope);
                            let handler_idx = match match handler_val {
                                Either::Left(reg) => ir.ir.regs[reg],
                                Either::Right(glob) => ir.ir.globals[glob],
                            } {
                                Type::Handler(handler_idx, _) => handler_idx,
                                _ => panic!(),
                            };
                            let handler = &ir.handlers[handler_idx];

                            // get closure
                            if let Either::Left(reg) = handler_val {
                                reg_args.push(reg);
                            }

                            // get output
                            let proc_idx = handler.procs[eff_fun_idx];
                            let typ = ir.ir.procsign[proc_idx].output;
                            let output = typ.into_result(ir);

                            // execute handler
                            blocks[*block].instructions.push(Instruction::Call(
                                proc_idx,
                                output.unwrap_or(None),
                                reg_args,
                            ));

                            if typ.is_never() {
                                blocks[*block].instructions.push(Instruction::Unreachable);
                            }
                            output
                        }
                        Definition::Function(func_idx, _) => {
                            // create proc identity
                            let fun = &ir.ast.functions[func_idx];

                            let effects: Box<[HandlerIdx]> = fun
                                .decl
                                .sign
                                .effects
                                .iter()
                                .map(|&e| {
                                    let effect = ir.asys.values[e];
                                    let handler_val =
                                        ir.get_handler(ctx.proc_idx, effect, ctx.scope);
                                    let handler_idx = match match handler_val {
                                        Either::Left(reg) => ir.ir.regs[reg],
                                        Either::Right(glob) => ir.ir.globals[glob],
                                    } {
                                        Type::Handler(handler_idx, _) => handler_idx,
                                        _ => panic!(),
                                    };
                                    handler_idx
                                })
                                .collect();

                            let procident = ProcIdent {
                                fun: val,
                                handlers: effects,
                            };

                            reg_args.extend(
                                procident
                                    .handlers
                                    .iter()
                                    .filter_map(|&idx| ctx.scope[&ir.handlers[idx].effect].left()),
                            );

                            // get proc
                            let proc_idx = if !ir.proc_map.contains_key(&procident) {
                                let handlers = &procident.handlers;

                                // get params
                                let params: Vec<(Val, Type)> = fun
                                    .decl
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|&(ident, _)| {
                                        let val = ir.asys.values[ident];
                                        (val, Type::from_val(ir, val))
                                    })
                                    .collect();

                                let (output, output_handler) = ir.function_output(val);

                                // generate debug name
                                let mut debug_name = ir.ctx.idents[fun.decl.name].0.clone();

                                if handlers.len() > 0 {
                                    debug_name += ".";

                                    for &handler in handlers.iter() {
                                        let eff_val = ir.handlers[handler].effect;
                                        let eff_name = ir
                                            .ast
                                            .effects
                                            .values()
                                            .find(|e| ir.asys.values[e.name] == eff_val)
                                            .map(|e| ir.ctx.idents[e.name].0.as_str())
                                            .unwrap_or("debug");

                                        debug_name += eff_name;
                                        debug_name += ".";
                                        debug_name += usize::from(handler).to_string().as_str();
                                        debug_name += ".";
                                    }

                                    debug_name.pop();
                                }

                                // generate func
                                let proc_idx = generate_proc_sign(
                                    ir,
                                    Some(procident),
                                    &[],
                                    &params,
                                    output,
                                    debug_name,
                                    fun.body,
                                    None,
                                    output_handler,
                                    proc_todo,
                                );
                                proc_idx
                            } else {
                                ir.proc_map[&procident]
                            };
                            let proc = &ir.ir.procsign[proc_idx];
                            let never = proc.output.is_never();

                            // execute proc
                            let output = proc.output.into_result(ir);

                            blocks[*block].instructions.push(Instruction::Call(
                                proc_idx,
                                output.unwrap_or(None),
                                reg_args,
                            ));

                            if never {
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
        E::Member(_, _) => todo!(),
        E::IfElse(cond, yes, no) => {
            let cond = generate_expr(ir, ctx.with_expr(cond, None), blocks, block, proc_todo)?
                .expect("condition has no value");

            match no {
                Some(no) => {
                    let no_start = blocks.push(BlockIdx, Block::default());

                    let mut no_end = no_start;
                    let mut no_scope = ctx.scope.clone();
                    let no_reg = generate_expr(
                        ir,
                        &mut ctx.child(no, &mut no_scope),
                        blocks,
                        &mut no_end,
                        proc_todo,
                    );

                    let yes_start = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, no_start));

                    let mut yes_end = yes_start;
                    let mut yes_scope = ctx.scope.clone();
                    let yes_reg = generate_expr(
                        ir,
                        &mut ctx.child(yes, &mut yes_scope),
                        blocks,
                        &mut yes_end,
                        proc_todo,
                    );

                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block].next = Some(no_start);
                    blocks[yes_end].next = Some(end);
                    blocks[no_end].next = Some(end);
                    *block = end;

                    // add phi instructions for changed values
                    for val in yes_scope.keys().copied() {
                        let Some(Either::Left(no)) = no_scope.get(&val).copied() else { continue };
                        let Some(Either::Left(yes)) = yes_scope.get(&val).copied() else { continue };
                        if no != yes {
                            let reg = ir.copy_reg(no);
                            blocks[*block]
                                .instructions
                                .push(Instruction::Phi(reg, [(yes, yes_end), (no, no_end)]));
                            ctx.scope.insert(val, Either::Left(reg));
                        }
                    }

                    match (yes_reg, no_reg) {
                        (Ok(Some(yes)), Ok(Some(no))) => {
                            if ir.ir.regs[yes] == ir.ir.regs[no] {
                                let out = ir.copy_reg(yes);
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::Phi(out, [(yes, yes_end), (no, no_end)]));
                                Ok(Some(out))
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

                    let no_end = *block;
                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, end));

                    let mut yes_end = yes_start;
                    let mut yes_scope = ctx.scope.clone();
                    let _ = generate_expr(
                        ir,
                        &mut ctx.child(yes, &mut yes_scope),
                        blocks,
                        &mut yes_end,
                        proc_todo,
                    );

                    blocks[*block].next = Some(end);
                    blocks[yes_end].next = Some(end);
                    *block = end;

                    // add phi instructions for changed values
                    for val in yes_scope.keys().copied() {
                        let Some(Either::Left(no)) = ctx.scope.get(&val).copied() else { continue };
                        let Some(Either::Left(yes)) = yes_scope.get(&val).copied() else { continue };
                        if no != yes {
                            let reg = ir.copy_reg(no);
                            blocks[*block]
                                .instructions
                                .push(Instruction::Phi(reg, [(yes, yes_end), (no, no_end)]));
                            ctx.scope.insert(val, Either::Left(reg));
                        }
                    }

                    Ok(None)
                }
            }
        }
        E::Op(left, op, right) => {
            if op == Op::Assign {
                let left = match ir.ctx.exprs[left].0 {
                    E::Ident(var) => ir.asys.values[var],
                    _ => todo!(),
                };

                let right =
                    generate_expr(ir, ctx.with_expr(right, None), blocks, block, proc_todo)?
                        .expect("right operand has no value");

                ctx.scope.insert(left, Either::Left(right));
                Ok(None)
            } else {
                let left = generate_expr(ir, ctx.with_expr(left, None), blocks, block, proc_todo)?
                    .expect("left operand has no value");

                let right =
                    generate_expr(ir, ctx.with_expr(right, None), blocks, block, proc_todo)?
                        .expect("right operand has no value");

                // TODO: ops with different return types
                let out = ir.next_reg(Type::Int);

                let instr = match op {
                    Op::Equals => Instruction::Equals(out, left, right),
                    Op::Divide => Instruction::Div(out, left, right),
                    Op::Multiply => Instruction::Mul(out, left, right),
                    Op::Subtract => Instruction::Sub(out, left, right),
                    Op::Add => Instruction::Add(out, left, right),
                    Op::Less => Instruction::Less(out, left, right),
                    Op::Greater => Instruction::Greater(out, left, right),
                    Op::Assign => unreachable!(),
                };
                blocks[*block].instructions.push(instr);

                Ok(Some(out))
            }
        }
        E::Yeet(value) => {
            // get break value
            let reg = value
                .map(|expr| generate_expr(ir, ctx.with_expr(expr, None), blocks, block, proc_todo))
                .unwrap_or(Ok(None))?;

            // TODO: we assume this is top level inside a handler
            blocks[*block]
                .instructions
                .push(Instruction::Yeet(reg, ctx.inside_handler.unwrap()));

            // break returns any type
            Err(Never)
        }
        E::Handler(ref ast_handler) => {
            // get break type
            let break_type = match &ir.asys.types[ctx.expr] {
                analyzer::Type::Handler(_, t) => Type::from_type(ir, t, None),
                _ => unreachable!(),
            };

            // get effect
            let eff_ident = ast_handler.effect;
            let eff_val = ir.asys.values[eff_ident];

            // generate handler
            let handler_idx = match output_handler {
                Some(handler_idx) => handler_idx,
                None => ir.new_handler(eff_val, false, break_type),
            };
            let closure_typ = ir.handlers[handler_idx].closure;
            let closure_reg = ir.next_reg(Type::Handler(handler_idx, closure_typ));

            let mut all_captures = Vec::new();

            for fun in ast_handler.functions.iter() {
                let val = ir.asys.values[fun.decl.name];
                let eff_fun_idx = match ir.asys.defs[val] {
                    Definition::EffectFunction(_, eff_fun_idx, _) => eff_fun_idx,
                    _ => panic!("handler has non-effect-function as a function value"),
                };

                // get params
                let params: Vec<(Val, Type)> = fun
                    .decl
                    .sign
                    .inputs
                    .values()
                    .map(|&(ident, _)| {
                        let val = ir.asys.values[ident];
                        (val, Type::from_val(ir, val))
                    })
                    .collect();

                let (output, output_handler) = ir.function_output(val);

                // generate debug name
                let eff_name = ir.ctx.idents[eff_ident].0.as_str();
                let proc_name = ir.ctx.idents[fun.decl.name].0.as_str();
                let debug_name = format!("{}.{}.{}", proc_name, eff_name, usize::from(handler_idx));

                // get captures
                let captures = get_captures(ir, ctx.scope, &mut blocks[*block], fun.body, None);
                for capture in captures.iter().copied() {
                    if !all_captures.contains(&capture) {
                        all_captures.push(capture);
                    }
                }

                // generate handler proc
                // TODO: add handlers of proc
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    &[],
                    &params,
                    output,
                    debug_name,
                    fun.body,
                    Some((handler_idx, &all_captures)),
                    output_handler,
                    proc_todo,
                );

                // add to handler
                ir.handlers[handler_idx].procs[eff_fun_idx] = proc_idx;
            }

            // create handler closure
            let aggregate = all_captures.iter().map(|&(_, reg)| reg).collect::<Vec<_>>();

            ir.ir.aggregates[closure_typ]
                .children
                .extend(aggregate.iter().map(|&reg| ir.ir.regs[reg]));

            blocks[*block]
                .instructions
                .push(Instruction::Aggregate(closure_reg, aggregate));

            Ok(Some(closure_reg))
        }
        E::TryWith(body, _, handler) => {
            if let Some(handler) = handler {
                // get handler
                let closure_reg =
                    generate_expr(ir, ctx.with_expr(handler, None), blocks, block, proc_todo)?
                        .expect("try handler does not return a value");
                let handler_idx = match ir.ir.regs[closure_reg] {
                    Type::Handler(handler_idx, _) => handler_idx,
                    _ => panic!(),
                };
                let eff_val = ir.handlers[handler_idx].effect;
                let global = ir.handlers[handler_idx].global;

                // generate reset
                let reset_captures =
                    get_captures(ir, ctx.scope, &mut blocks[*block], body, Some(eff_val));
                let reset_params = reset_captures
                    .iter()
                    .copied()
                    .map(|(v, r)| (v, ir.ir.regs[r]))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.procsign[ctx.proc_idx];
                let debug_name = format!(
                    "{}__reset.{}",
                    proc_sign.debug_name,
                    usize::from(handler_idx)
                );

                let output = Type::from_expr(ir, body);
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    &[handler_idx],
                    &reset_params,
                    output,
                    debug_name,
                    body,
                    None,
                    output_handler,
                    proc_todo,
                );

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r)| r).collect();

                // execute proc
                let out = output.into_result(ir);

                match global {
                    Some(glob) => {
                        let next = blocks.push(BlockIdx, Block::default());

                        blocks[*block]
                            .instructions
                            .push(Instruction::SetScopedGlobal(glob, closure_reg, next));

                        blocks[*block].instructions.push(Instruction::Call(
                            proc_idx,
                            out.unwrap_or(None),
                            input_regs,
                        ));

                        blocks[*block].next = Some(next);
                        *block = next;
                    }
                    None => {
                        let mut input_regs = input_regs;
                        input_regs.push(closure_reg);

                        blocks[*block].instructions.push(Instruction::Call(
                            proc_idx,
                            out.unwrap_or(None),
                            input_regs,
                        ));
                    }
                }

                if output.is_never() {
                    blocks[*block].instructions.push(Instruction::Unreachable);
                }
                out
            } else {
                // generate reset
                let reset_captures = get_captures(ir, ctx.scope, &mut blocks[*block], body, None);
                let reset_params = reset_captures
                    .iter()
                    .copied()
                    .map(|(v, r)| (v, ir.ir.regs[r]))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.procsign[ctx.proc_idx];
                let debug_name = format!("{}__reset", proc_sign.debug_name);

                let output = Type::from_expr(ir, body);
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    &[],
                    &reset_params,
                    output,
                    debug_name,
                    body,
                    None,
                    output_handler,
                    proc_todo,
                );

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r)| r).collect();

                // execute proc
                let output = output.into_result(ir);

                blocks[*block].instructions.push(Instruction::Call(
                    proc_idx,
                    output.unwrap_or(None),
                    input_regs,
                ));

                output
            }
        }
        E::String(ref s) => {
            let reg = ir.next_reg(Type::Aggregate(STR_SLICE));

            blocks[*block]
                .instructions
                .push(Instruction::InitString(reg, s.clone()));

            Ok(Some(reg))
        }

        E::Int(i) => {
            let reg = ir.next_reg(Type::Int);

            // TODO: handle overflow
            blocks[*block]
                .instructions
                .push(Instruction::Init(reg, i as i64 as u64));

            Ok(Some(reg))
        }

        E::Ident(id) => {
            let val = ir.asys.values[id];
            let reg = ctx
                .scope
                .get(&val)
                .copied()
                .expect("value is not loaded in scope");
            let reg = match reg {
                Either::Left(reg) => reg,
                Either::Right(glob) => {
                    let reg = ir.next_reg(ir.ir.globals[glob]);
                    blocks[*block]
                        .instructions
                        .push(Instruction::GetGlobal(reg, glob));
                    reg
                }
            };
            Ok(Some(reg))
        }
        E::Error => unreachable!(),
    }
}
