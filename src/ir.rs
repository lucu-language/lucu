use std::{
    borrow::Cow,
    collections::HashMap,
    fmt::{self, Display},
    rc::Rc,
    write,
};

use either::Either;

use crate::{
    analyzer::{
        self, Analysis, Definition, EffFunIdx, Val, DEBUG, PUTINT_IDX, PUTSTR_IDX, TYPE_NONE,
    },
    parser::{ExprIdx, Expression, Op, Parsed, AST},
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Aggregate(AggrIdx),

    // Handler without a try-with block purther up the stack
    NakedHandler(HandlerIdx),

    // Handler from a try-with block
    Handler(HandlerIdx),

    // Temporary output value of functions that return handlers
    HandlerOutput,

    BytePointer,
    ArraySize,

    Never,
    None,
}

impl Type {
    fn is_never(&self) -> bool {
        matches!(self, Type::Never)
    }
    fn from_type(ir: &IRContext, typ: analyzer::TypeIdx) -> Type {
        use analyzer::Type as T;
        match ir.asys.types[typ] {
            T::Int => Type::Int,
            T::Str => Type::Aggregate(STR_SLICE),
            T::Bool => Type::Int,
            T::None => Type::None,
            T::Never => Type::Never,
            T::FunctionLiteral(_) => todo!(),

            // Supposed to be handled on a case-by-case basis
            T::Handler(_, _, _) => unreachable!(),
            T::Unknown => unreachable!(),
        }
    }
    fn from_return_type(ir: &IRContext, typ: analyzer::TypeIdx) -> Type {
        use analyzer::Type as T;
        match ir.asys.types[typ] {
            T::Handler(_, _, _) => Type::HandlerOutput,
            _ => Type::from_type(ir, typ),
        }
    }
    fn from_val(ir: &IRContext, val: Val) -> Type {
        match ir.asys.defs[val] {
            Definition::Parameter(_, _, t) => Type::from_type(ir, t),
            Definition::Variable(_, _, t) => Type::from_type(ir, t),
            Definition::EffectFunction(_, _, _) => todo!(),
            Definition::Function(_, _) => todo!(),

            // TODO: type type
            Definition::BuiltinType(_) => todo!(),
            Definition::BuiltinEffect => todo!(),
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct BlockIdx(usize);

impl From<BlockIdx> for usize {
    fn from(value: BlockIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct AggrIdx(usize);

impl From<AggrIdx> for usize {
    fn from(value: AggrIdx) -> Self {
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

    // create handler
    Handler(Reg, Vec<Reg>),

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
    fun: Either<Val, (HandlerIdx, EffFunIdx)>,
    handlers: Vec<HandlerIdx>,
}

#[derive(Debug, Clone)]
struct HandlerCtx {
    effect: Val,
    global: Option<Global>,
    definition: Option<ExprIdx>,
    captures: Vec<(Val, Type)>,
}

#[derive(Debug, Clone)]
pub struct HandlerType {
    pub captures: Vec<Type>,
    pub break_ty: Type,
}

type Scope = HashMap<Val, Either<Reg, Global>>;

struct IRContext<'a> {
    ir: IR,

    proc_map: HashMap<ProcIdent, ProcIdx>,
    implied_handlers: HashMap<Val, HandlerIdx>,

    handlers: VecMap<HandlerIdx, HandlerCtx>,

    ast: &'a AST,
    ctx: &'a Parsed,
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
    fn get_in_scope(&mut self, val: Val, scope: &Scope) -> Either<Reg, Global> {
        match scope.get(&val).copied() {
            Some(r) => r,
            None => {
                let idx = self.implied_handlers[&val];
                let reg = self.next_reg(Type::NakedHandler(idx));
                Either::Left(reg)
            }
        }
    }
    fn new_handler(
        &mut self,
        eff_val: Val,
        global: bool,
        break_type: Type,
        definition: ExprIdx,
        scope: &Scope,
    ) -> HandlerIdx {
        let captures = match self.asys.types[self.asys.exprs[definition]] {
            analyzer::Type::Handler(_, _, def) => match def.map(|h| &self.asys.handlers[h]) {
                Some(analyzer::HandlerDef::Handler(_, captures)) => captures
                    .iter()
                    .copied()
                    .map(|v| {
                        (
                            v,
                            match scope.get(&v) {
                                Some(reg) => match *reg {
                                    Either::Left(reg) => self.ir.regs[reg],
                                    Either::Right(glob) => self.ir.globals[glob],
                                },
                                None => Type::from_val(self, v),
                            },
                        )
                    })
                    .collect(),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };

        // generate handler
        let global = match global {
            true => Some(
                self.ir
                    .globals
                    .push(Global, Type::Handler(HandlerIdx(self.handlers.len()))),
            ),
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
                .map(|(_, t)| t)
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

    pub regs: VecMap<Reg, Type>,
    pub globals: VecMap<Global, Type>,

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

pub const STR_SLICE: AggrIdx = AggrIdx(0);

#[derive(Clone)]
struct ProcCtx {
    proc_idx: ProcIdx,
    expr: ExprIdx,
    inside_handler: Option<HandlerIdx>,
    scope: Scope,
    handler_defs: Rc<[(ExprIdx, HandlerIdx)]>,
}
impl ProcCtx {
    fn with_expr(&mut self, expr: ExprIdx) -> &mut Self {
        self.expr = expr;
        self
    }
    fn child(&self, expr: ExprIdx) -> Self {
        let mut clone = self.clone();
        clone.expr = expr;
        clone
    }
}
type ProcTodo = Vec<ProcCtx>;

pub fn generate_ir(ast: &AST, ctx: &Parsed, asys: &Analysis) -> IR {
    let mut ir = IRContext {
        proc_map: HashMap::new(),
        handlers: VecMap::new(),
        implied_handlers: HashMap::new(),
        ast,
        ctx,
        asys,
        ir: IR {
            proc_sign: VecMap::new(),
            proc_impl: VecMap::new(),
            main: ProcIdx(0),

            regs: VecMap::new(),
            globals: VecMap::new(),
            aggregates: VecMap::new(),

            handler_type: VecMap::new(),
        },
    };

    ir.ir.aggregates.push_value(AggregateType {
        children: vec![Type::BytePointer, Type::ArraySize],
        debug_name: "str".into(),
    });

    // define putint
    let inputs = vec![ir.next_reg(Type::Int)];
    let putint = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output: Type::None,
            debug_name: "putint".into(),
            handled: Vec::new(),
            captures: None,
            unhandled: Vec::new(),
            redirect: Vec::new(),
        },
    );
    ir.ir.proc_impl.push_value(ProcImpl {
        blocks: vec![Block {
            instructions: vec![Instruction::PrintNum(Reg(0)), Instruction::Return(None)],
            next: None,
        }]
        .into(),
    });

    let inputs = vec![ir.next_reg(Type::Aggregate(STR_SLICE))];
    let putstr = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output: Type::None,
            debug_name: "putstr".into(),
            handled: Vec::new(),
            captures: None,
            unhandled: Vec::new(),
            redirect: Vec::new(),
        },
    );
    ir.ir.proc_impl.push_value(ProcImpl {
        blocks: vec![Block {
            instructions: vec![Instruction::PrintStr(Reg(1)), Instruction::Return(None)],
            next: None,
        }]
        .into(),
    });

    // define debug
    let debug = ir.handlers.push(
        HandlerIdx,
        HandlerCtx {
            effect: DEBUG,
            global: None,
            definition: None,
            captures: Vec::new(),
        },
    );
    ir.ir.handler_type.push_value(HandlerType {
        captures: Vec::new(),
        break_ty: Type::Never,
    });

    ir.proc_map.insert(
        ProcIdent {
            fun: Either::Right((debug, PUTINT_IDX)),
            handlers: Vec::new(),
        },
        putint,
    );
    ir.proc_map.insert(
        ProcIdent {
            fun: Either::Right((debug, PUTSTR_IDX)),
            handlers: Vec::new(),
        },
        putstr,
    );

    // generate main signature
    let main = asys.main.expect("no main function");
    let fun = &ir.ast.functions[main];
    let val = ir.asys.values[fun.decl.name];
    let mut proc_todo = Vec::new();

    ir.ir.main = generate_proc_sign(
        &mut ir,
        Some(Either::Left(val)),
        Cow::Borrowed(&[debug]),
        &[],
        &Vec::new(),
        TYPE_NONE,
        "main".into(),
        fun.body,
        None,
        &mut proc_todo,
    );

    // generate implied handlers
    for expr in ast.implied.iter().copied() {
        let ast_handler = match &ir.ctx.exprs[expr].0 {
            Expression::Handler(ast_handler) => ast_handler,
            _ => unreachable!(),
        };

        let break_type = match ir.asys.types[ir.asys.exprs[expr]] {
            analyzer::Type::Handler(_, t, _) => Type::from_type(&ir, t),
            _ => unreachable!(),
        };

        // get effect
        let eff_ident = ast_handler.effect;
        let eff_val = ir.asys.values[eff_ident];

        let handler_idx = ir.new_handler(eff_val, false, break_type, expr, &HashMap::new());

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

fn get_proc(
    ir: &mut IRContext,
    val: Val,
    proc_idx: ProcIdx,
    scope: &Scope,
    param_types: Box<[Type]>,
    mut reg_args: Option<&mut Vec<Reg>>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    match ir.asys.defs[val] {
        Definition::EffectFunction(eff_val, eff_fun_idx, _) => {
            // get handler
            let handler_val = ir.get_in_scope(eff_val, scope);
            let handler_idx = match match handler_val {
                Either::Left(reg) => ir.ir.regs[reg],
                Either::Right(glob) => ir.ir.globals[glob],
            } {
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

            let proc = get_handler_proc(
                ir,
                handler_idx,
                eff_fun_idx,
                scope,
                param_types,
                reg_args.as_deref_mut(),
                proc_todo,
            );

            // get closure
            if let Some(reg_args) = reg_args {
                if let Either::Left(reg) = handler_val {
                    reg_args.push(reg);
                }
            }

            proc
        }
        Definition::Function(func_idx, _) => {
            // create proc identity
            let fun = &ir.ast.functions[func_idx];

            let effects = fun
                .decl
                .sign
                .effects
                .iter()
                .map(|&e| {
                    let effect = ir.asys.values[e];
                    let handler_val = ir.get_in_scope(effect, scope);
                    let handler_idx = match match handler_val {
                        Either::Left(reg) => ir.ir.regs[reg],
                        Either::Right(glob) => ir.ir.globals[glob],
                    } {
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
            };

            if let Some(reg_args) = reg_args {
                reg_args.extend(
                    procident
                        .handlers
                        .iter()
                        .filter_map(|&idx| scope[&ir.handlers[idx].effect].left()),
                );
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
                    .copied()
                    .map(|(ident, _)| ir.asys.values[ident])
                    .zip(param_types.iter().copied())
                    .collect::<Vec<_>>();

                let output = Type::from_function(ir, val);

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
    _scope: &Scope,
    param_types: Box<[Type]>,
    _reg_args: Option<&mut Vec<Reg>>,
    proc_todo: &mut ProcTodo,
) -> ProcIdx {
    let handler = &ir.handlers[handler_idx];
    let eff_val = handler.effect;

    let procident = ProcIdent {
        fun: Either::Right((handler_idx, eff_fun_idx)),
        handlers: Vec::new(), // TODO: handler effects
    };

    // get proc
    if !ir.proc_map.contains_key(&procident) {
        let handlers = &procident.handlers;
        let effect = match ir.asys.defs[eff_val] {
            Definition::Effect(idx) => &ir.ast.effects[idx],
            _ => unreachable!(),
        };
        let val = ir.asys.values[effect.functions[eff_fun_idx].name];
        let ast_handler = match &ir.ctx.exprs[handler.definition.unwrap()].0 {
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
            .copied()
            .map(|(ident, _)| ir.asys.values[ident])
            .zip(param_types.iter().copied())
            .collect::<Vec<_>>();

        let output = Type::from_function(ir, val);

        // generate debug name
        let eff_name = ir.ctx.idents[effect.name].0.as_str();
        let proc_name = ir.ctx.idents[effect.functions[eff_fun_idx].name].0.as_str();
        let mut debug_name = format!("{}.{}.{}", proc_name, eff_name, usize::from(handler_idx));

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
    params: &[(Val, Type)],
    output: analyzer::TypeIdx,
    debug_name: String,
    body: ExprIdx,
    inside_handler: Option<HandlerIdx>,
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

    for idx in unhandled.iter().copied().chain(handled.iter().copied()) {
        let handler = &ir.handlers[idx];

        match handler.global {
            Some(glob) => {
                scope.insert(handler.effect, Either::Right(glob));
            }
            None => {
                let reg = ir.ir.regs.push(Reg, Type::Handler(idx));
                inputs.push(reg);
                scope.insert(handler.effect, Either::Left(reg));
            }
        }
    }

    let captures = if let Some(idx) = inside_handler {
        let handler = &ir.handlers[idx];

        let mut members = Vec::new();
        for (val, typ) in handler.captures.iter().copied() {
            let reg = ir.ir.regs.push(Reg, typ);
            members.push(reg);
            scope.insert(val, Either::Left(reg));
        }

        Some(Captures {
            input: match handler.global {
                Some(glob) => {
                    scope.insert(handler.effect, Either::Right(glob));
                    Either::Right(glob)
                }
                None => {
                    let reg = ir.ir.regs.push(Reg, Type::Handler(idx));
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

    // create handlers
    let mut handler_defs = Vec::new();
    ir.ctx.for_each_ignore_try(body, &mut |expr| {
        if let Expression::Handler(h) = &ir.ctx.exprs[expr].0 {
            // get break type
            let break_type = match ir.asys.types[ir.asys.exprs[expr]] {
                analyzer::Type::Handler(_, t, _) => Type::from_type(ir, t),
                _ => unreachable!(),
            };

            // create handler
            let handler = ir.new_handler(ir.asys.values[h.effect], false, break_type, expr, &scope);

            handler_defs.push((expr, handler));
        }
    });

    // create signature
    let proc_idx = ir.ir.proc_sign.push(
        ProcIdx,
        ProcSign {
            inputs,
            output: Type::from_return_type(ir, output),
            debug_name,
            captures,
            unhandled: inside_handler
                .iter()
                .copied()
                .filter(|_| ir.ctx.yeets(body))
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
            },
            proc_idx,
        );
    }

    let handler_defs = Rc::from(handler_defs);
    proc_todo.push(ProcCtx {
        proc_idx,
        expr: body,
        inside_handler,
        scope: scope.clone(),
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
) -> Type {
    let handler = match ir.asys.handlers[def.expect("function return handler type not filled in")] {
        analyzer::HandlerDef::Handler(expr, _) => Type::NakedHandler(
            defs.iter()
                .find(|&&(e, _)| expr == e)
                .expect("function returns handler not defined by self")
                .1,
        ),
        analyzer::HandlerDef::Call(fun, ref exprs) => {
            let param_types = exprs
                .iter()
                .copied()
                .map(|expr| match ir.asys.types[ir.asys.exprs[expr]] {
                    analyzer::Type::Handler(effect, _, def) => {
                        // recursive call!
                        handler_type(ir, effect, def, proc_idx, defs, scope, proc_todo)
                    }
                    _ => Type::from_type(ir, ir.asys.exprs[expr]),
                })
                .collect();

            // recursive call!
            let proc = get_proc(ir, fun, proc_idx, &scope, param_types, None, proc_todo);
            ir.ir.proc_sign[proc].output
        }
        analyzer::HandlerDef::Param(p) => {
            let reg = ir.ir.proc_sign[proc_idx].inputs[usize::from(p)];
            ir.ir.regs[reg]
        }
        analyzer::HandlerDef::Signature => match ir.get_in_scope(effect, scope) {
            Either::Left(reg) => ir.ir.regs[reg],
            Either::Right(glob) => ir.ir.globals[glob],
        },
        analyzer::HandlerDef::Error => unreachable!(),
    };
    handler
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
    ir.ctx.for_each(expr, &mut |expr| {
        if let Expression::Ident(i) = ir.ctx.exprs[expr].0 {
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
    use Expression as E;
    match ir.ctx.exprs[ctx.expr].0 {
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
                .expect("let value does not return a value");
            ctx.scope.insert(val, Either::Left(reg));
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
            match ir.ctx.exprs[func].0 {
                E::Member(handler, id) => {
                    let val = ir.asys.values[id];

                    // get handler
                    let handler_reg =
                        generate_expr(ir, ctx.with_expr(handler), blocks, block, proc_todo)?
                            .expect("member parent does not return a value");

                    match ir.ir.regs[handler_reg] {
                        Type::NakedHandler(handler_idx) | Type::Handler(handler_idx) => {
                            // add naked handler to handled
                            if matches!(ir.ir.regs[handler_reg], Type::NakedHandler(_)) {
                                let proc = &mut ir.ir.proc_sign[ctx.proc_idx];
                                if !proc.handled.contains(&handler_idx) {
                                    proc.handled.push(handler_idx);
                                }
                            }

                            let handler = &ir.handlers[handler_idx];
                            let global = handler.global;

                            // get output
                            let eff_fun_idx = match ir.asys.defs[val] {
                                Definition::EffectFunction(_, eff_fun_idx, _) => eff_fun_idx,
                                _ => panic!(),
                            };
                            let proc_idx = get_handler_proc(
                                ir,
                                handler_idx,
                                eff_fun_idx,
                                &ctx.scope,
                                reg_args.iter().copied().map(|r| ir.ir.regs[r]).collect(),
                                Some(&mut reg_args),
                                proc_todo,
                            );
                            let typ = ir.ir.proc_sign[proc_idx].output;
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
                    let proc_idx = get_proc(
                        ir,
                        val,
                        ctx.proc_idx,
                        &ctx.scope,
                        reg_args.iter().copied().map(|r| ir.ir.regs[r]).collect(),
                        Some(&mut reg_args),
                        proc_todo,
                    );

                    let typ = ir.ir.proc_sign[proc_idx].output;
                    let output = typ.into_result(ir);

                    // execute function
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
                _ => todo!(),
            }
        }
        E::Member(_, _) => todo!(),
        E::IfElse(cond, yes, no) => {
            let cond = generate_expr(ir, ctx.with_expr(cond), blocks, block, proc_todo)?
                .expect("condition has no value");

            match no {
                Some(no) => {
                    let no_start = blocks.push(BlockIdx, Block::default());

                    let mut no_end = no_start;
                    let mut no_ctx = ctx.child(no);
                    let no_reg = generate_expr(ir, &mut no_ctx, blocks, &mut no_end, proc_todo);

                    let yes_start = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, no_start));

                    let mut yes_end = yes_start;
                    let mut yes_ctx = ctx.child(yes);
                    let yes_reg = generate_expr(ir, &mut yes_ctx, blocks, &mut yes_end, proc_todo);

                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block].next = Some(no_start);
                    blocks[yes_end].next = Some(end);
                    blocks[no_end].next = Some(end);
                    *block = end;

                    // add phi instructions for changed values
                    for val in yes_ctx.scope.keys().copied() {
                        let Some(Either::Left(no)) = no_ctx.scope.get(&val).copied() else { continue };
                        let Some(Either::Left(yes)) = yes_ctx.scope.get(&val).copied() else { continue };
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
                    let mut yes_ctx = ctx.child(yes);
                    let _ = generate_expr(ir, &mut yes_ctx, blocks, &mut yes_end, proc_todo);

                    blocks[*block].next = Some(end);
                    blocks[yes_end].next = Some(end);
                    *block = end;

                    // add phi instructions for changed values
                    for val in yes_ctx.scope.keys().copied() {
                        let Some(Either::Left(no)) = ctx.scope.get(&val).copied() else { continue };
                        let Some(Either::Left(yes)) = yes_ctx.scope.get(&val).copied() else { continue };
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

                let right = generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
                    .expect("right operand has no value");

                ctx.scope.insert(left, Either::Left(right));
                Ok(None)
            } else {
                let left = generate_expr(ir, ctx.with_expr(left), blocks, block, proc_todo)?
                    .expect("left operand has no value");

                let right = generate_expr(ir, ctx.with_expr(right), blocks, block, proc_todo)?
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
                .map(|expr| generate_expr(ir, ctx.with_expr(expr), blocks, block, proc_todo))
                .unwrap_or(Ok(None))?;

            // TODO: we assume this is top level inside a handler
            blocks[*block]
                .instructions
                .push(Instruction::Yeet(reg, ctx.inside_handler.unwrap()));

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
                            .copied()
                            .map(|v| {
                                let reg = ir.get_in_scope(v, &ctx.scope);
                                match reg {
                                    Either::Left(reg) => reg,
                                    Either::Right(glob) => {
                                        let reg = ir.next_reg(ir.ir.globals[glob]);
                                        blocks[*block]
                                            .instructions
                                            .push(Instruction::GetGlobal(reg, glob));
                                        reg
                                    }
                                }
                            })
                            .collect(),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                })
                .unwrap_or(Vec::new());

            // create handler closure
            let closure_reg = ir.next_reg(Type::NakedHandler(handler_idx));

            blocks[*block]
                .instructions
                .push(Instruction::Handler(closure_reg, captures));

            Ok(Some(closure_reg))
        }
        E::TryWith(body, _, handler) => {
            if let Some(handler) = handler {
                // get handler
                let closure_reg =
                    generate_expr(ir, ctx.with_expr(handler), blocks, block, proc_todo)?
                        .expect("try handler does not return a value");
                let handler_idx = match ir.ir.regs[closure_reg] {
                    Type::NakedHandler(handler_idx) | Type::Handler(handler_idx) => handler_idx,
                    _ => panic!(),
                };
                let naked = matches!(ir.ir.regs[closure_reg], Type::NakedHandler(_));
                let eff_val = ir.handlers[handler_idx].effect;
                let global = ir.handlers[handler_idx].global;

                // generate reset
                let reset_captures =
                    get_captures(ir, &ctx.scope, &mut blocks[*block], body, Some(eff_val));
                let reset_params = reset_captures
                    .iter()
                    .copied()
                    .map(|(v, r)| (v, ir.ir.regs[r]))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.proc_sign[ctx.proc_idx];
                let debug_name = format!(
                    "{}__reset.{}",
                    proc_sign.debug_name,
                    usize::from(handler_idx)
                );

                let handlers = &[handler_idx];
                let (handled, unhandled): (Cow<[HandlerIdx]>, &[HandlerIdx]) = if naked {
                    (Cow::Borrowed(&[]), handlers)
                } else {
                    (Cow::Borrowed(handlers), &[])
                };

                let output = Type::from_expr(ir, body);
                let proc_idx = generate_proc_sign(
                    ir,
                    None,
                    handled,
                    unhandled,
                    &reset_params,
                    output,
                    debug_name,
                    body,
                    None,
                    proc_todo,
                );

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r)| r).collect();

                // execute proc
                let output = ir.ir.proc_sign[proc_idx].output;
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
                let reset_captures = get_captures(ir, &ctx.scope, &mut blocks[*block], body, None);
                let reset_params = reset_captures
                    .iter()
                    .copied()
                    .map(|(v, r)| (v, ir.ir.regs[r]))
                    .collect::<Vec<_>>();

                // add handler to handler list
                let proc_sign = &ir.ir.proc_sign[ctx.proc_idx];
                let debug_name = format!("{}__reset", proc_sign.debug_name);

                let output = Type::from_expr(ir, body);
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

                let input_regs: Vec<Reg> = reset_captures.into_iter().map(|(_, r)| r).collect();

                // execute proc
                let output = ir.ir.proc_sign[proc_idx].output;
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
            let reg = ir.get_in_scope(val, &ctx.scope);
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
            if let Type::Handler(idx) = ir.ir.regs[reg] {
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
                            ir.ir.regs[reg] = Type::Handler(cloned);

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
        E::Error => unreachable!(),
    }
}
