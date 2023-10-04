use std::{
    collections::HashMap,
    fmt::{self, Display},
    write,
};

use either::Either;

use crate::{
    analyzer::{Analysis, Definition, EffFunIdx, Val, DEBUG, INT, STR},
    parser::{self, ExprIdx, Expression, Op, ParseContext, AST},
    vecmap::VecMap,
};

#[derive(Debug)]
pub struct ReturnType {
    pub output: Type,
    pub implicit_break: Option<HandlerIdx>,
    pub break_union: Vec<Type>,
}

#[derive(Debug)]
pub struct Procedure {
    pub inputs: Vec<Reg>,
    pub output: ReturnType,

    pub blocks: VecMap<BlockIdx, Block>,
    pub start: BlockIdx,

    pub debug_name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int,
    Aggregate(TypeIdx),

    BytePointer,
    ArraySize,

    Never,
    None,
}

impl Type {
    fn is_never(&self) -> bool {
        matches!(self, Type::Never)
    }
    fn from_type(asys: &Analysis, typ: &parser::Type) -> Type {
        match asys.values[typ.ident] {
            STR => Type::Aggregate(SLICE),
            INT => Type::Int,
            _ => panic!("unknown type"),
        }
    }
    fn from_return(asys: &Analysis, typ: Option<&parser::ReturnType>) -> Type {
        match typ {
            Some(parser::ReturnType::Type(t)) => Type::from_type(asys, t),
            Some(parser::ReturnType::Never) => Type::Never,
            None => Type::None,
        }
    }
    fn into_result(self, ir: &mut IRContext) -> ExprResult {
        match self {
            Type::Never => Err(Never),
            Type::None => Ok(None),
            _ => Ok(Some(ir.next_reg(self))),
        }
    }
    fn from_result(result: ExprResult, ir: &IRContext) -> Self {
        match result {
            Ok(Some(reg)) => ir.ir.regs[reg],
            Ok(None) => Type::None,
            Err(Never) => Type::Never,
        }
    }
}

#[derive(Default)]
pub struct AggregateType {
    pub children: Vec<Type>,
}

impl Procedure {
    fn instructions(&self) -> impl Iterator<Item = &Instruction> {
        self.blocks.values().flat_map(|b| b.instructions.iter())
    }
    fn calls(&self) -> impl Iterator<Item = ProcIdx> + '_ {
        self.instructions().filter_map(|i| match *i {
            Instruction::Reset(p, _, _, _) | Instruction::Call(p, _, _) => Some(p),
            _ => None,
        })
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
    Div(Reg, Reg, Reg),
    Mul(Reg, Reg, Reg),
    Add(Reg, Reg, Reg),
    Sub(Reg, Reg, Reg),

    // call procedure, put return into reg, call with arguments
    Reset(ProcIdx, Option<Reg>, Vec<Reg>, HandlerIdx), // catch any breaks to handler
    Call(ProcIdx, Option<Reg>, Vec<Reg>),              // regular call

    // return statements
    Break(Option<Reg>, HandlerIdx), // break with optional value to handler
    Return(Option<Reg>),            // return with optional value
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
    procs: VecMap<EffFunIdx, ProcIdx>,
    global: bool,
}

#[derive(Default)]
struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    regs: HashMap<Val, Either<Reg, Global>>,
    captures: Vec<(Val, Reg)>,
}

impl<'a> Scope<'a> {
    fn get_parent(&self, key: Val) -> Option<Either<Reg, Global>> {
        match self.regs.get(&key) {
            Some(&v) => Some(v),
            _ => self.parent.map(|p| p.get_parent(key)).flatten(),
        }
    }
    fn get_or_capture(
        &mut self,
        ir: &mut IRContext,
        instr: &mut Vec<Instruction>,
        key: Val,
    ) -> Option<Reg> {
        let either = match self.regs.get(&key) {
            Some(&v) => Some(v),
            None => match self.parent.map(|p| p.get_parent(key)).flatten() {
                Some(Either::Right(glob)) => Some(Either::Right(glob)),
                Some(Either::Left(reg)) => {
                    let pos = self.captures.iter().position(|&(k, _)| k == key);
                    if let Some(pos) = pos {
                        Some(Either::Left(self.captures[pos].1))
                    } else {
                        let capture = ir.copy_reg(reg);
                        self.captures.push((key, capture));
                        Some(Either::Left(capture))
                    }
                }
                None => None,
            },
        }?;
        match either {
            Either::Left(reg) => Some(reg),
            Either::Right(glob) => {
                let reg = ir.next_reg(ir.ir.globals[glob]);
                instr.push(Instruction::GetGlobal(reg, glob));
                Some(reg)
            }
        }
    }
    fn child(&self) -> Scope {
        Scope {
            parent: Some(self),
            regs: HashMap::new(),
            captures: Vec::new(),
        }
    }
}

struct IRContext<'a> {
    ir: IR,

    proc_map: HashMap<ProcIdent, ProcIdx>,
    handlers: VecMap<HandlerIdx, Handler>,
    implied_handlers: Vec<HandlerIdx>,

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
    fn break_union(&self, handlers: &[HandlerIdx]) -> Vec<Type> {
        let mut union = Vec::new();
        for handler in handlers.into_iter().copied() {
            for proc in self.handlers[handler].procs.values().copied() {
                for t in self.ir.procs[proc].output.break_union.iter().copied() {
                    if !union.contains(&t) {
                        union.push(t);
                    }
                }
            }
        }
        union
    }
}

pub struct IR {
    pub procs: VecMap<ProcIdx, Procedure>,
    pub recursive: VecMap<ProcIdx, bool>,

    pub main: ProcIdx,

    pub regs: VecMap<Reg, Type>,
    pub globals: VecMap<Global, Type>,

    pub aggregates: VecMap<TypeIdx, AggregateType>,
}

impl Display for VecMap<ProcIdx, Procedure> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for proc in self.values() {
            // write proc signature
            write!(f, "{}", proc.debug_name)?;

            if proc.inputs.len() > 0 {
                write!(f, " ( ")?;
                for &r in proc.inputs.iter() {
                    if r != *proc.inputs.first().unwrap() {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", r)?;
                }
                write!(f, " )")?;
            }

            write!(f, " {{\n")?;

            // write blocks
            for (i, block) in proc.blocks.values().enumerate() {
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
                            self[proc].debug_name,
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
                        Instruction::Reset(proc, out, ref args, handler) => writeln!(
                            f,
                            "{}rst {}, {}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            usize::from(handler),
                            self[proc].debug_name,
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
                        Instruction::Break(r, h) => writeln!(
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

const SLICE: TypeIdx = TypeIdx(0);

pub fn generate_ir(ast: &AST, ctx: &ParseContext, asys: &Analysis) -> IR {
    let mut ir = IRContext {
        proc_map: HashMap::new(),
        handlers: VecMap::new(),
        implied_handlers: Vec::new(),
        ast,
        ctx,
        asys,
        ir: IR {
            procs: VecMap::new(),
            recursive: VecMap::new(),

            main: ProcIdx(0),

            regs: VecMap::new(),
            globals: VecMap::new(),
            aggregates: VecMap::new(),
        },
    };

    ir.ir.aggregates.push_value(AggregateType {
        children: vec![Type::BytePointer, Type::ArraySize],
    });

    // define putint
    let debug_closure = ir.ir.aggregates.push(TypeIdx, AggregateType::default());

    let inputs = vec![ir.next_reg(Type::Int)];

    let putint = ir.ir.procs.push(
        ProcIdx,
        Procedure {
            inputs,

            output: ReturnType {
                output: Type::None,
                implicit_break: None,
                break_union: Vec::new(),
            },

            blocks: vec![Block {
                instructions: vec![Instruction::PrintNum(Reg(0)), Instruction::Return(None)],
                next: None,
            }]
            .into(),
            start: BlockIdx(0),
            debug_name: "putint".into(),
        },
    );

    // define debug
    let debug = ir.handlers.push(
        HandlerIdx,
        Handler {
            effect: DEBUG,
            procs: vec![putint].into(),
            closure: debug_closure,
            global: true,
        },
    );

    // generate implied handlers
    for expr in ast.implied.iter().copied() {
        // TODO: first class handlers
        let Expression::Handler(ast_handler) = &ctx.exprs[expr].0 else { panic!() };

        // get effect
        let eff_ident = ast_handler.effect;
        let eff_val = ir.asys.values[eff_ident];
        let eff_idx = match ir.asys.defs[eff_val] {
            Definition::Effect(eff_idx) => eff_idx,
            _ => panic!("handler has non-effect as effect value"),
        };
        let effect = &ir.ast.effects[eff_idx];

        // generate handler
        let closure = ir.ir.aggregates.push(TypeIdx, AggregateType::default());
        let handler_idx = ir.handlers.push(
            HandlerIdx,
            Handler {
                effect: eff_val,
                closure,
                procs: VecMap::filled(effect.functions.len(), ProcIdx(usize::MAX)),
                global: true,
            },
        );

        for fun in ast_handler.functions.iter() {
            let val = ir.asys.values[fun.decl.name];
            let eff_fun_idx = match ir.asys.defs[val] {
                Definition::EffectFunction(_, eff_fun_idx) => eff_fun_idx,
                _ => panic!("handler has non-effect-function as a function value"),
            };

            // get params
            let params: Vec<(Val, Type)> = fun
                .decl
                .sign
                .inputs
                .values()
                .map(|&(ident, ref typ)| (ir.asys.values[ident], Type::from_type(&ir.asys, typ)))
                .collect();

            let output = Type::from_return(&ir.asys, fun.decl.sign.output.as_ref());

            // generate debug name
            let eff_name = ir.ctx.idents[eff_ident].0.as_str();
            let proc_name = ir.ctx.idents[fun.decl.name].0.as_str();
            let debug_name = format!("{}#{}__{}", eff_name, usize::from(handler_idx), proc_name);
            // TODO: add handlers of proc

            // generate handler proc
            let proc_idx = generate_fun(
                &mut ir,
                None,
                &[], // TODO: add handlers of proc
                &params,
                fun.body,
                output,
                Some(handler_idx),
                debug_name,
                &mut Scope::default(),
            );

            // check if handler can break
            let can_break = ir.ir.procs[proc_idx]
                .instructions()
                .any(|instr| matches!(instr, Instruction::Break(_, _)));

            let proc = &mut ir.ir.procs[proc_idx];
            proc.output.implicit_break = Some(handler_idx);

            let break_type = match &ast_handler.break_type {
                Some(parser::ReturnType::Type(t)) => Some(Type::from_type(asys, t)),
                Some(parser::ReturnType::Never) => None,
                None => {
                    if can_break {
                        Some(Type::None)
                    } else {
                        None
                    }
                }
            };
            if let Some(break_type) = break_type {
                if !proc.output.break_union.contains(&break_type) {
                    proc.output.break_union.push(break_type);
                }
            }

            // add to handler
            ir.handlers[handler_idx].procs[eff_fun_idx] = proc_idx;
        }

        // add handler to implied
        ir.implied_handlers.push(handler_idx);
    }

    // generate
    // TODO: main not found
    let main = asys.main.expect("no main function");
    let fun = &ir.ast.functions[main];
    let val = ir.asys.values[fun.decl.name];

    let params: Box<[(Val, Type)]> = fun
        .decl
        .sign
        .inputs
        .values()
        .map(|&(ident, ref typ)| (ir.asys.values[ident], Type::from_type(&ir.asys, typ)))
        .collect();

    let output = Type::from_return(&ir.asys, fun.decl.sign.output.as_ref());

    let debug_glob = ir.ir.globals.push(Global, Type::Aggregate(debug_closure));
    let mut scope = Scope::default();
    scope.regs.insert(DEBUG, Either::Right(debug_glob));

    ir.ir.main = generate_fun(
        &mut ir,
        Some(val),
        &[debug],
        &params,
        fun.body,
        output,
        None,
        "main".into(),
        &mut scope,
    );

    // get recursive functions
    ir.ir.recursive = VecMap::filled(ir.ir.procs.len(), false);
    find_recursive_funs(&ir.ir.procs, &mut vec![ir.ir.main], &mut ir.ir.recursive);

    // return ir
    ir.ir
}

fn find_recursive_funs(
    procs: &VecMap<ProcIdx, Procedure>,
    dfs: &mut Vec<ProcIdx>,
    recursive: &mut VecMap<ProcIdx, bool>,
) {
    let last = dfs.last().copied().unwrap();

    for call in procs[last].calls() {
        if let Some(pos) = dfs.iter().position(|&p| p == call) {
            // we found a cycle, set all in cycle to be recursive
            for &p in dfs[pos..].iter() {
                recursive[p] = true;
            }
        } else {
            // no cycle yet, search further
            dfs.push(call);
            find_recursive_funs(procs, dfs, recursive);
            dfs.pop();
        }
    }
}

fn generate_fun(
    ir: &mut IRContext,
    fun: Option<Val>,
    handlers: &[HandlerIdx],
    params: &[(Val, Type)],
    body: ExprIdx,
    output: Type,
    handler: Option<HandlerIdx>,
    debug_name: String,
    scope: &mut Scope,
) -> ProcIdx {
    // add new proc to list
    let mut blocks = VecMap::new();
    let start = blocks.push(BlockIdx, Block::default());

    let proc_idx = ir.ir.procs.push(
        ProcIdx,
        Procedure {
            inputs: Vec::new(),
            output: ReturnType {
                output,
                implicit_break: None,
                break_union: ir.break_union(handlers),
            },
            start,
            debug_name: debug_name.clone(),

            // these will be defined at the end
            blocks: VecMap::new(),
        },
    );

    if let Some(fun) = fun {
        let ident = ProcIdent {
            fun,
            handlers: handlers.into(),
        };
        ir.proc_map.insert(ident, proc_idx);
    }

    // add params to vars
    for &(val, typ) in params {
        let reg = ir.next_reg(typ);
        scope.regs.insert(val, Either::Left(reg));
        ir.ir.procs[proc_idx].inputs.push(reg);
    }

    // generate code
    let mut end = start;
    let ret = generate_expr(
        ir,
        handlers,
        body,
        &mut blocks,
        &mut end,
        handler,
        &debug_name,
        scope,
    );

    if let Ok(ret) = ret {
        if !matches!(
            blocks[end].instructions.last(),
            Some(Instruction::Return(_) | Instruction::Break(_, _))
        ) {
            // add return if we haven't already
            blocks[end].instructions.push(Instruction::Return(ret));
        }
    }

    // return proc
    ir.ir.procs[proc_idx].blocks = blocks;
    proc_idx
}

fn generate_reset(
    ir: &mut IRContext,
    handlers: &[HandlerIdx],
    body: ExprIdx,
    debug_name: String,
    scope: &mut Scope,
) -> ProcIdx {
    // create blocks
    let mut blocks = VecMap::new();
    let start = blocks.push(BlockIdx, Block::default());

    // generate code
    let mut end = start;
    let ret = generate_expr(
        ir,
        handlers,
        body,
        &mut blocks,
        &mut end,
        None,
        &debug_name,
        scope,
    );

    if let Ok(ret) = ret {
        if !matches!(
            blocks[end].instructions.last(),
            Some(Instruction::Return(_) | Instruction::Break(_, _))
        ) {
            // add return if we haven't already
            blocks[end].instructions.push(Instruction::Return(ret));
        }
    }

    let output = Type::from_result(ret, ir);

    // return proc
    ir.ir.procs.push(
        ProcIdx,
        Procedure {
            inputs: scope.captures.iter().map(|&(_, v)| v).collect(),
            output: ReturnType {
                output,
                implicit_break: None,
                break_union: ir.break_union(handlers),
            },
            start,
            debug_name,
            blocks,
        },
    )
}

#[derive(Clone, Copy)]
struct Never;
type ExprResult = Result<Option<Reg>, Never>;

fn generate_expr(
    ir: &mut IRContext,
    handlers: &[HandlerIdx],
    expr: ExprIdx,
    blocks: &mut VecMap<BlockIdx, Block>,
    block: &mut BlockIdx,
    handler: Option<HandlerIdx>,
    debug_name: &str,
    scope: &mut Scope,
) -> ExprResult {
    use Expression as E;
    match ir.ctx.exprs[expr].0 {
        E::Body(ref body) => {
            for &expr in body.main.iter() {
                generate_expr(
                    ir, handlers, expr, blocks, block, handler, debug_name, scope,
                )?;
            }
            body.last
                .map(|expr| {
                    generate_expr(
                        ir, handlers, expr, blocks, block, handler, debug_name, scope,
                    )
                })
                .unwrap_or(Ok(None))
        }
        E::Call(func, ref args) => {
            // TODO: currently we assume func is an Ident expr or Effect Member expr
            match ir.ctx.exprs[func].0 {
                E::Ident(id) | E::Member(_, id) => {
                    let val = ir.asys.values[id];

                    // get base registers
                    let mut reg_args = args
                        .iter()
                        .map(|&expr| {
                            generate_expr(
                                ir, handlers, expr, blocks, block, handler, debug_name, scope,
                            )
                            .map(|r| r.expect("call argument does not return a value"))
                        })
                        .collect::<Result<Vec<_>, _>>()?;

                    // check handlers
                    match ir.asys.defs[val] {
                        Definition::EffectFunction(eff_val, eff_fun_idx) => {
                            // get handler
                            let handler = handlers
                                .iter()
                                .chain(ir.implied_handlers.iter())
                                .map(|&idx| &ir.handlers[idx])
                                .find(|handler| handler.effect == eff_val)
                                .expect("handler of effect function is not in scope");
                            let global = handler.global;

                            let proc_idx = handler.procs[eff_fun_idx];

                            let typ = ir.ir.procs[proc_idx].output.output;
                            let output = typ.into_result(ir);

                            // get closure
                            if !global {
                                let closure = scope
                                    .get_or_capture(ir, &mut blocks[*block].instructions, eff_val)
                                    .expect("handler closure is not in scope");
                                reg_args.push(closure);
                            }

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
                        Definition::Function(func_idx) => {
                            // create proc identity
                            let fun = &ir.ast.functions[func_idx];

                            let effects: Box<[HandlerIdx]> = fun
                                .decl
                                .sign
                                .effects
                                .iter()
                                .map(|&e| {
                                    let effect = ir.asys.values[e];
                                    handlers
                                        .iter()
                                        .find(|&&h| ir.handlers[h].effect == effect)
                                        .unwrap()
                                        .clone()
                                })
                                .collect();

                            let procident = ProcIdent {
                                fun: val,
                                handlers: effects,
                            };

                            reg_args.extend(procident.handlers.iter().filter_map(|&idx| {
                                match ir.handlers[idx].global {
                                    true => None,
                                    false => Some(
                                        scope
                                            .get_or_capture(
                                                ir,
                                                &mut blocks[*block].instructions,
                                                ir.handlers[idx].effect,
                                            )
                                            .expect("handler closure not in scope"),
                                    ),
                                }
                            }));

                            // get proc
                            let proc_idx = if !ir.proc_map.contains_key(&procident) {
                                let handlers = &procident.handlers;

                                // get params
                                let mut params: Vec<(Val, Type)> = fun
                                    .decl
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|&(ident, ref typ)| {
                                        (ir.asys.values[ident], Type::from_type(&ir.asys, typ))
                                    })
                                    .collect();

                                params.extend(procident.handlers.iter().filter_map(|&idx| {
                                    match ir.handlers[idx].global {
                                        true => None,
                                        false => Some((
                                            ir.handlers[idx].effect,
                                            Type::Aggregate(ir.handlers[idx].closure),
                                        )),
                                    }
                                }));

                                let output =
                                    Type::from_return(&ir.asys, fun.decl.sign.output.as_ref());

                                // generate debug name
                                let mut debug_name = ir.ctx.idents[fun.decl.name].0.clone();

                                if handlers.len() > 0 {
                                    debug_name += "/";

                                    for &handler in handlers.iter() {
                                        let eff_val = ir.handlers[handler].effect;
                                        let eff_name = ir
                                            .ast
                                            .effects
                                            .values()
                                            .find(|e| ir.asys.values[e.name] == eff_val)
                                            .map(|e| ir.ctx.idents[e.name].0.as_str())
                                            .unwrap_or("debug"); // TODO: support other builtin effects

                                        debug_name += eff_name;
                                        debug_name += "#";
                                        debug_name += usize::from(handler).to_string().as_str();
                                        debug_name += "_";
                                    }

                                    debug_name.pop();
                                }

                                // generate func
                                let mut child = scope.child();
                                generate_fun(
                                    ir,
                                    Some(val),
                                    handlers,
                                    &params,
                                    fun.body,
                                    output,
                                    None,
                                    debug_name,
                                    &mut child,
                                )
                            } else {
                                ir.proc_map[&procident]
                            };
                            let proc = &ir.ir.procs[proc_idx];
                            let never = proc.output.output.is_never();

                            // execute proc
                            let output = proc.output.output.into_result(ir);

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

                        Definition::Parameter(_, _) => todo!(),
                        Definition::Effect(_) => todo!(),
                        Definition::Builtin => todo!(),
                    }
                }
                _ => todo!(),
            }
        }
        E::Member(_, _) => todo!(),
        E::IfElse(cond, yes, no) => {
            let cond = generate_expr(
                ir, handlers, cond, blocks, block, handler, debug_name, scope,
            )?
            .expect("condition has no value");

            match no {
                Some(no) => {
                    let no_start = blocks.push(BlockIdx, Block::default());

                    let mut no_end = no_start;
                    let no_reg = generate_expr(
                        ir,
                        handlers,
                        no,
                        blocks,
                        &mut no_end,
                        handler,
                        debug_name,
                        scope,
                    );

                    let yes_start = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, no_start));

                    let mut yes_end = yes_start;
                    let yes_reg = generate_expr(
                        ir,
                        handlers,
                        yes,
                        blocks,
                        &mut yes_end,
                        handler,
                        debug_name,
                        scope,
                    );

                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block].next = Some(no_start);
                    blocks[yes_end].next = Some(end);
                    blocks[no_end].next = Some(end);
                    *block = end;

                    if let (Ok(Some(yes)), Ok(Some(no))) = (yes_reg, no_reg) {
                        if ir.ir.regs[yes] == ir.ir.regs[no] {
                            let out = ir.copy_reg(yes);
                            blocks[*block]
                                .instructions
                                .push(Instruction::Phi(out, [(yes, yes_end), (no, no_end)]));
                            Ok(Some(out))
                        } else {
                            Ok(None)
                        }
                    } else if let (Err(Never), Err(Never)) = (yes_reg, no_reg) {
                        Err(Never)
                    } else {
                        Ok(None)
                    }
                }
                None => {
                    let yes_start = blocks.push(BlockIdx, Block::default());

                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::Branch(cond, yes_start, end));

                    let mut yes_end = yes_start;
                    let _ = generate_expr(
                        ir,
                        handlers,
                        yes,
                        blocks,
                        &mut yes_end,
                        handler,
                        debug_name,
                        scope,
                    );

                    blocks[*block].next = Some(end);
                    blocks[yes_end].next = Some(end);
                    *block = end;

                    Ok(None)
                }
            }
        }
        E::Op(left, op, right) => {
            let left = generate_expr(
                ir, handlers, left, blocks, block, handler, debug_name, scope,
            )?
            .expect("left operand has no value");

            let right = generate_expr(
                ir, handlers, right, blocks, block, handler, debug_name, scope,
            )?
            .expect("right operand has no value");

            // TODO: ops with different return types
            let out = ir.next_reg(Type::Int);

            let instr = match op {
                Op::Equals => Instruction::Equals(out, left, right),
                Op::Divide => Instruction::Div(out, left, right),
                Op::Multiply => Instruction::Mul(out, left, right),
                Op::Subtract => Instruction::Sub(out, left, right),
                Op::Add => Instruction::Add(out, left, right),
            };
            blocks[*block].instructions.push(instr);

            Ok(Some(out))
        }
        E::Break(value) => {
            // get break value
            let reg = value
                .map(|expr| {
                    generate_expr(
                        ir, handlers, expr, blocks, block, handler, debug_name, scope,
                    )
                })
                .unwrap_or(Ok(None))?;

            // TODO: we assume this is top level inside a handler
            blocks[*block]
                .instructions
                .push(Instruction::Break(reg, handler.unwrap()));

            // break returns any type
            Err(Never)
        }
        E::TryWith(body, handler) => {
            // get handler
            let ast_handler = match ir.ctx.exprs[handler].0 {
                E::Handler(ref handler) => handler,
                _ => todo!(),
            };

            // get effect
            let eff_ident = ast_handler.effect;
            let eff_val = ir.asys.values[eff_ident];
            let eff_idx = match ir.asys.defs[eff_val] {
                Definition::Effect(eff_idx) => eff_idx,
                _ => panic!("handler has non-effect as effect value"),
            };
            let effect = &ir.ast.effects[eff_idx];

            // generate handler
            let closure = ir.ir.aggregates.push(TypeIdx, AggregateType::default());
            let closure_reg = ir.next_reg(Type::Aggregate(closure));

            let global = true; // TODO: this is for testing, should be false by default

            if global {
                let glob = ir.ir.globals.push(Global, Type::Aggregate(closure));
                scope.regs.insert(eff_val, Either::Right(glob));
            } else {
                scope.regs.insert(eff_val, Either::Left(closure_reg));
            }

            // generate handler
            let handler_idx = ir.handlers.push(
                HandlerIdx,
                Handler {
                    closure,
                    effect: eff_val,
                    procs: VecMap::filled(effect.functions.len(), ProcIdx(usize::MAX)),
                    global,
                },
            );

            let mut break_self = false;

            let mut child = scope.child();
            for fun in ast_handler.functions.iter() {
                let val = ir.asys.values[fun.decl.name];
                let eff_fun_idx = match ir.asys.defs[val] {
                    Definition::EffectFunction(_, eff_fun_idx) => eff_fun_idx,
                    _ => panic!("handler has non-effect-function as a function value"),
                };

                // get params
                let mut params: Vec<(Val, Type)> = fun
                    .decl
                    .sign
                    .inputs
                    .values()
                    .map(|&(ident, ref typ)| {
                        (ir.asys.values[ident], Type::from_type(&ir.asys, typ))
                    })
                    .collect();

                if !global {
                    params.push((val, Type::Aggregate(closure)));
                }

                let output = Type::from_return(&ir.asys, fun.decl.sign.output.as_ref());

                // generate debug name
                let eff_name = ir.ctx.idents[eff_ident].0.as_str();
                let proc_name = ir.ctx.idents[fun.decl.name].0.as_str();
                let debug_name =
                    format!("{}#{}__{}", eff_name, usize::from(handler_idx), proc_name);
                // TODO: add handlers of proc

                // generate handler proc
                let proc_idx = generate_fun(
                    ir,
                    None,
                    handlers, // TODO: add handlers of proc
                    &params,
                    fun.body,
                    output,
                    Some(handler_idx),
                    debug_name,
                    &mut child,
                );

                // check if handler can break
                let can_break = ir.ir.procs[proc_idx]
                    .instructions()
                    .any(|instr| matches!(instr, Instruction::Break(_, _)));
                if can_break {
                    break_self = true;
                }

                let proc = &mut ir.ir.procs[proc_idx];

                // TODO: infer break type
                let break_type = match &ast_handler.break_type {
                    Some(parser::ReturnType::Type(t)) => Some(Type::from_type(ir.asys, &t)),
                    Some(parser::ReturnType::Never) => None,
                    None => {
                        if can_break {
                            Some(Type::None)
                        } else {
                            None
                        }
                    }
                };
                if let Some(break_type) = break_type {
                    if !proc.output.break_union.contains(&break_type) {
                        proc.output.break_union.push(break_type);
                    }
                }

                // get captures
                let (param, offset) = match global {
                    true => {
                        let glob = scope.regs[&eff_val].unwrap_right();
                        let reg = ir.ir.regs.push(Reg, ir.ir.globals[glob]);
                        proc.blocks[proc.start]
                            .instructions
                            .insert(0, Instruction::GetGlobal(reg, glob));
                        (reg, 1)
                    }
                    false => {
                        let reg = proc.inputs.last().copied().unwrap();
                        (reg, 0)
                    }
                };
                for (i, capture) in child.captures.iter().map(|&(_, v)| v).enumerate() {
                    proc.blocks[proc.start]
                        .instructions
                        .insert(i + offset, Instruction::Member(capture, param, i))
                }

                // add to handler
                ir.handlers[handler_idx].procs[eff_fun_idx] = proc_idx;
            }

            // create handler closure
            ir.ir.aggregates[closure]
                .children
                .extend(child.captures.iter().map(|&(_, reg)| ir.ir.regs[reg]));

            let aggregate = child
                .captures
                .iter()
                .map(|&(val, _)| {
                    scope
                        .get_or_capture(ir, &mut blocks[*block].instructions, val)
                        .expect("value not in scope")
                })
                .collect();

            blocks[*block]
                .instructions
                .push(Instruction::Aggregate(closure_reg, aggregate));

            // add handler to handler list
            let mut subhandlers = Vec::new();
            subhandlers.extend_from_slice(handlers);

            match subhandlers
                .iter()
                .position(|&idx| ir.handlers[idx].effect == eff_val)
            {
                Some(pos) => {
                    // replace existing handler
                    subhandlers[pos] = handler_idx;
                }
                None => {
                    // push new handler
                    subhandlers.push(handler_idx);
                }
            }

            // generate reset
            let debug_name = format!("{}__reset#{}", debug_name, usize::from(handler_idx));

            let mut child = scope.child();
            let proc_idx = generate_reset(ir, &subhandlers, body, debug_name, &mut child);

            let input_regs: Vec<Reg> = child
                .captures
                .iter()
                .map(|&(val, _)| {
                    scope
                        .get_or_capture(ir, &mut blocks[*block].instructions, val)
                        .expect("value not in scope")
                })
                .collect();

            let proc = &ir.ir.procs[proc_idx];
            let never = proc.output.output.is_never();

            // execute proc
            let output = proc.output.output.into_result(ir);

            if global {
                let next = blocks.push(BlockIdx, Block::default());

                let glob = scope.regs[&eff_val].unwrap_right();
                blocks[*block]
                    .instructions
                    .push(Instruction::SetScopedGlobal(glob, closure_reg, next));

                if break_self {
                    blocks[*block].instructions.push(Instruction::Reset(
                        proc_idx,
                        output.unwrap_or(None),
                        input_regs,
                        handler_idx,
                    ));
                } else {
                    // TODO: inline call?
                    blocks[*block].instructions.push(Instruction::Call(
                        proc_idx,
                        output.unwrap_or(None),
                        input_regs,
                    ));
                }

                blocks[*block].next = Some(next);
                *block = next;
            } else {
                if break_self {
                    blocks[*block].instructions.push(Instruction::Reset(
                        proc_idx,
                        output.unwrap_or(None),
                        input_regs,
                        handler_idx,
                    ));
                } else {
                    // TODO: inline call?
                    blocks[*block].instructions.push(Instruction::Call(
                        proc_idx,
                        output.unwrap_or(None),
                        input_regs,
                    ));
                }
            }

            if never {
                blocks[*block].instructions.push(Instruction::Unreachable);
            }
            output
        }
        E::Handler(_) => todo!(),
        E::String(ref s) => {
            let reg = ir.next_reg(Type::Aggregate(SLICE));

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
            let reg = scope
                .get_or_capture(ir, &mut blocks[*block].instructions, val)
                .expect("value is not loaded in scope");
            Ok(Some(reg))
        }
        E::Error => unreachable!(),
    }
}
