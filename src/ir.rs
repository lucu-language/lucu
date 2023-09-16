use std::{
    collections::HashMap,
    fmt::{self, Display},
    mem::{self, MaybeUninit},
    write,
};

use crate::{
    analyzer::{Analysis, Definition, EffFunIdx, FunIdx, Val, DEBUG},
    parser::{ExprIdx, Expression, Op, ParseContext, AST},
    vecmap::VecMap,
};

#[derive(Debug)]
pub struct Procedure {
    pub inputs: usize,

    // extra values from the parent function(s) to use as inputs
    // TODO: is Val accurate enough or will this take the wrong value during recursion?
    pub closure_inputs: Vec<Val>,

    // whether or not this is an effect handler that accepts a continuation parameter
    pub is_handler: bool,

    // TODO: add never return type in the IR
    pub outputs: bool,
    pub blocks: VecMap<BlockIdx, Block>,
    pub start: BlockIdx,

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
pub struct Reg(usize);

impl From<Reg> for usize {
    fn from(value: Reg) -> Self {
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
    Copy(Reg, Reg),

    // conditionals
    JmpNZ(Reg, BlockIdx),
    Phi(Reg, [(Reg, BlockIdx); 2]),

    // operations (r0 = r1 op r2)
    Equals(Reg, Reg, Reg),
    Div(Reg, Reg, Reg),
    Mul(Reg, Reg, Reg),
    Add(Reg, Reg, Reg),

    // call procedure, put return into reg, call with arguments
    Reset(ProcIdx, Option<Reg>, Vec<Reg>, Reg), // puts frame parameter into reg and calls
    Shift(ProcIdx, Option<Reg>, Vec<Reg>, Reg), // shift into procedure with frame parameter
    Call(ProcIdx, Option<Reg>, Vec<Reg>),       // regular call

    // return statements for effect handlers
    Resume(Option<Reg>),  // resume the continuation with optional value
    Discard(Option<Reg>), // discard the continuation and return with optional value

    // return statement for regular procedures
    Return(Option<Reg>), // return with optional value

    PrintNum(Reg), // print number in register
    PrintStr(Reg), // dereference register and print string
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ProcIdx(usize);

impl From<ProcIdx> for usize {
    fn from(value: ProcIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct HandlerIdx(usize);

impl From<HandlerIdx> for usize {
    fn from(value: HandlerIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct ProcIdent {
    func: Val,
    handlers: Box<[HandlerIdx]>,
}

#[derive(Debug)]
struct Handler {
    effect: Val,
    procs: VecMap<EffFunIdx, ProcIdx>,
}

struct IR<'a> {
    procs: VecMap<ProcIdx, Procedure>,
    proc_map: HashMap<ProcIdent, ProcIdx>,
    handlers: VecMap<HandlerIdx, Handler>,

    ast: &'a AST,
    ctx: &'a ParseContext,
    asys: &'a Analysis,
}

#[derive(Default)]
struct ClosureScope {
    parent: Option<Box<ClosureScope>>,
    vars: HashMap<Val, Reg>,

    base_params: usize,
    extra_inputs: Vec<Val>, // extra values from the parent function(s) to use as inputs
}

impl ClosureScope {
    fn find_reg(&mut self, val: Val) -> Option<Reg> {
        self.vars.get(&val).cloned().or_else(|| {
            self.parent
                .as_mut()
                .and_then(|parent| parent.find_reg(val))
                .map(|_| {
                    let reg = Reg(self.base_params + self.extra_inputs.len());
                    self.extra_inputs.push(val);
                    self.vars.insert(val, reg);
                    reg
                })
        })
    }
    fn child(me: &mut Box<Self>) {
        unsafe {
            #[allow(invalid_value)]
            let inner = mem::replace(me, MaybeUninit::uninit().assume_init());
            let child = ClosureScope {
                parent: Some(inner),
                vars: HashMap::new(),
                base_params: 0,
                extra_inputs: Vec::new(),
            };

            let uninit = mem::replace(me, Box::new(child));
            mem::forget(uninit);
        }
    }
    fn parent(me: &mut Box<Self>) -> Vec<Val> {
        unsafe {
            #[allow(invalid_value)]
            let inner = mem::replace(me, MaybeUninit::uninit().assume_init());

            let uninit = mem::replace(me, inner.parent.unwrap());
            mem::forget(uninit);

            inner.extra_inputs
        }
    }
}

impl Display for VecMap<ProcIdx, Procedure> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for proc in self.values() {
            // write proc signature
            write!(f, "{}(", proc.debug_name)?;
            let params = proc.inputs + proc.closure_inputs.len();

            for i in 0..params {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "R{}", i)?;
            }

            if proc.is_handler {
                if params > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "resume")?;
            }

            write!(f, ") {{\n")?;

            // write blocks
            for (i, block) in proc.blocks.values().enumerate() {
                // write label
                if i > 0 {
                    writeln!(f, "L{}:", i)?;
                }

                // write instructions
                for instr in block.instructions.iter() {
                    write!(f, "  ")?;
                    match *instr {
                        Instruction::Init(r, v) => writeln!(f, "R{} <- {}", usize::from(r), v)?,
                        Instruction::Copy(r, v) => {
                            writeln!(f, "R{} <- R{}", usize::from(r), usize::from(v))?
                        }
                        Instruction::JmpNZ(r, b) => {
                            writeln!(f, "       jnz R{}, L{}", usize::from(r), usize::from(b))?
                        }
                        Instruction::Phi(r, [(r1, b1), (r2, b2)]) => writeln!(
                            f,
                            "R{} <- phi [ R{}, L{} ], [ R{}, L{} ]",
                            usize::from(r),
                            usize::from(r1),
                            usize::from(b1),
                            usize::from(r2),
                            usize::from(b2),
                        )?,
                        Instruction::Equals(out, left, right) => writeln!(
                            f,
                            "R{} <- R{} == R{}",
                            usize::from(out),
                            usize::from(left),
                            usize::from(right)
                        )?,
                        Instruction::Div(out, left, right) => writeln!(
                            f,
                            "R{} <- R{} / R{}",
                            usize::from(out),
                            usize::from(left),
                            usize::from(right)
                        )?,
                        Instruction::Mul(out, left, right) => writeln!(
                            f,
                            "R{} <- R{} * R{}",
                            usize::from(out),
                            usize::from(left),
                            usize::from(right)
                        )?,
                        Instruction::Add(out, left, right) => writeln!(
                            f,
                            "R{} <- R{} + R{}",
                            usize::from(out),
                            usize::from(left),
                            usize::from(right)
                        )?,
                        Instruction::Reset(proc, out, ref args, frame) => writeln!(
                            f,
                            "{}rst {}, R{}, [ {} ]",
                            out.map(|r| format!("R{} <- ", usize::from(r)))
                                .unwrap_or("       ".into()),
                            self[proc].debug_name,
                            usize::from(frame),
                            args.iter()
                                .map(|&r| format!("R{}", usize::from(r)))
                                .collect::<Vec<_>>()
                                .join(", "),
                        )?,
                        Instruction::Shift(proc, out, ref args, frame) => writeln!(
                            f,
                            "{}sft {}, R{}, [ {} ]",
                            out.map(|r| format!("R{} <- ", usize::from(r)))
                                .unwrap_or("       ".into()),
                            self[proc].debug_name,
                            usize::from(frame),
                            args.iter()
                                .map(|&r| format!("R{}", usize::from(r)))
                                .collect::<Vec<_>>()
                                .join(", "),
                        )?,
                        Instruction::Call(proc, out, ref args) => writeln!(
                            f,
                            "{}cal {}, [ {} ]",
                            out.map(|r| format!("R{} <- ", usize::from(r)))
                                .unwrap_or("       ".into()),
                            self[proc].debug_name,
                            args.iter()
                                .map(|&r| format!("R{}", usize::from(r)))
                                .collect::<Vec<_>>()
                                .join(", "),
                        )?,
                        Instruction::Resume(r) => match r {
                            Some(r) => writeln!(f, "       res R{}", usize::from(r))?,
                            None => writeln!(f, "       res")?,
                        },
                        Instruction::Discard(r) | Instruction::Return(r) => match r {
                            Some(r) => writeln!(f, "       ret R{}", usize::from(r))?,
                            None => writeln!(f, "       ret")?,
                        },
                        Instruction::PrintNum(r) => writeln!(f, "       put R{}", usize::from(r))?,

                        Instruction::PrintStr(_) => todo!(),
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

pub fn generate_ir(
    ast: &AST,
    ctx: &ParseContext,
    asys: &Analysis,
) -> (VecMap<ProcIdx, Procedure>, ProcIdx) {
    // TODO: main not found
    let main = asys.main.unwrap();

    let mut ir = IR {
        procs: VecMap::new(),
        proc_map: HashMap::new(),
        handlers: VecMap::new(),
        ast,
        ctx,
        asys,
    };

    // define putint
    let putint = ir.procs.push(
        ProcIdx,
        Procedure {
            inputs: 1, // int
            closure_inputs: Vec::new(),

            is_handler: false,
            outputs: false,

            blocks: vec![Block {
                instructions: vec![Instruction::PrintNum(Reg(0)), Instruction::Return(None)],
                next: None,
            }]
            .into(),
            start: BlockIdx(0),
            debug_name: "debug#0__putint".into(),
        },
    );

    // define debug
    let debug = ir.handlers.push(
        HandlerIdx,
        Handler {
            effect: DEBUG,
            procs: vec![putint].into(),
        },
    );

    // generate
    let main = generate_func(
        &mut ir,
        &[debug],
        main,
        &mut Box::new(ClosureScope::default()),
        false,
    );
    (ir.procs, main)
}

fn generate_reset(
    ir: &mut IR,
    handlers: &[HandlerIdx],
    body: ExprIdx,
    closure_scope: &mut Box<ClosureScope>,
    debug_name: String,
) -> ProcIdx {
    ClosureScope::child(closure_scope);

    // generate code
    let mut blocks = VecMap::new();
    let start = blocks.push(BlockIdx, Block::default());

    let mut end = start;
    let ret = generate_expr(
        ir,
        handlers,
        body,
        &mut blocks,
        &mut end,
        closure_scope,
        false,
        &mut 0,
        &debug_name,
    );

    if !matches!(
        blocks[end].instructions.last(),
        Some(Instruction::Return(_))
    ) {
        // add return if we haven't already
        blocks[end].instructions.push(Instruction::Return(ret));
    }

    // return proc
    let base_params = closure_scope.base_params;
    let extra_inputs = ClosureScope::parent(closure_scope);

    ir.procs.push(
        ProcIdx,
        Procedure {
            inputs: base_params,
            closure_inputs: extra_inputs,

            is_handler: false,
            outputs: ret.is_some(),
            blocks,
            start,
            debug_name,
        },
    )
}

fn generate_func(
    ir: &mut IR,
    handlers: &[HandlerIdx],
    func: FunIdx,
    closure_scope: &mut Box<ClosureScope>,
    is_handler: bool,
) -> ProcIdx {
    let func = &ir.ast.functions[func];

    // create this closure scope
    ClosureScope::child(closure_scope);

    // add params to vars
    // TODO: we assume all input types fit in a register
    for (i, &(ident, _)) in func.decl.sign.inputs.values().enumerate() {
        let val = ir.asys.values[ident];
        closure_scope.vars.insert(val, Reg(i));
        closure_scope.base_params += 1;
    }

    // generate debug name
    let mut debug_name = ir.ctx.idents[func.decl.name].0.clone();

    if handlers.len() > 0 {
        debug_name += "/";

        for &handler in handlers {
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

    // generate code
    let mut blocks = VecMap::new();
    let start = blocks.push(BlockIdx, Block::default());

    let body = func.body;

    let mut end = start;
    let ret = generate_expr(
        ir,
        handlers,
        body,
        &mut blocks,
        &mut end,
        closure_scope,
        is_handler,
        &mut 0,
        &debug_name,
    )
    .filter(|_| func.decl.sign.output.is_some());

    if is_handler {
        if !matches!(
            blocks[end].instructions.last(),
            Some(Instruction::Resume(_))
        ) {
            // add resume if we haven't already
            blocks[end].instructions.push(Instruction::Resume(ret));
        }
    } else {
        if !matches!(
            blocks[end].instructions.last(),
            Some(Instruction::Return(_))
        ) {
            // add return if we haven't already
            blocks[end].instructions.push(Instruction::Return(ret));
        }
    }

    // return proc
    let base_params = closure_scope.base_params;
    let extra_inputs = ClosureScope::parent(closure_scope);

    ir.procs.push(
        ProcIdx,
        Procedure {
            inputs: base_params,
            closure_inputs: extra_inputs,

            is_handler,
            outputs: ret.is_some(),
            blocks,
            start,
            debug_name,
        },
    )
}

const MAX_PARAMS: usize = 64;

fn next_reg(regs: &mut usize) -> Reg {
    let reg = Reg(MAX_PARAMS + *regs);
    *regs += 1;
    reg
}

fn generate_expr(
    ir: &mut IR,
    handlers: &[HandlerIdx],
    expr: ExprIdx,
    blocks: &mut VecMap<BlockIdx, Block>,
    block: &mut BlockIdx,
    closure_scope: &mut Box<ClosureScope>,
    is_handler: bool,
    regs: &mut usize,
    parent_name: &str,
) -> Option<Reg> {
    use Expression as E;
    match ir.ctx.exprs[expr].0 {
        E::Body(ref body) => {
            for &expr in body.main.iter() {
                generate_expr(
                    ir,
                    handlers,
                    expr,
                    blocks,
                    block,
                    closure_scope,
                    is_handler,
                    regs,
                    parent_name,
                );
            }
            body.last.and_then(|expr| {
                generate_expr(
                    ir,
                    handlers,
                    expr,
                    blocks,
                    block,
                    closure_scope,
                    is_handler,
                    regs,
                    parent_name,
                )
            })
        }
        E::Call(func, ref args) => {
            // TODO: currently we assume func is an Ident expr
            match ir.ctx.exprs[func].0 {
                E::Ident(id) => {
                    let val = ir.asys.values[id];

                    // get base registers
                    let mut reg_args = Vec::new();
                    for &expr in args {
                        let reg = generate_expr(
                            ir,
                            handlers,
                            expr,
                            blocks,
                            block,
                            closure_scope,
                            is_handler,
                            regs,
                            parent_name,
                        )
                        .expect("function call argument does not return a value");
                        reg_args.push(reg);
                    }

                    // check handlers
                    match ir.asys.defs[val] {
                        Definition::EffectFunction(eff_val, eff_idx) => {
                            // get handler
                            let handler = handlers
                                .iter()
                                .map(|&idx| &ir.handlers[idx])
                                .find(|handler| handler.effect == eff_val)
                                .expect("handler of effect function is not in scope");

                            let proc_idx = handler.procs[eff_idx];
                            let proc = &ir.procs[proc_idx];

                            // get closure registers
                            for &val in proc.closure_inputs.iter() {
                                let reg = closure_scope.find_reg(val).expect(
                                    format!("value {} is not loaded in scope", usize::from(val))
                                        .as_str(),
                                );
                                reg_args.push(reg);
                            }

                            // execute handler
                            let output = if proc.outputs {
                                Some(next_reg(regs))
                            } else {
                                None
                            };
                            if proc.is_handler {
                                // get frame parameter
                                let frame_param = closure_scope
                                    .find_reg(eff_val)
                                    .expect("frame parameter is not in scope");

                                // shift to handler
                                blocks[*block].instructions.push(Instruction::Shift(
                                    proc_idx,
                                    output,
                                    reg_args,
                                    frame_param,
                                ));
                            } else {
                                // call handler as function
                                blocks[*block]
                                    .instructions
                                    .push(Instruction::Call(proc_idx, output, reg_args));
                            }
                            output
                        }
                        Definition::Function(func_idx) => {
                            // create proc identity
                            let func = &ir.ast.functions[func_idx];

                            let effects: Box<[HandlerIdx]> = func
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
                                func: val,
                                handlers: effects,
                            };

                            // get proc
                            let proc_idx = if !ir.proc_map.contains_key(&procident) {
                                let idx = generate_func(
                                    ir,
                                    &procident.handlers,
                                    func_idx,
                                    closure_scope,
                                    false,
                                );
                                ir.proc_map.insert(procident, idx);
                                idx
                            } else {
                                ir.proc_map[&procident]
                            };
                            let proc = &ir.procs[proc_idx];

                            // get closure registers
                            for &val in proc.closure_inputs.iter() {
                                let reg = closure_scope
                                    .find_reg(val)
                                    .expect("value is not loaded in scope");
                                reg_args.push(reg);
                            }

                            // execute proc
                            let output = if proc.outputs {
                                Some(next_reg(regs))
                            } else {
                                None
                            };
                            blocks[*block]
                                .instructions
                                .push(Instruction::Call(proc_idx, output, reg_args));
                            output
                        }

                        Definition::Parameter(_) => todo!(),
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
                ir,
                handlers,
                cond,
                blocks,
                block,
                closure_scope,
                is_handler,
                regs,
                parent_name,
            )
            .expect("condition has no value");

            match no {
                Some(no) => {
                    let noblock = blocks.push(BlockIdx, Block::default());
                    let yesblock = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::JmpNZ(cond, yesblock));

                    let yes_reg = generate_expr(
                        ir,
                        handlers,
                        yes,
                        blocks,
                        &mut BlockIdx(yesblock.0),
                        closure_scope,
                        is_handler,
                        regs,
                        parent_name,
                    );

                    let endblock = blocks.push(BlockIdx, Block::default());
                    blocks[*block].next = Some(noblock);
                    blocks[yesblock].next = Some(endblock);
                    blocks[noblock].next = Some(endblock);

                    let no_reg = generate_expr(
                        ir,
                        handlers,
                        no,
                        blocks,
                        &mut BlockIdx(noblock.0),
                        closure_scope,
                        is_handler,
                        regs,
                        parent_name,
                    );

                    *block = endblock;
                    if let (Some(yes), Some(no)) = (yes_reg, no_reg) {
                        let out = next_reg(regs);
                        blocks[*block]
                            .instructions
                            .push(Instruction::Phi(out, [(yes, yesblock), (no, noblock)]));
                        Some(out)
                    } else {
                        None
                    }
                }
                None => {
                    let yesblock = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::JmpNZ(cond, yesblock));

                    generate_expr(
                        ir,
                        handlers,
                        yes,
                        blocks,
                        &mut BlockIdx(yesblock.0),
                        closure_scope,
                        is_handler,
                        regs,
                        parent_name,
                    );

                    let endblock = blocks.push(BlockIdx, Block::default());
                    blocks[*block].next = Some(endblock);
                    blocks[yesblock].next = Some(endblock);

                    *block = endblock;
                    None
                }
            }
        }
        E::Op(left, op, right) => {
            let left = generate_expr(
                ir,
                handlers,
                left,
                blocks,
                block,
                closure_scope,
                is_handler,
                regs,
                parent_name,
            )
            .expect("left operand has no value");

            let right = generate_expr(
                ir,
                handlers,
                right,
                blocks,
                block,
                closure_scope,
                is_handler,
                regs,
                parent_name,
            )
            .expect("right operand has no value");

            let out = next_reg(regs);

            match op {
                Op::Equals => blocks[*block]
                    .instructions
                    .push(Instruction::Equals(out, left, right)),
                Op::Divide => blocks[*block]
                    .instructions
                    .push(Instruction::Div(out, left, right)),
            }

            Some(out)
        }
        E::Break(value) => {
            // get break value
            let reg = value.and_then(|expr| {
                generate_expr(
                    ir,
                    handlers,
                    expr,
                    blocks,
                    block,
                    closure_scope,
                    is_handler,
                    regs,
                    parent_name,
                )
            });

            // TODO: we assume this is top level inside a handler
            blocks[*block].instructions.push(Instruction::Discard(reg));

            // break returns any type
            Some(next_reg(regs))
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

            // put frame register in scope
            let frame_reg = next_reg(regs);
            closure_scope.vars.insert(eff_val, frame_reg);

            // generate handler
            let handler_idx = ir.handlers.push(
                HandlerIdx,
                Handler {
                    effect: eff_val,
                    procs: VecMap::filled(effect.functions.len(), ProcIdx(usize::MAX)),
                },
            );

            for func in ast_handler.functions.iter() {
                let val = ir.asys.values[func.decl.name];
                let eff_fun_idx = match ir.asys.defs[val] {
                    Definition::EffectFunction(_, eff_fun_idx) => eff_fun_idx,
                    _ => panic!("handler has non-effect-function as a function value"),
                };

                // generate handler proc
                let proc_idx = {
                    ClosureScope::child(closure_scope);

                    // add params to vars
                    // TODO: we assume all input types fit in a register
                    for (i, &(ident, _)) in func.decl.sign.inputs.values().enumerate() {
                        let val = ir.asys.values[ident];
                        closure_scope.vars.insert(val, Reg(i));
                        closure_scope.base_params += 1;
                    }

                    // generate debug name
                    let eff_name = ir.ctx.idents[eff_ident].0.as_str();
                    let proc_name = ir.ctx.idents[func.decl.name].0.as_str();
                    let debug_name =
                        format!("{}#{}__{}", eff_name, usize::from(handler_idx), proc_name);
                    // TODO: add handlers of proc

                    // generate code
                    let mut blocks = VecMap::new();
                    let start = blocks.push(BlockIdx, Block::default());

                    let body = func.body;

                    let mut end = start;
                    let ret = generate_expr(
                        ir,
                        handlers, // TODO: add handlers of proc
                        body,
                        &mut blocks,
                        &mut end,
                        closure_scope,
                        true,
                        &mut 0,
                        debug_name.as_str(),
                    )
                    .filter(|_| func.decl.sign.output.is_some());

                    if !matches!(
                        blocks[end].instructions.last(),
                        Some(Instruction::Resume(_))
                    ) {
                        // add resume if we haven't already
                        blocks[end].instructions.push(Instruction::Resume(ret));
                    }

                    // return proc
                    let base_params = closure_scope.base_params;
                    let extra_inputs = ClosureScope::parent(closure_scope);

                    ir.procs.push(
                        ProcIdx,
                        Procedure {
                            inputs: base_params,
                            closure_inputs: extra_inputs,

                            is_handler: true,
                            outputs: ret.is_some(),
                            blocks,
                            start,
                            debug_name,
                        },
                    )
                };

                // add to handler
                ir.handlers[handler_idx].procs[eff_fun_idx] = proc_idx;
            }

            let mut subhandlers = Vec::new();
            subhandlers.extend_from_slice(handlers);
            subhandlers.push(handler_idx);

            // generate reset
            let debug_name = format!(
                "{}__reset#{}",
                parent_name,
                usize::from(frame_reg) - MAX_PARAMS
            );

            let proc_idx = generate_reset(ir, &subhandlers, body, closure_scope, debug_name);
            let proc = &ir.procs[proc_idx];

            // get closure registers
            let mut reg_args = Vec::new();

            for &val in proc.closure_inputs.iter() {
                let reg = closure_scope
                    .find_reg(val)
                    .expect("value is not loaded in scope");
                reg_args.push(reg);
            }

            // execute proc
            let output = if proc.outputs {
                Some(next_reg(regs))
            } else {
                None
            };
            blocks[*block]
                .instructions
                .push(Instruction::Reset(proc_idx, output, reg_args, frame_reg));
            output
        }
        E::Handler(_) => todo!(),
        E::String(_) => todo!(),

        E::Int(i) => {
            let reg = next_reg(regs);

            // TODO: handle overflow
            blocks[*block]
                .instructions
                .push(Instruction::Init(reg, i as i64 as u64));

            Some(reg)
        }

        E::Ident(id) => {
            // TODO: globals
            let val = ir.asys.values[id];
            Some(
                closure_scope
                    .find_reg(val)
                    .expect("value is not loaded in scope"),
            )
        }
        E::Error => todo!(),
    }
}
