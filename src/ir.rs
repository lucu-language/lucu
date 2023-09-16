use std::{
    collections::HashMap,
    mem::{self, MaybeUninit},
};

use crate::{
    analyzer::{Analysis, Definition, EffFunIdx, FunIdx, Val, DEBUG},
    parser::{ExprIdx, Expression, ParseContext, ReturnType, AST},
    vecmap::VecMap,
};

#[derive(Debug)]
pub struct Procedure {
    pub inputs: usize,

    // extra values from the parent function(s) to use as inputs
    pub closure_inputs: Vec<Val>,

    // whether or not this is an effect handler that accepts a continuation parameter
    pub is_handler: bool,

    pub outputs: bool,
    pub blocks: VecMap<BlockIdx, Block>,
    pub start: BlockIdx,
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

#[derive(Debug)]
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
    let main = generate_func(&mut ir, &[debug], main, None, false);
    (ir.procs, main)
}

fn generate_reset(
    ir: &mut IR,
    handlers: &[HandlerIdx],
    body: ExprIdx,
    closure_scope: &mut Box<ClosureScope>,
) -> ProcIdx {
    ClosureScope::child(closure_scope);

    // generate code
    let mut blocks = VecMap::new();
    let mut start_block = Block {
        instructions: Vec::new(),
        next: None,
    };

    let ret = generate_expr(
        ir,
        handlers,
        body,
        &mut blocks,
        &mut start_block,
        closure_scope,
        false,
        &mut 0,
    );

    if !matches!(
        start_block.instructions.last(),
        Some(Instruction::Return(_))
    ) {
        // add return if we haven't already
        start_block.instructions.push(Instruction::Return(ret));
    }

    let start = blocks.push(BlockIdx, start_block);

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
        },
    )
}

fn generate_func(
    ir: &mut IR,
    handlers: &[HandlerIdx],
    func: FunIdx,
    parent_closure: Option<Box<ClosureScope>>,
    is_handler: bool,
) -> ProcIdx {
    let func = &ir.ast.functions[func];

    // create this closure scope
    let mut closure_scope = Box::new(ClosureScope {
        parent: parent_closure,
        vars: HashMap::new(),
        base_params: 0,
        extra_inputs: Vec::new(),
    });

    // add params to vars
    // TODO: we assume all input types fit in a register
    for (i, &(ident, _)) in func.decl.sign.inputs.values().enumerate() {
        let val = ir.asys.values[ident];
        closure_scope.vars.insert(val, Reg(i));
        closure_scope.base_params += 1;
    }

    // generate code
    let mut blocks = VecMap::new();
    let mut start_block = Block {
        instructions: Vec::new(),
        next: None,
    };

    let body = func.body;

    let ret = generate_expr(
        ir,
        handlers,
        body,
        &mut blocks,
        &mut start_block,
        &mut closure_scope,
        is_handler,
        &mut 0,
    )
    .filter(|_| matches!(func.decl.sign.output, Some(ReturnType::Type(_))));

    if is_handler {
        if !matches!(
            start_block.instructions.last(),
            Some(Instruction::Resume(_))
        ) {
            // add resume if we haven't already
            start_block.instructions.push(Instruction::Resume(ret));
        }
    } else {
        if !matches!(
            start_block.instructions.last(),
            Some(Instruction::Return(_))
        ) {
            // add return if we haven't already
            start_block.instructions.push(Instruction::Return(ret));
        }
    }

    let start = blocks.push(BlockIdx, start_block);

    // return proc
    ir.procs.push(
        ProcIdx,
        Procedure {
            inputs: closure_scope.base_params,
            closure_inputs: closure_scope.extra_inputs,

            is_handler,
            outputs: ret.is_some(),
            blocks,
            start,
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
    block: &mut Block,
    closure_scope: &mut Box<ClosureScope>,
    is_handler: bool,
    regs: &mut usize,
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
                );
            }
            match body.last {
                Some(expr) => generate_expr(
                    ir,
                    handlers,
                    expr,
                    blocks,
                    block,
                    closure_scope,
                    is_handler,
                    regs,
                ),
                None => None,
            }
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
                                let reg = closure_scope
                                    .find_reg(val)
                                    .expect("value is not loaded in scope");
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
                                block.instructions.push(Instruction::Shift(
                                    proc_idx,
                                    output,
                                    reg_args,
                                    frame_param,
                                ));
                            } else {
                                // call handler as function
                                block
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
                                let idx =
                                    generate_func(ir, &procident.handlers, func_idx, None, false);
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
                            block
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
        E::IfElse(_, _, _) => todo!(),
        E::Op(_, _, _) => todo!(),
        E::Break(_) => todo!(),
        E::TryWith(body, handler) => {
            // get handler
            let ast_handler = match ir.ctx.exprs[handler].0 {
                E::Handler(ref handler) => handler,
                _ => todo!(),
            };

            // get effect
            let eff_val = ir.asys.values[ast_handler.effect];
            let eff_idx = match ir.asys.defs[eff_val] {
                Definition::Effect(eff_idx) => eff_idx,
                _ => panic!("handler has non-effect as effect value"),
            };
            let effect = &ir.ast.effects[eff_idx];

            // put frame register in scope
            let frame_reg = next_reg(regs);
            closure_scope.vars.insert(eff_val, frame_reg);

            // generate handler
            let mut handler = Handler {
                effect: eff_val,
                procs: VecMap::filled(effect.functions.len(), ProcIdx(usize::MAX)),
            };
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

                    // generate code
                    let mut blocks = VecMap::new();
                    let mut start_block = Block {
                        instructions: Vec::new(),
                        next: None,
                    };

                    let body = func.body;

                    let ret = generate_expr(
                        ir,
                        handlers, // TODO: add handlers of proc
                        body,
                        &mut blocks,
                        &mut start_block,
                        closure_scope,
                        true,
                        &mut 0,
                    )
                    .filter(|_| matches!(func.decl.sign.output, Some(ReturnType::Type(_))));

                    if !matches!(
                        start_block.instructions.last(),
                        Some(Instruction::Resume(_))
                    ) {
                        // add resume if we haven't already
                        start_block.instructions.push(Instruction::Resume(ret));
                    }

                    let start = blocks.push(BlockIdx, start_block);

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
                        },
                    )
                };

                // add to handler
                handler.procs[eff_fun_idx] = proc_idx;
            }

            // add handler to list
            let handler_idx = ir.handlers.push(HandlerIdx, handler);

            let mut subhandlers = Vec::new();
            subhandlers.extend_from_slice(handlers);
            subhandlers.push(handler_idx);

            // generate reset
            let proc_idx = generate_reset(ir, &subhandlers, body, closure_scope);
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
            block
                .instructions
                .push(Instruction::Reset(proc_idx, output, reg_args, frame_reg));
            output
        }
        E::Handler(_) => todo!(),
        E::String(_) => todo!(),

        E::Int(i) => {
            let reg = next_reg(regs);

            // TODO: handle overflow
            block
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
