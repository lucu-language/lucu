use std::collections::HashMap;

use crate::{
    analyzer::{Analysis, Val, DEBUG, PUTINT},
    parser::{Expr, Expression, ParseContext, ReturnType, AST},
    vecmap::VecMap,
};

#[derive(Debug)]
pub struct Procedure {
    pub inputs: usize,
    pub outputs: usize,
    pub blocks: VecMap<BlockIdx, Block>,
}

#[derive(Debug)]
pub enum Instruction {
    PushInt(i64),
    PushString(String),
    PushParam(usize),
    Pop,

    Jmp(BlockIdx),        // jump to block
    JmpNonzero(BlockIdx), // jump to block if top is nonzero

    Equals,
    Div,
    Mul,
    Add,

    Reset(ProcIdx), // reset to function
    Shift(ProcIdx), // shift to function
    Call(ProcIdx),  // call function

    Continue(usize), // continue continuation with arguments
    Return(usize),   // return with arguments

    Print,
}

#[derive(Debug)]
pub struct Block {
    pub instructions: Vec<Instruction>,
}

#[derive(Debug)]
struct HandlerProcIdent {
    proc: ProcIdent,
    has_cont: bool,
}

#[derive(Debug)]
struct Handler {
    effect: Val,
    procs: HashMap<Val, HandlerProcIdent>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct HandlerIdx(usize);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ProcIdx(usize);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct BlockIdx(usize);

impl From<HandlerIdx> for usize {
    fn from(value: HandlerIdx) -> Self {
        value.0
    }
}

impl From<ProcIdx> for usize {
    fn from(value: ProcIdx) -> Self {
        value.0
    }
}

impl From<BlockIdx> for usize {
    fn from(value: BlockIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
struct ProcIdent {
    func: Val,
    handlers: Box<[HandlerIdx]>,
}

#[derive(Default)]
struct IR {
    procs: VecMap<ProcIdx, Procedure>,
    func_map: HashMap<ProcIdent, ProcIdx>,
    handlers: VecMap<HandlerIdx, Handler>,
}

fn generate_expr(
    ast: &AST,
    ctx: &ParseContext,
    asys: &Analysis,
    handlers: &[HandlerIdx],
    params: &[Val],
    expr: Expr,
    pop_ret: bool,
    block: &mut Block,
    proc: &mut Procedure,
    out: &mut IR,
) {
    use Expression as E;
    match ctx.exprs[expr].0 {
        E::Body(ref b) => {
            for &expr in b.main.iter() {
                generate_expr(
                    ast, ctx, asys, handlers, params, expr, true, block, proc, out,
                );
            }
            if let Some(expr) = b.last {
                generate_expr(
                    ast, ctx, asys, handlers, params, expr, pop_ret, block, proc, out,
                );
                block.instructions.push(Instruction::Return(proc.outputs))
            }
        }
        E::Call(func, ref args) => {
            // push args to stack
            for &expr in args.iter() {
                generate_expr(
                    ast, ctx, asys, handlers, params, expr, false, block, proc, out,
                );
            }

            // TODO: currently we assume func is an Ident expr
            match ctx.exprs[func].0 {
                E::Ident(id) => {
                    let val = asys.values[id];

                    // check handlers
                    let option = handlers
                        .iter()
                        .map(|&idx| out.handlers[idx].procs.get(&val).map(|proc| (idx, proc)))
                        .flatten()
                        .next();

                    match option {
                        Some((closure, proc_idx)) => {
                            // push handler closures
                            for &closure in proc_idx.proc.handlers.iter() {
                                let pos = handlers
                                    .iter()
                                    .position(|&handler| handler == closure)
                                    .unwrap();
                                block
                                    .instructions
                                    .push(Instruction::PushParam(params.len() + pos));
                            }

                            // push this handler closure
                            let pos = handlers
                                .iter()
                                .position(|&handler| handler == closure)
                                .unwrap();
                            block
                                .instructions
                                .push(Instruction::PushParam(params.len() + pos));

                            // goto handler
                            if proc_idx.has_cont {
                                // shift to handler
                                block
                                    .instructions
                                    .push(Instruction::Shift(out.func_map[&proc_idx.proc]));
                            } else {
                                // call handler as regular function
                                block
                                    .instructions
                                    .push(Instruction::Call(out.func_map[&proc_idx.proc]));
                            }
                        }
                        None => {
                            // find function
                            let (func_idx, decl) = ast
                                .functions
                                .iter()
                                .enumerate()
                                .find(|(_, p)| asys.values[p.decl.name] == val)
                                .map(|(i, f)| (i, &f.decl))
                                .unwrap();

                            // get handler vec of function
                            let effects: Box<[HandlerIdx]> = decl
                                .sign
                                .effects
                                .iter()
                                .map(|&e| {
                                    let effect = asys.values[e];
                                    handlers
                                        .iter()
                                        .find(|&&h| out.handlers[h].effect == effect)
                                        .unwrap()
                                        .clone()
                                })
                                .collect();

                            // push handler closures
                            for &closure in effects.iter() {
                                let pos = handlers
                                    .iter()
                                    .position(|&handler| handler == closure)
                                    .unwrap();
                                block
                                    .instructions
                                    .push(Instruction::PushParam(params.len() + pos));
                            }

                            // create procedure fingerprint
                            let procident = ProcIdent {
                                func: val,
                                handlers: effects,
                            };

                            // generate function if it does not exist yet
                            let idx = if !out.func_map.contains_key(&procident) {
                                let idx = generate_func(
                                    ast,
                                    ctx,
                                    asys,
                                    &procident.handlers,
                                    func_idx,
                                    out,
                                );
                                out.func_map.insert(procident, idx);
                                idx
                            } else {
                                out.func_map[&procident]
                            };

                            // call function
                            block.instructions.push(Instruction::Call(idx));
                        }
                    }
                }
                _ => todo!(),
            };
        }
        E::Member(_, _) => todo!(),
        E::IfElse(_, _, _) => todo!(),
        E::Op(_, _, _) => todo!(),
        E::Break(_) => todo!(),
        E::TryWith(_, _) => todo!(),
        E::Handler(_) => todo!(),
        E::String(ref s) => {
            if !pop_ret {
                block.instructions.push(Instruction::PushString(s.clone()))
            }
        }
        E::Int(i) => {
            if !pop_ret {
                // TODO: handle overflow
                block
                    .instructions
                    .push(Instruction::PushInt(i.try_into().unwrap()))
            }
        }
        E::Ident(id) => {
            if !pop_ret {
                let val = asys.values[id];

                // TODO: global and local variables

                // TODO: handle not found
                let param = params.iter().position(|&p| p == val).unwrap();

                block.instructions.push(Instruction::PushParam(param))
            }
        }
        E::Error => todo!(),
    }
}

fn generate_func(
    ast: &AST,
    ctx: &ParseContext,
    asys: &Analysis,
    handlers: &[HandlerIdx],
    func: usize,
    out: &mut IR,
) -> ProcIdx {
    let func = &ast.functions[func];

    // create base procedure
    let mut proc = Procedure {
        inputs: func.decl.sign.inputs.len() + handlers.len(),
        outputs: match func.decl.sign.output {
            Some(ReturnType::Type(_)) => 1,
            _ => 0,
        },
        blocks: VecMap::new(),
    };

    // create parameter vec
    let params: Vec<Val> = func
        .decl
        .sign
        .inputs
        .iter()
        .map(|&(ident, _)| asys.values[ident])
        .collect();

    // generate code
    let mut start_block = Block {
        instructions: Vec::new(),
    };

    let body = func.body;
    generate_expr(
        ast,
        ctx,
        asys,
        handlers,
        &params,
        body,
        false,
        &mut start_block,
        &mut proc,
        out,
    );
    proc.blocks.push(BlockIdx, start_block);

    out.procs.push(ProcIdx, proc)
}

pub fn generate_ir(ast: &AST, ctx: &ParseContext, asys: &Analysis) -> Vec<Procedure> {
    let main = ast
        .functions
        .iter()
        .enumerate()
        .find(|(_, f)| ctx.idents[f.decl.name].0 == "main")
        .unwrap()
        .0;

    let mut out = IR::default();

    // define putint
    let putint = out.procs.push(
        ProcIdx,
        Procedure {
            inputs: 2, // int + debug closure
            outputs: 0,
            blocks: vec![Block {
                instructions: vec![
                    Instruction::PushParam(0),
                    Instruction::Print,
                    Instruction::Return(0),
                ],
            }]
            .into(),
        },
    );

    let putint_ident = ProcIdent {
        func: PUTINT,
        handlers: Box::new([]),
    };

    out.func_map.insert(putint_ident.clone(), putint);

    // define debug
    let mut debug_procs = HashMap::new();
    debug_procs.insert(
        PUTINT,
        HandlerProcIdent {
            proc: putint_ident,
            has_cont: false,
        },
    );

    let debug = out.handlers.push(
        HandlerIdx,
        Handler {
            effect: DEBUG,
            procs: debug_procs,
        },
    );

    // generate
    generate_func(ast, ctx, asys, &[debug], main, &mut out);
    out.procs.as_vec()
}
