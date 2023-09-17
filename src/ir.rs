use std::{
    collections::HashMap,
    fmt::{self, Display},
    write,
};

use crate::{
    analyzer::{Analysis, Definition, EffFunIdx, Val, DEBUG},
    parser::{ExprIdx, Expression, Op, ParseContext, AST},
    vecmap::VecMap,
};

#[derive(Debug)]
pub struct Procedure {
    pub inputs: Vec<Reg>,
    pub captures: Vec<Reg>,

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
    Sub(Reg, Reg, Reg),

    // call procedure, put return into reg, call with arguments
    Reset(ProcIdx, Option<Reg>, Vec<Reg>, Reg), // puts frame parameter into reg and calls
    Shift(ProcIdx, Option<Reg>, Vec<Reg>, Reg), // shift into procedure with frame parameter
    Call(ProcIdx, Option<Reg>, Vec<Reg>),       // regular call

    // return statements for effect handlers
    Resume(Option<Reg>, Option<Reg>), // resume the continuation with optional value
    Discard(Option<Reg>),             // discard the continuation and return with optional value

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
    fun: Val,
    handlers: Box<[HandlerIdx]>,
}

#[derive(Debug)]
struct Handler {
    effect: Val,
    procs: VecMap<EffFunIdx, ProcIdx>,
}

struct Regs(usize);

struct IR<'a> {
    procs: VecMap<ProcIdx, Procedure>,
    proc_map: HashMap<ProcIdent, ProcIdx>,
    handlers: VecMap<HandlerIdx, Handler>,

    vars: HashMap<Val, Reg>,
    regs: Regs,

    ast: &'a AST,
    ctx: &'a ParseContext,
    asys: &'a Analysis,
}

impl Regs {
    fn next_reg(&mut self) -> Reg {
        let reg = Reg(self.0);
        self.0 += 1;
        reg
    }
}

impl Display for VecMap<ProcIdx, Procedure> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for proc in self.values() {
            // write proc signature
            write!(f, "{}", proc.debug_name)?;

            if proc.is_handler {
                write!(f, " < cont >")?;
            }

            if proc.captures.len() > 0 {
                write!(f, " [ ")?;
                for &r in proc.captures.iter() {
                    if r != *proc.captures.first().unwrap() {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", r)?;
                }
                write!(f, " ]")?;
            }

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
                        Instruction::Copy(r, v) => writeln!(f, "{} <- {}", r, v)?,
                        Instruction::JmpNZ(r, b) => writeln!(f, "       jnz {}, {}", r, b)?,
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
                        Instruction::Reset(proc, out, ref args, frame) => writeln!(
                            f,
                            "{}rst {}, {}{}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            frame,
                            self[proc].debug_name,
                            match self[proc]
                                .captures
                                .iter()
                                .map(|r| r.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                                .as_str()
                            {
                                "" => "".into(),
                                a => format!(" [ {} ]", a),
                            },
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
                        Instruction::Shift(proc, out, ref args, frame) => writeln!(
                            f,
                            "{}sft {} < {} >{}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            self[proc].debug_name,
                            frame,
                            match self[proc]
                                .captures
                                .iter()
                                .map(|r| r.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                                .as_str()
                            {
                                "" => "".into(),
                                a => format!(" [ {} ]", a),
                            },
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
                        Instruction::Call(proc, out, ref args) => writeln!(
                            f,
                            "{}cal {}{}{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            self[proc].debug_name,
                            match self[proc]
                                .captures
                                .iter()
                                .map(|r| r.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                                .as_str()
                            {
                                "" => "".into(),
                                a => format!(" [ {} ]", a),
                            },
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
                        Instruction::Resume(out, r) => writeln!(
                            f,
                            "{}res{}",
                            match out {
                                Some(out) => format!("{} <- ", out),
                                None => "       ".into(),
                            },
                            match r {
                                Some(r) => format!(" {}", r),
                                None => "".into(),
                            }
                        )?,
                        Instruction::Discard(r) | Instruction::Return(r) => match r {
                            Some(r) => writeln!(f, "       ret {}", r)?,
                            None => writeln!(f, "       ret")?,
                        },
                        Instruction::PrintNum(r) => writeln!(f, "       put {}", r)?,

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
    let mut ir = IR {
        procs: VecMap::new(),
        proc_map: HashMap::new(),
        handlers: VecMap::new(),
        ast,
        ctx,
        asys,
        vars: HashMap::new(),
        regs: Regs(0),
    };

    // define putint
    let putint = ir.procs.push(
        ProcIdx,
        Procedure {
            inputs: vec![ir.regs.next_reg()], // int
            captures: vec![],

            is_handler: false,
            outputs: false,

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
        },
    );

    // generate
    // TODO: main not found
    let main = asys.main.expect("no main function");
    let fun = &ir.ast.functions[main];
    let val = ir.asys.values[fun.decl.name];

    let params: Box<[Val]> = fun
        .decl
        .sign
        .inputs
        .values()
        .map(|&(ident, _)| ir.asys.values[ident])
        .collect();

    let main = generate_func(
        &mut ir,
        Some(val),
        &[debug],
        &params,
        fun.body,
        fun.decl.sign.output.is_some(),
        false,
        "main".into(),
    );
    (ir.procs, main)
}

fn generate_func(
    ir: &mut IR,
    fun: Option<Val>,
    handlers: &[HandlerIdx],
    params: &[Val],
    body: ExprIdx,
    outputs: bool,
    is_handler: bool,
    debug_name: String,
) -> ProcIdx {
    // add params to vars
    // TODO: we assume all input types fit in a register
    let mut inputs = Vec::new();

    for &val in params {
        let reg = ir.regs.next_reg();
        ir.vars.insert(val, reg);
        inputs.push(reg);
    }

    // add new proc to list
    let mut blocks = VecMap::new();
    let start = blocks.push(BlockIdx, Block::default());

    let proc_idx = ir.procs.push(
        ProcIdx,
        Procedure {
            inputs,
            is_handler,
            outputs,
            start,

            // these will be defined at the end
            debug_name: String::new(),
            captures: Vec::new(),
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

    // generate code
    let mut end = start;
    let ret = generate_expr(
        ir,
        handlers,
        body,
        &mut blocks,
        &mut end,
        is_handler,
        &debug_name,
    )
    .filter(|_| outputs);

    if !matches!(
        blocks[end].instructions.last(),
        Some(Instruction::Return(_))
    ) {
        // add return if we haven't already
        let ret = if is_handler {
            // tail call resume for handlers
            let res = ret;
            let ret = res.map(|_| ir.regs.next_reg());
            blocks[end].instructions.push(Instruction::Resume(ret, res));
            ret
        } else {
            ret
        };
        blocks[end].instructions.push(Instruction::Return(ret));
    }

    // return proc
    ir.procs[proc_idx].debug_name = debug_name;
    ir.procs[proc_idx].blocks = blocks;
    proc_idx
}

fn generate_expr(
    ir: &mut IR,
    handlers: &[HandlerIdx],
    expr: ExprIdx,
    blocks: &mut VecMap<BlockIdx, Block>,
    block: &mut BlockIdx,
    is_handler: bool,
    parent_name: &str,
) -> Option<Reg> {
    use Expression as E;
    match ir.ctx.exprs[expr].0 {
        E::Body(ref body) => {
            for &expr in body.main.iter() {
                generate_expr(ir, handlers, expr, blocks, block, is_handler, parent_name);
            }
            body.last.and_then(|expr| {
                generate_expr(ir, handlers, expr, blocks, block, is_handler, parent_name)
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
                            is_handler,
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

                            // execute handler
                            let output = if proc.outputs {
                                Some(ir.regs.next_reg())
                            } else {
                                None
                            };
                            if proc.is_handler {
                                // get frame parameter
                                let frame_param = *ir
                                    .vars
                                    .get(&eff_val)
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

                            // get proc
                            let proc_idx = if !ir.proc_map.contains_key(&procident) {
                                let handlers = &procident.handlers;

                                // get params
                                let params: Box<[Val]> = fun
                                    .decl
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|&(ident, _)| ir.asys.values[ident])
                                    .collect();

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
                                generate_func(
                                    ir,
                                    Some(val),
                                    handlers,
                                    &params,
                                    fun.body,
                                    fun.decl.sign.output.is_some(),
                                    false,
                                    debug_name,
                                )
                            } else {
                                ir.proc_map[&procident]
                            };
                            let proc = &ir.procs[proc_idx];

                            // execute proc
                            let output = if proc.outputs {
                                Some(ir.regs.next_reg())
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
            let cond = generate_expr(ir, handlers, cond, blocks, block, is_handler, parent_name)
                .expect("condition has no value");

            match no {
                Some(no) => {
                    let no_start = blocks.push(BlockIdx, Block::default());
                    let yes_start = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::JmpNZ(cond, yes_start));

                    let mut yes_end = yes_start;
                    let yes_reg = generate_expr(
                        ir,
                        handlers,
                        yes,
                        blocks,
                        &mut yes_end,
                        is_handler,
                        parent_name,
                    );

                    let end = blocks.push(BlockIdx, Block::default());

                    let mut no_end = no_start;
                    let no_reg = generate_expr(
                        ir,
                        handlers,
                        no,
                        blocks,
                        &mut no_end,
                        is_handler,
                        parent_name,
                    );

                    blocks[*block].next = Some(no_start);
                    blocks[yes_end].next = Some(end);
                    blocks[no_end].next = Some(end);
                    *block = end;

                    if let (Some(yes), Some(no)) = (yes_reg, no_reg) {
                        let out = ir.regs.next_reg();
                        blocks[*block]
                            .instructions
                            .push(Instruction::Phi(out, [(yes, yes_end), (no, no_end)]));
                        Some(out)
                    } else {
                        None
                    }
                }
                None => {
                    let yes_start = blocks.push(BlockIdx, Block::default());

                    blocks[*block]
                        .instructions
                        .push(Instruction::JmpNZ(cond, yes_start));

                    let mut yes_end = yes_start;
                    generate_expr(
                        ir,
                        handlers,
                        yes,
                        blocks,
                        &mut yes_end,
                        is_handler,
                        parent_name,
                    );

                    let end = blocks.push(BlockIdx, Block::default());

                    blocks[*block].next = Some(end);
                    blocks[yes_end].next = Some(end);
                    *block = end;

                    None
                }
            }
        }
        E::Op(left, op, right) => {
            let left = generate_expr(ir, handlers, left, blocks, block, is_handler, parent_name)
                .expect("left operand has no value");

            let right = generate_expr(ir, handlers, right, blocks, block, is_handler, parent_name)
                .expect("right operand has no value");

            let out = ir.regs.next_reg();

            let instr = match op {
                Op::Equals => Instruction::Equals(out, left, right),
                Op::Divide => Instruction::Div(out, left, right),
                Op::Multiply => Instruction::Mul(out, left, right),
                Op::Subtract => Instruction::Sub(out, left, right),
                Op::Add => Instruction::Add(out, left, right),
            };
            blocks[*block].instructions.push(instr);

            Some(out)
        }
        E::Break(value) => {
            // get break value
            let reg = value.and_then(|expr| {
                generate_expr(ir, handlers, expr, blocks, block, is_handler, parent_name)
            });

            // TODO: we assume this is top level inside a handler
            blocks[*block].instructions.push(Instruction::Discard(reg));

            // break returns any type
            Some(ir.regs.next_reg())
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
            let frame_reg = ir.regs.next_reg();
            ir.vars.insert(eff_val, frame_reg);

            // generate handler
            let handler_idx = ir.handlers.push(
                HandlerIdx,
                Handler {
                    effect: eff_val,
                    procs: VecMap::filled(effect.functions.len(), ProcIdx(usize::MAX)),
                },
            );

            for fun in ast_handler.functions.iter() {
                let val = ir.asys.values[fun.decl.name];
                let eff_fun_idx = match ir.asys.defs[val] {
                    Definition::EffectFunction(_, eff_fun_idx) => eff_fun_idx,
                    _ => panic!("handler has non-effect-function as a function value"),
                };

                // get params
                let params: Box<[Val]> = fun
                    .decl
                    .sign
                    .inputs
                    .values()
                    .map(|&(ident, _)| ir.asys.values[ident])
                    .collect();

                // generate debug name
                let eff_name = ir.ctx.idents[eff_ident].0.as_str();
                let proc_name = ir.ctx.idents[fun.decl.name].0.as_str();
                let debug_name =
                    format!("{}#{}__{}", eff_name, usize::from(handler_idx), proc_name);
                // TODO: add handlers of proc

                // generate handler proc
                let proc_idx = generate_func(
                    ir,
                    None,
                    handlers, // TODO: add handlers of proc
                    &params,
                    fun.body,
                    fun.decl.sign.output.is_some(),
                    true,
                    debug_name,
                );

                // add to handler
                ir.handlers[handler_idx].procs[eff_fun_idx] = proc_idx;
            }

            let mut subhandlers = Vec::new();
            subhandlers.extend_from_slice(handlers);
            subhandlers.push(handler_idx);

            // generate reset
            let debug_name = format!("{}__reset#{}", parent_name, usize::from(frame_reg));

            let proc_idx = generate_func(
                ir,
                None,
                &subhandlers,
                &[],
                body,
                true, // TODO: use type checker to see if this outputs a value
                is_handler,
                debug_name,
            );
            let proc = &ir.procs[proc_idx];

            // execute proc
            let output = if proc.outputs {
                Some(ir.regs.next_reg())
            } else {
                None
            };
            blocks[*block].instructions.push(Instruction::Reset(
                proc_idx,
                output,
                Vec::new(),
                frame_reg,
            ));
            output
        }
        E::Handler(_) => todo!(),
        E::String(_) => todo!(),

        E::Int(i) => {
            let reg = ir.regs.next_reg();

            // TODO: handle overflow
            blocks[*block]
                .instructions
                .push(Instruction::Init(reg, i as i64 as u64));

            Some(reg)
        }

        E::Ident(id) => {
            // TODO: globals
            let val = ir.asys.values[id];
            Some(*ir.vars.get(&val).expect("value is not loaded in scope"))
        }
        E::Error => todo!(),
    }
}
