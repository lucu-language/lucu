use std::collections::{hash_map::Entry, HashMap, HashSet};

use crate::{
    ast::EffIdx,
    error::Errors,
    sema::{
        self, get_value, BlockIdx, FunIdent, FunImpl, FunSign, GenericIdx, GenericVal, InstrIdx,
        IntSize, LazyIdx, LazyValue, SemIR, Value,
    },
    vecmap::{VecMap, VecSet},
    Target,
};

use super::{
    AggrIdx, AggregateType, Block, HandlerIdx, Instruction, ProcForeignIdx, ProcIdx, ProcImpl,
    ProcSign, Reg, Type, TypeIdx, IR,
};

struct IRCtx<'a> {
    ir: IR,
    sema: &'a SemIR,
    errors: &'a mut Errors,

    slice_types: HashMap<TypeIdx, AggrIdx>,
    proc_todo: Vec<(ProcIdx, ProcCtx<'a>)>,

    handler_types: HashMap<(sema::HandlerIdx, GenericParams<'a>), TypeIdx>,
    functions: HashMap<(FunIdent, GenericParams<'a>), ProcType>,
    handlers: VecMap<HandlerIdx, (sema::HandlerIdx, GenericParams<'a>)>,
}

#[derive(Clone, Copy)]
enum ProcType {
    Top(ProcIdx),
    Foreign(ProcForeignIdx),
}

struct ProcCtx<'a> {
    idx: ProcIdx,

    sign: &'a FunSign,
    handler: Option<HandlerIdx>,
    imp: &'a FunImpl,

    params: GenericParams<'a>,
    regs: VecMap<BlockIdx, VecMap<InstrIdx, Option<Reg>>>,

    blocks: VecMap<BlockIdx, Block>,
    block: BlockIdx,
}

impl ProcCtx<'_> {
    fn push(&mut self, instr: Instruction) {
        self.blocks[self.block].instructions.push(instr);
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
enum Generic<'a> {
    Type(TypeIdx),
    Const(&'a Value),
    Effect(EffIdx, GenericParams<'a>),
}

type GenericParams<'a> = Vec<(GenericIdx, Generic<'a>)>;

fn get_param<'a>(generic_params: &GenericParams<'a>, idx: GenericIdx) -> Option<Generic<'a>> {
    get_value(generic_params, &idx).cloned()
}

fn get_type<'a>(params: &GenericParams<'a>, idx: GenericIdx) -> TypeIdx {
    match get_param(params, idx).unwrap() {
        Generic::Type(val) => val,
        _ => unreachable!(),
    }
}

fn get_constant<'a>(params: &GenericParams<'a>, idx: GenericIdx) -> &'a Value {
    match get_param(params, idx).unwrap() {
        Generic::Const(val) => val,
        _ => unreachable!(),
    }
}

impl<'a> IRCtx<'a> {
    fn lower_type(&mut self, ty: sema::TypeIdx, params: &GenericParams<'a>) -> TypeIdx {
        match self.lower_generic(ty, params) {
            Generic::Type(idx) => idx,
            _ => unreachable!(),
        }
    }
    fn lower_generic(&mut self, ty: sema::TypeIdx, params: &GenericParams<'a>) -> Generic<'a> {
        use sema::Type as T;
        Generic::Type(match self.sema.types[ty] {
            T::Handler(l) => self.lower_lazy(l.idx, params),
            T::Generic(g) => {
                return get_param(&params, g.idx).unwrap();
            }
            T::Pointer(ty) => {
                let ty = self.lower_type(ty, params);
                self.insert_type(Type::Pointer(ty))
            }
            T::ConstArray(size, ty) => {
                let ty = self.lower_type(ty, params);
                let size = match size {
                    GenericVal::Literal(size) => size,
                    GenericVal::Generic(idx) => match get_constant(&params, idx) {
                        Value::ConstantInt(_, false, size) => *size,
                        Value::ConstantZero(_) => 0,
                        _ => unreachable!(),
                    },
                };
                self.insert_type(Type::ConstArray(size, ty))
            }
            T::Slice(ty) => {
                let ty = self.lower_type(ty, params);
                self.insert_slice(ty)
            }
            T::Integer(_, IntSize::Reg) => self.insert_type(Type::Int),
            T::Integer(_, IntSize::Size) => self.insert_type(Type::IntSize),
            T::Integer(_, IntSize::Ptr) => self.insert_type(Type::IntPtr),
            T::Integer(_, IntSize::Bits(8)) => self.insert_type(Type::Int8),
            T::Integer(_, IntSize::Bits(16)) => self.insert_type(Type::Int16),
            T::Integer(_, IntSize::Bits(32)) => self.insert_type(Type::Int32),
            T::Integer(_, IntSize::Bits(64)) => self.insert_type(Type::Int64),
            T::Integer(_, _) => todo!(),
            T::Str => {
                let char = self.insert_type(Type::Int8);
                self.insert_slice(char)
            }
            T::Char => self.insert_type(Type::Int32),
            T::Bool => self.insert_type(Type::Bool),
            T::None => self.insert_type(Type::Unit),
            T::Never => self.insert_type(Type::Never),

            T::CompileTime(ref val) => return Generic::Const(val),
            T::Effect(ref ident) => {
                return Generic::Effect(
                    ident.effect,
                    ident
                        .generic_params
                        .iter()
                        .map(|&(idx, ty)| (idx, self.lower_generic(ty, params)))
                        .collect(),
                )
            }

            T::EffectType => unreachable!(),
            T::DataType => unreachable!(),
            T::HandlerType(_) => unreachable!(),

            T::Error => unreachable!(),
        })
    }
    fn lower_lazy(&mut self, lazy: LazyIdx, params: &GenericParams<'a>) -> TypeIdx {
        match &self.sema.lazy_handlers[lazy] {
            LazyValue::Some(GenericVal::Literal(ident)) => {
                let params = ident
                    .generic_params
                    .iter()
                    .map(|&(idx, ty)| (idx, self.lower_generic(ty, params)))
                    .collect::<Vec<_>>();
                let ident = (ident.handler, params);
                if let Some(ty) = self.handler_types.get(&ident).copied() {
                    return ty;
                }

                let break_type = self.lower_type(self.sema.handlers[ident.0].fail, &ident.1);
                let captures = self.sema.handlers[ident.0]
                    .captures
                    .iter()
                    .map(|&ty| self.lower_type(ty, &ident.1))
                    .collect();
                let aggr = self.ir.aggregates.push(
                    AggrIdx,
                    AggregateType {
                        children: captures,
                        debug_name: format!("H{}", ident.0 .0),
                    },
                );

                let idx = self.handlers.push(HandlerIdx, ident.clone());
                self.ir.break_types.push_value(break_type);

                let ty = self.insert_type(Type::Handler(idx, aggr));
                self.handler_types.insert(ident, ty);
                ty
            }
            LazyValue::Some(GenericVal::Generic(idx)) => get_type(&params, *idx),
            LazyValue::EffectFunOutput(idx, fun, ps) => {
                let handler = self.lower_lazy(*idx, params);
                let handler = match self.ir.types[handler] {
                    Type::Handler(idx, _) => idx,
                    _ => unreachable!(),
                };
                let (idx, ref handler_params) = self.handlers[handler];
                let params = handler_params
                    .clone()
                    .into_iter()
                    .chain(
                        ps.iter()
                            .map(|&(idx, ty)| (idx, self.lower_generic(ty, &params))),
                    )
                    .collect::<Vec<_>>();
                self.lower_type(self.sema.handlers[idx].funs[*fun].0.return_type.ty, &params)
            }
            LazyValue::None => todo!(),
            LazyValue::Refer(_, _) => unreachable!(),
        }
    }
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        *self.ir.types.insert(TypeIdx, ty)
    }
    fn insert_slice(&mut self, ty: TypeIdx) -> TypeIdx {
        let ptr = self.insert_type(Type::Pointer(ty));
        let size = self.insert_type(Type::IntSize);

        match self.slice_types.entry(ty) {
            Entry::Occupied(e) => {
                let aggr = *e.get();
                self.insert_type(Type::Aggregate(aggr))
            }
            Entry::Vacant(e) => {
                let aggr = self.ir.aggregates.push(
                    AggrIdx,
                    AggregateType {
                        children: vec![ptr, size],
                        debug_name: format!("[]#{}", ty.0),
                    },
                );

                e.insert(aggr);
                self.insert_type(Type::Aggregate(aggr))
            }
        }
    }
    fn next_reg(&mut self, ty: TypeIdx) -> Reg {
        self.ir.regs.push(Reg, ty)
    }
    fn lower_sign(
        &mut self,
        fun: FunIdent,
        mut params: GenericParams<'a>,
        inputs: Vec<TypeIdx>,
        effect_tys: Vec<TypeIdx>,
        return_type: TypeIdx,
    ) -> ProcType {
        let (imp, handler) = match fun {
            FunIdent::Top(idx) => (&self.sema.fun_impl[idx], None),
            FunIdent::Effect(_, idx) => {
                let handler = match params.last().unwrap().1 {
                    Generic::Type(ty) => ty,
                    _ => unreachable!(),
                };
                let handler_idx = match self.ir.types[handler] {
                    Type::Handler(idx, _) => idx,
                    _ => unreachable!(),
                };
                let handler = &self.handlers[handler_idx];
                params.extend(handler.1.iter().cloned());

                (
                    &self.sema.handlers[handler.0].funs[idx].1,
                    Some(handler_idx),
                )
            }
        };

        let ident = (fun, params);
        if let Some(idx) = self.functions.get(&ident).copied() {
            return idx;
        }
        let (fun, params) = ident;

        // TODO: recursrively add captured handlers as well
        let unhandled = effect_tys
            .iter()
            .filter_map(|&ty| match self.ir.types[ty] {
                Type::Handler(idx, _) => match self.ir.types[self.ir.break_types[idx]] {
                    Type::Never => None,
                    _ => Some(idx),
                },
                _ => unreachable!(),
            })
            .collect();

        let inputs = inputs.into_iter().map(|ty| self.next_reg(ty)).collect();
        let output = return_type;

        let sign = fun.sign(self.sema);
        let idx = self.ir.proc_sign.push(
            ProcIdx,
            ProcSign {
                debug_name: sign.name.clone(),
                inputs,
                output,
                unhandled,
            },
        );
        self.ir.proc_impl.push_value(ProcImpl::default());

        self.functions
            .insert((fun, params.clone()), ProcType::Top(idx));
        self.proc_todo.push((
            idx,
            ProcCtx {
                idx,
                sign,
                imp,
                handler,
                params,
                regs: imp
                    .blocks
                    .values()
                    .map(|b| b.instructions.values().map(|_| None).collect())
                    .collect(),
                blocks: imp.blocks.values().map(|_| Block::default()).collect(),
                block: BlockIdx(0),
            },
        ));
        ProcType::Top(idx)
    }
    fn get_value_reg(&mut self, ctx: &mut ProcCtx<'a>, value: &'a Value) -> Reg {
        match *value {
            Value::Reg(idx, None) => ctx.blocks[idx].phis[0].0,
            Value::Reg(idx, Some(instr)) => ctx.regs[idx][instr].unwrap(),
            Value::Deref(ref value) => {
                let ptr = self.get_value_reg(ctx, value);

                let inner = self.ir.regs[ptr].inner(&self.ir);
                let reg = self.next_reg(inner);

                ctx.push(Instruction::Load(reg, ptr));
                reg
            }
            Value::ConstantAggregate(ty, ref vals) | Value::ConstantHandler(ty, ref vals) => {
                let vals = vals.iter().map(|v| self.get_value_reg(ctx, v)).collect();

                let ty = self.lower_type(ty, &ctx.params);
                let reg = self.next_reg(ty);
                ctx.push(Instruction::Aggregate(reg, vals));
                reg
            }
            Value::ConstantInt(ty, false, n) => {
                let ty = self.lower_type(ty, &ctx.params);
                let reg = self.next_reg(ty);
                ctx.push(Instruction::Init(reg, n));
                reg
            }
            Value::ConstantInt(_, true, _) => todo!(),
            Value::ConstantString(ty, ref s) => {
                let ty = self.lower_type(ty, &ctx.params);
                let reg = self.next_reg(ty);
                ctx.push(Instruction::InitString(
                    reg,
                    String::from_utf8_lossy(s).into_owned(),
                ));
                reg
            }
            Value::ConstantBool(b) => {
                let ty = self.insert_type(Type::Bool);
                let reg = self.next_reg(ty);
                ctx.push(Instruction::Init(reg, u64::from(b)));
                reg
            }
            Value::ConstantNone => {
                let ty = self.insert_type(Type::Unit);
                let reg = self.next_reg(ty);
                ctx.push(Instruction::Zeroinit(reg));
                reg
            }
            Value::ConstantUninit(ty) => {
                let ty = self.lower_type(ty, &ctx.params);
                let reg = self.next_reg(ty);
                ctx.push(Instruction::Uninit(reg));
                reg
            }
            Value::ConstantZero(ty) => {
                let ty = self.lower_type(ty, &ctx.params);
                let reg = self.next_reg(ty);
                ctx.push(Instruction::Zeroinit(reg));
                reg
            }
            Value::ConstantGeneric(idx) => self.get_value_reg(ctx, get_constant(&ctx.params, idx)),
            Value::Param(n) => self.ir.proc_sign[ctx.idx].inputs[n.0],
            Value::EffectParam(n) => {
                let params = ctx.sign.params.len();
                self.ir.proc_sign[ctx.idx].inputs[params + n]
            }
            Value::Capture(n) => {
                let aggr = self.ir.proc_sign[ctx.idx].inputs.last().copied().unwrap();

                let handler = self.handlers[ctx.handler.unwrap()].0;
                let handler = &self.sema.handlers[handler];

                let inner = self.lower_type(handler.captures[n], &ctx.params);
                let inner_ptr = self.insert_type(Type::Pointer(inner));
                let reg = self.next_reg(inner_ptr);

                ctx.push(Instruction::ElementPtr(reg, aggr, n));
                reg
            }
            Value::ConstantError => unreachable!(),
        }
    }
    fn lower_impl(&mut self, idx: ProcIdx, mut ctx: ProcCtx<'a>) {
        for idx in ctx.blocks.keys(BlockIdx) {
            // generate phi reg
            if let Some((ty, _)) = ctx.imp.blocks[idx].value {
                let ty = self.lower_type(ty, &ctx.params);
                let reg = self.next_reg(ty);
                ctx.blocks[idx].phis = vec![(reg, Vec::new())];
            }

            // generate instruction regs
            for (i, instr) in ctx.imp.blocks[idx].instructions.iter(InstrIdx) {
                use sema::Instruction as I;
                let ty = match *instr {
                    I::Div(ty, _, _)
                    | I::Mul(ty, _, _)
                    | I::Add(ty, _, _)
                    | I::Sub(ty, _, _)
                    | I::Load(ty, _)
                    | I::Cast(_, ty) => self.lower_type(ty, &ctx.params),

                    I::Reference(_, ty) | I::AdjacentPtr(_, _, ty) => {
                        let ty = self.lower_type(ty, &ctx.params);
                        self.insert_type(Type::Pointer(ty))
                    }

                    I::Member(_, n, ty) => {
                        let aggr_ty = self.lower_type(ty, &ctx.params);
                        let aggr = match self.ir.types[aggr_ty] {
                            Type::Aggregate(idx) => idx,
                            _ => unreachable!(),
                        };
                        self.ir.aggregates[aggr].children[n as usize]
                    }

                    I::Equals(_, _) | I::Greater(_, _) | I::Less(_, _) => {
                        self.insert_type(Type::Bool)
                    }

                    I::Call(id, ref params, _, _) => {
                        let params = params
                            .iter()
                            .map(|&(idx, ty)| (idx, self.lower_generic(ty, &ctx.params)))
                            .collect();

                        self.lower_type(id.sign(self.sema).return_type.ty, &params)
                    }
                    I::LinkHandler(_, _) => todo!(),
                    I::AsmHandler(_, _, _, _) => todo!(),
                    I::Syscall(_, _) => self.insert_type(Type::Int),

                    I::Jump(_)
                    | I::Branch(_, _, _)
                    | I::CompileError(_)
                    | I::Store(_, _)
                    | I::Yeet(_, _)
                    | I::Return(_)
                    | I::Unreachable => continue,
                };
                ctx.regs[idx][i] = Some(self.next_reg(ty));
            }
        }

        // generate instructions
        for idx in ctx.blocks.keys(BlockIdx) {
            ctx.block = idx;

            for (i, instr) in ctx.imp.blocks[idx].instructions.iter(InstrIdx) {
                let ireg = ctx.regs[idx][i];

                use sema::Instruction as I;
                match instr {
                    I::Cast(p, _) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        ctx.push(Instruction::Cast(ireg.unwrap(), p));
                    }
                    I::Jump(idx) => ctx.push(Instruction::Jump(*idx)),
                    I::Branch(p, y, n) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        ctx.push(Instruction::Branch(p, *y, *n));
                    }
                    I::Equals(l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Equals(ireg.unwrap(), l, r));
                    }
                    I::Greater(l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Greater(ireg.unwrap(), l, r));
                    }
                    I::Less(l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Less(ireg.unwrap(), l, r));
                    }
                    I::Div(_, l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Div(ireg.unwrap(), l, r));
                    }
                    I::Mul(_, l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Mul(ireg.unwrap(), l, r));
                    }
                    I::Add(_, l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Add(ireg.unwrap(), l, r));
                    }
                    I::Sub(_, l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Sub(ireg.unwrap(), l, r));
                    }
                    I::Call(fun, params, args, effects) => {
                        let effects = effects
                            .iter()
                            .map(|&(ref effect, block)| {
                                (
                                    match effect {
                                        Value::EffectParam(_) => {
                                            // should already be a pointer
                                            self.get_value_reg(&mut ctx, effect)
                                        }
                                        Value::Deref(effectptr) => {
                                            self.get_value_reg(&mut ctx, effectptr)
                                        }
                                        Value::ConstantHandler(_, _) => {
                                            let effect = self.get_value_reg(&mut ctx, effect);

                                            let effect_ty = self.ir.regs[effect];
                                            let effectptr_ty =
                                                self.insert_type(Type::Pointer(effect_ty));
                                            let effectptr = self.next_reg(effectptr_ty);

                                            ctx.push(Instruction::Reference(effectptr, effect));
                                            effectptr
                                        }
                                        _ => unreachable!(),
                                    },
                                    block,
                                )
                            })
                            .collect::<Vec<_>>();

                        // TODO: captured handlers?
                        let handled = effects
                            .iter()
                            .filter_map(|&(e, b)| {
                                let b = b?;

                                let effectptr_ty = self.ir.regs[e];
                                let effect_ty = effectptr_ty.inner(&self.ir);
                                let handler = match self.ir.types[effect_ty] {
                                    Type::Handler(idx, _) => idx,
                                    _ => unreachable!(),
                                };
                                if matches!(
                                    self.ir.types[self.ir.break_types[handler]],
                                    Type::Never
                                ) {
                                    None?;
                                }

                                Some((handler, b))
                            })
                            .collect::<Vec<_>>();

                        let args = args
                            .iter()
                            .map(|arg| self.get_value_reg(&mut ctx, arg))
                            .chain(effects.iter().map(|&(e, _)| e))
                            .collect::<Vec<_>>();

                        let params = params
                            .iter()
                            .map(|&(idx, ty)| (idx, self.lower_generic(ty, &ctx.params)))
                            .collect();
                        let proc = self.lower_sign(
                            *fun,
                            params,
                            args.iter().map(|&r| self.ir.regs[r]).collect(),
                            effects
                                .iter()
                                .map(|&(r, _)| self.ir.regs[r].inner(&self.ir))
                                .collect(),
                            self.ir.regs[ireg.unwrap()],
                        );
                        match proc {
                            ProcType::Top(idx) => {
                                ctx.push(Instruction::Call(idx, ireg, args, handled))
                            }
                            ProcType::Foreign(idx) => {
                                ctx.push(Instruction::CallForeign(idx, ireg, args))
                            }
                        }
                    }
                    I::Yeet(p, b) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        if let Some(b) = *b {
                            ctx.push(Instruction::Yeet(Some(p), None, Some(b)));
                        } else {
                            ctx.push(Instruction::Yeet(Some(p), Some(ctx.handler.unwrap()), None));
                        }
                    }
                    I::Return(p) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        ctx.push(Instruction::Return(Some(p)));
                    }
                    I::Unreachable => {
                        ctx.push(Instruction::Unreachable);
                    }
                    I::Reference(p, _) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        ctx.push(Instruction::Reference(ireg.unwrap(), p));
                    }
                    I::Load(_, p) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        ctx.push(Instruction::Load(ireg.unwrap(), p));
                    }
                    I::Store(l, r) => {
                        let l = self.get_value_reg(&mut ctx, l);
                        let r = self.get_value_reg(&mut ctx, r);
                        ctx.push(Instruction::Store(l, r));
                    }
                    I::Member(p, n, _) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        ctx.push(Instruction::Member(ireg.unwrap(), p, *n as usize));
                    }
                    I::AdjacentPtr(p, n, _) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        let n = self.get_value_reg(&mut ctx, n);
                        ctx.push(Instruction::AdjacentPtr(ireg.unwrap(), p, n));
                    }
                    I::LinkHandler(_, _) => todo!(),
                    I::AsmHandler(_, _, _, _) => todo!(),
                    I::CompileError(_) => todo!(),
                    I::Syscall(nr, args) => {
                        let nr = self.get_value_reg(&mut ctx, nr);
                        let args = self.get_value_reg(&mut ctx, args);

                        let ty = self.ir.regs[args];
                        let n = match self.ir.types[ty] {
                            Type::ConstArray(n, _) => n,
                            _ => unreachable!(),
                        };

                        let int = self.insert_type(Type::Int);
                        let args = (0..n)
                            .map(|i| {
                                let arg = self.next_reg(int);
                                ctx.push(Instruction::Member(arg, args, i as usize));
                                arg
                            })
                            .collect();

                        ctx.push(Instruction::Syscall(ireg, nr, args));
                    }
                }
            }
        }

        // generate phi incoming
        for idx in ctx.blocks.keys(BlockIdx) {
            if let Some((_, ref phis)) = ctx.imp.blocks[idx].value {
                let incoming = phis
                    .iter()
                    .map(|&(ref val, idx)| {
                        ctx.block = idx;

                        let instr = ctx.blocks[ctx.block].instructions.pop().unwrap();
                        let reg = self.get_value_reg(&mut ctx, val);
                        ctx.push(instr);

                        (reg, idx)
                    })
                    .collect();
                ctx.blocks[idx].phis[0].1 = incoming;
            }
        }

        // set proc
        self.ir.proc_impl[idx].blocks = ctx.blocks;
    }
}

pub fn codegen(sema: &SemIR, errors: &mut Errors, target: &Target) -> IR {
    let mut ctx = IRCtx {
        ir: IR {
            proc_sign: VecMap::new(),
            proc_impl: VecMap::new(),
            proc_foreign: VecMap::new(),
            entry: ProcIdx(0),
            regs: VecMap::new(),
            types: VecSet::new(),
            break_types: VecMap::new(),
            aggregates: VecMap::new(),
            links: HashSet::new(),
        },
        sema,
        errors,
        slice_types: HashMap::new(),
        proc_todo: Vec::new(),
        handler_types: HashMap::new(),
        functions: HashMap::new(),
        handlers: VecMap::new(),
    };

    let unit = ctx.insert_type(Type::Unit);
    ctx.lower_sign(
        FunIdent::Top(sema.entry),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        unit,
    );
    while let Some((idx, pctx)) = ctx.proc_todo.pop() {
        ctx.lower_impl(idx, pctx);
    }

    ctx.ir
}
