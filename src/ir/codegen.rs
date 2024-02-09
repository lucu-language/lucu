use std::collections::{hash_map::Entry, HashMap, HashSet};

use crate::{
    ast::{EffFunIdx, EffIdx, StructIdx},
    error::Errors,
    sema::{
        self, get_value, BlockIdx, EffectIdent, FunIdent, FunImpl, FunSign, GenericIdx, GenericVal,
        InstrIdx, IntSize, LazyIdx, LazyValue, SemIR, Value,
    },
    vecmap::{VecMap, VecSet},
    Target,
};

use super::{
    AggrIdx, AggregateType, Block, HandlerIdx, Instruction, ProcForeign, ProcForeignIdx, ProcIdx,
    ProcImpl, ProcSign, Reg, Type, TypeIdx, ASM, IR,
};

struct IRCtx<'a> {
    ir: IR,
    target: &'a Target,
    sema: &'a SemIR,
    errors: &'a mut Errors,

    proc_todo: Vec<(ProcIdx, ProcCtx<'a>)>,
    functions: HashMap<(FunIdent, GenericParams<'a>), ProcType>,

    handlers: VecMap<HandlerIdx, (Option<sema::HandlerIdx>, GenericParams<'a>)>,

    slice_types: HashMap<TypeIdx, AggrIdx>,
    struct_types: VecMap<StructIdx, AggrIdx>,
    handler_types: HashMap<(sema::HandlerIdx, GenericParams<'a>), TypeIdx>,
    foreign_types: HashMap<(EffIdx, GenericParams<'a>, Option<ASM>), TypeIdx>,
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

fn get_effect<'a, 'b>(params: &GenericParams<'a>, idx: GenericIdx) -> (EffIdx, GenericParams<'a>) {
    match get_param(params, idx).unwrap() {
        Generic::Effect(idx, params) => (idx, params),
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
            T::Struct(idx) => {
                let aggr = self.struct_types[idx];
                self.insert_type(Type::Aggregate(aggr))
            }
            T::Handler(l) => self.lower_lazy(l.idx, params),
            T::Generic(g) => {
                return get_param(&params, g.idx).unwrap();
            }
            T::Pointer(_, ty) | T::MaybePointer(_, ty) => {
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
            T::Slice(_, ty) => {
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
    fn foreign_handler(
        &mut self,
        e: &GenericVal<EffectIdent>,
        asm: Option<ASM>,
        params: &GenericParams<'a>,
    ) -> TypeIdx {
        let (effect, params) = match *e {
            GenericVal::Literal(ref ident) => (
                ident.effect,
                ident
                    .generic_params
                    .iter()
                    .map(|&(idx, ty)| (idx, self.lower_generic(ty, params)))
                    .collect(),
            ),
            GenericVal::Generic(idx) => get_effect(params, idx),
        };

        let ident = (effect, params, asm);
        if let Some(ty) = self.foreign_types.get(&ident).copied() {
            return ty;
        }
        let (effect, params, asm) = ident;

        let sema_effect = &self.sema.effects[effect];
        let prefix = sema_effect
            .foreign
            .as_ref()
            .map(|f| f.prefix.as_str())
            .unwrap_or("");

        let ty = self.new_implicit_handler(effect);

        for (idx, fun) in sema_effect.funs.iter(EffFunIdx) {
            let symbol = format!("{}{}", prefix, fun.name);
            let inputs = fun
                .params
                .values()
                .map(|p| self.lower_type(p.ty, &params))
                .collect::<Vec<_>>();
            let output = self.lower_type(fun.return_type.ty, &params);

            let mut fun_params = params.clone();
            fun_params.push((fun.generics.last().unwrap().idx, Generic::Type(ty)));

            let proc = self.ir.proc_foreign.push(
                ProcForeignIdx,
                ProcForeign {
                    inputs,
                    output,
                    symbol,
                    asm: asm.clone(),
                },
            );
            self.functions.insert(
                (FunIdent::Effect(effect, idx), fun_params),
                ProcType::Foreign(proc),
            );
        }

        self.foreign_types.insert((effect, params, asm), ty);
        ty
    }
    fn new_implicit_handler(&mut self, effect: EffIdx) -> TypeIdx {
        let aggr = self.ir.aggregates.push(
            AggrIdx,
            AggregateType {
                children: Vec::new(),
                debug_name: format!("F{}", effect.0),
            },
        );

        let idx = self.handlers.push(HandlerIdx, (None, Vec::new()));

        let never = self.insert_type(Type::Never);
        self.ir.break_types.push_value(never);

        self.insert_type(Type::Handler(idx, aggr))
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

                let idx = self
                    .handlers
                    .push(HandlerIdx, (Some(ident.0), ident.1.clone()));
                self.ir.break_types.push_value(break_type);

                let ty = self.insert_type(Type::Handler(idx, aggr));
                self.handler_types.insert(ident, ty);
                ty
            }
            LazyValue::Some(GenericVal::Generic(idx)) => get_type(params, *idx),
            LazyValue::EffectFunOutput(idx, fun, ps) => {
                let handler = self.lower_lazy(*idx, params);
                let handler = match self.ir.types[handler] {
                    Type::Handler(idx, _) => idx,
                    _ => unreachable!(),
                };
                let (idx, ref handler_params) = self.handlers[handler];
                let params = Iterator::chain(
                    handler_params.clone().into_iter(),
                    ps.iter()
                        .map(|&(idx, ty)| (idx, self.lower_generic(ty, &params))),
                )
                .collect::<Vec<_>>();

                let idx = idx.unwrap();
                if self.sema.foreign_handler == idx {
                    match fun {
                        EffFunIdx(0) => {
                            // link handler
                            let lib = GenericVal::Generic(ps[0].0);
                            let lib = match lib {
                                GenericVal::Literal(s) => s,
                                GenericVal::Generic(g) => match get_constant(&params, g) {
                                    Value::ConstantString(_, s) => {
                                        String::from_utf8_lossy(s).into_owned()
                                    }
                                    _ => unreachable!(),
                                },
                            };
                            self.ir.links.insert(lib);

                            let effect = GenericVal::Generic(ps[1].0);
                            self.foreign_handler(&effect, None, &params)
                        }
                        EffFunIdx(1) => {
                            // link asm
                            let assembly = GenericVal::Generic(ps[0].0);
                            let assembly = match assembly.clone() {
                                GenericVal::Literal(s) => s,
                                GenericVal::Generic(g) => match get_constant(&params, g) {
                                    Value::ConstantString(_, s) => {
                                        String::from_utf8_lossy(s).into_owned()
                                    }
                                    _ => unreachable!(),
                                },
                            };
                            let constraints = GenericVal::Generic(ps[1].0);
                            let constraints = match constraints.clone() {
                                GenericVal::Literal(s) => s,
                                GenericVal::Generic(g) => match get_constant(&params, g) {
                                    Value::ConstantString(_, s) => {
                                        String::from_utf8_lossy(s).into_owned()
                                    }
                                    _ => unreachable!(),
                                },
                            };
                            let sideeffects = GenericVal::Generic(ps[2].0);
                            let sideeffects = match sideeffects {
                                GenericVal::Literal(b) => b,
                                GenericVal::Generic(g) => match get_constant(&params, g) {
                                    &Value::ConstantBool(b) => b,
                                    _ => unreachable!(),
                                },
                            };

                            let effect = GenericVal::Generic(ps[3].0);
                            self.foreign_handler(
                                &effect,
                                Some(ASM {
                                    assembly,
                                    constraints,
                                    sideeffects,
                                }),
                                &params,
                            )
                        }
                        _ => unreachable!(),
                    }
                } else {
                    self.lower_type(self.sema.handlers[idx].funs[*fun].0.return_type.ty, &params)
                }
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
        return_type: TypeIdx,
    ) -> ProcType {
        let (imp, handler) = match fun {
            FunIdent::Top(idx) => (Some(&self.sema.fun_impl[idx]), None),
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
                    handler.0.map(|h| &self.sema.handlers[h].funs[idx].1),
                    Some(handler_idx),
                )
            }
        };

        let ident = (fun, params);
        if let Some(idx) = self.functions.get(&ident).copied() {
            return idx;
        }
        let (fun, params) = ident;

        let imp = imp.unwrap();
        let inputs = inputs.into_iter().map(|ty| self.next_reg(ty)).collect();
        let output = return_type;

        let sign = fun.sign(self.sema);
        let idx = self.ir.proc_sign.push(
            ProcIdx,
            ProcSign {
                debug_name: sign.name.clone(),
                inputs,
                output,
                unhandled: vec![],
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
            Value::Deref(ref value, _) => {
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
            Value::ConstantSizeOf(ty) => {
                let ty = self.lower_type(ty, &ctx.params);
                let size = self.sizeof(ty);

                let int_ty = self.insert_type(Type::IntSize);
                let reg = self.next_reg(int_ty);
                ctx.push(Instruction::Init(reg, size));
                reg
            }
            Value::ConstantAlignOf(ty) => {
                let ty = self.lower_type(ty, &ctx.params);
                let align = self.alignof(ty);

                let int_ty = self.insert_type(Type::Int8);
                let reg = self.next_reg(int_ty);
                ctx.push(Instruction::Init(reg, align));
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

                let handler = self.handlers[ctx.handler.unwrap()].0.unwrap();
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

                    I::ElementPtr(_, n, ty) => {
                        let aggr_ty = self.lower_type(ty, &ctx.params);
                        let aggr = match self.ir.types[aggr_ty] {
                            Type::Aggregate(idx) => idx,
                            _ => unreachable!(),
                        };
                        let elem_ty = self.ir.aggregates[aggr].children[n as usize];
                        self.insert_type(Type::Pointer(elem_ty))
                    }

                    I::Equals(_, _) | I::Greater(_, _) | I::Less(_, _) => {
                        self.insert_type(Type::Bool)
                    }

                    I::Call(id, ref params, _, _, _) => {
                        let mut params = params
                            .iter()
                            .map(|&(idx, ty)| (idx, self.lower_generic(ty, &ctx.params)))
                            .collect::<Vec<_>>();
                        let sign = match id {
                            FunIdent::Top(idx) => &self.sema.fun_sign[idx],
                            FunIdent::Effect(eff, idx) => {
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

                                match handler.0 {
                                    Some(h) => {
                                        // handler
                                        &self.sema.handlers[h].funs[idx].0
                                    }
                                    None => {
                                        // foreign
                                        &self.sema.effects[eff].funs[idx]
                                    }
                                }
                            }
                        };
                        self.lower_type(sign.return_type.ty, &params)
                    }
                    I::LinkHandler(_, _) | I::AsmHandler(_, _, _, _) => {
                        self.ir.proc_sign[ctx.idx].output
                    }
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
                    I::Call(fun, params, args, effects, handled) => {
                        let effects = effects
                            .iter()
                            .map(|effect| match effect {
                                Value::Deref(effectptr, _) => {
                                    self.get_value_reg(&mut ctx, effectptr)
                                }
                                _ => {
                                    let effect = self.get_value_reg(&mut ctx, effect);

                                    let effect_ty = self.ir.regs[effect];
                                    let effectptr_ty = self.insert_type(Type::Pointer(effect_ty));
                                    let effectptr = self.next_reg(effectptr_ty);

                                    ctx.push(Instruction::Reference(effectptr, effect));
                                    effectptr
                                }
                            })
                            .collect::<Vec<_>>();

                        let handled = handled
                            .iter()
                            .filter_map(|&(e, b)| {
                                let effect_ty = self.lower_type(e, &ctx.params);
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

                        let arg_count = args.len();
                        let args = args
                            .iter()
                            .map(|arg| self.get_value_reg(&mut ctx, arg))
                            .chain(effects)
                            .collect::<Vec<_>>();

                        let params = params
                            .iter()
                            .map(|&(idx, ty)| (idx, self.lower_generic(ty, &ctx.params)))
                            .collect();
                        let proc = self.lower_sign(
                            *fun,
                            params,
                            args.iter().map(|&r| self.ir.regs[r]).collect(),
                            self.ir.regs[ireg.unwrap()],
                        );
                        match proc {
                            ProcType::Top(idx) => {
                                ctx.push(Instruction::Call(idx, ireg, args, handled))
                            }
                            ProcType::Foreign(idx) => ctx.push(Instruction::CallForeign(
                                idx,
                                ireg,
                                args.into_iter().take(arg_count).collect(),
                            )),
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
                    I::ElementPtr(p, n, _) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        ctx.push(Instruction::ElementPtr(ireg.unwrap(), p, *n as usize));
                    }
                    I::AdjacentPtr(p, n, _) => {
                        let p = self.get_value_reg(&mut ctx, p);
                        let n = self.get_value_reg(&mut ctx, n);
                        ctx.push(Instruction::AdjacentPtr(ireg.unwrap(), p, n));
                    }
                    I::LinkHandler(_, _) | I::AsmHandler(_, _, _, _) => {
                        ctx.push(Instruction::Aggregate(ireg.unwrap(), Vec::new()));
                    }
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

    fn sizeof(&self, ty: TypeIdx) -> u64 {
        let arch = self.target.lucu_arch();
        match self.ir.types[ty] {
            Type::Int => arch.register_size().div_ceil(8) as u64,
            Type::IntSize => arch.array_len_size().div_ceil(8) as u64,
            Type::IntPtr => arch.ptr_size().div_ceil(8) as u64,
            Type::Int8 => 1,
            Type::Int16 => 2,
            Type::Int32 => 4,
            Type::Int64 => 8,
            Type::Bool => 1,
            Type::Pointer(_) => arch.ptr_size().div_ceil(8) as u64,
            Type::ConstArray(len, inner) => self.sizeof(inner) * len,
            Type::Aggregate(idx) | Type::Handler(_, idx) => {
                let mut size = 0;
                for child in self.ir.aggregates[idx].children.iter().copied() {
                    // round up to child align
                    let align_mask = (1 << self.alignof(child)) - 1;
                    size = size + align_mask & !align_mask;

                    // add child
                    size += self.sizeof(child);
                }

                // round up to align
                let align_mask = (1 << self.alignof(ty)) - 1;
                size + align_mask & !align_mask
            }
            Type::Unit => 0,
            Type::Never => 0,
        }
    }

    fn alignof(&self, ty: TypeIdx) -> u64 {
        let arch = self.target.lucu_arch();
        match self.ir.types[ty] {
            Type::Int => ilog2_ceil(arch.register_size().div_ceil(8)) as u64,
            Type::IntSize => ilog2_ceil(arch.array_len_size().div_ceil(8)) as u64,
            Type::IntPtr => ilog2_ceil(arch.ptr_size().div_ceil(8)) as u64,
            Type::Int8 => 0,
            Type::Int16 => 1,
            Type::Int32 => 2,
            Type::Int64 => 3,
            Type::Bool => 0,
            Type::Pointer(_) => ilog2_ceil(arch.ptr_size().div_ceil(8)) as u64,
            Type::ConstArray(_, inner) => self.alignof(inner),
            Type::Aggregate(idx) | Type::Handler(_, idx) => self.ir.aggregates[idx]
                .children
                .iter()
                .copied()
                .map(|ty| self.alignof(ty))
                .max()
                .unwrap_or(0),
            Type::Unit => 0,
            Type::Never => 0,
        }
    }
}

fn ilog2_ceil(n: u32) -> u32 {
    if n < 2 {
        0
    } else {
        (n - 1).ilog2() + 1
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
            links: HashSet::new(),
            aggregates: std::iter::repeat_with(AggregateType::default)
                .take(sema.structs.len())
                .collect(),
        },
        sema,
        errors,
        target,
        slice_types: HashMap::new(),
        proc_todo: Vec::new(),
        handler_types: HashMap::new(),
        foreign_types: HashMap::new(),
        functions: HashMap::new(),
        handlers: VecMap::new(),
        struct_types: sema
            .structs
            .keys(StructIdx)
            .map(|idx| AggrIdx(idx.0))
            .collect(),
    };

    for (idx, struc) in sema.structs.iter(StructIdx) {
        let children = struc
            .elems
            .iter()
            .map(|&(_, ty)| ctx.lower_type(ty, &Vec::new()))
            .collect();

        let idx = ctx.struct_types[idx];
        ctx.ir.aggregates[idx].children = children;
        ctx.ir.aggregates[idx].debug_name = struc.name.clone();
    }

    let unit = ctx.insert_type(Type::Unit);
    ctx.lower_sign(FunIdent::Top(sema.entry), Vec::new(), Vec::new(), unit);
    while let Some((idx, pctx)) = ctx.proc_todo.pop() {
        ctx.lower_impl(idx, pctx);
    }

    // calculate unhandled from yeet
    for idx in ctx.ir.proc_impl.keys(ProcIdx) {
        for instr in ctx.ir.proc_impl[idx].instructions() {
            if let Instruction::Yeet(_, Some(handler), None) = *instr {
                let unhandled = &mut ctx.ir.proc_sign[idx].unhandled;
                if !unhandled.contains(&handler) {
                    unhandled.push(handler);
                }
            }
        }
    }

    // bubble up unhandled
    let mut bubbled = true;
    while bubbled {
        bubbled = false;
        for idx1 in ctx.ir.proc_impl.keys(ProcIdx) {
            for instr in ctx.ir.proc_impl[idx1].instructions() {
                if let Instruction::Call(idx2, _, _, ref handled) = *instr {
                    let unhandled1 = &ctx.ir.proc_sign[idx1].unhandled;
                    let unhandled2 = ctx.ir.proc_sign[idx2]
                        .unhandled
                        .iter()
                        .copied()
                        .filter(|h| {
                            !handled.iter().any(|(h2, _)| h2 == h) && !unhandled1.contains(h)
                        })
                        .collect::<Vec<_>>();

                    if !unhandled2.is_empty() {
                        ctx.ir.proc_sign[idx1].unhandled.extend(unhandled2);
                        bubbled = true;
                    }
                }
            }
        }
    }

    ctx.ir
}
