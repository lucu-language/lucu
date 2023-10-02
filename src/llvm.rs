use std::{collections::HashMap, path::Path};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::PassManager,
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetTriple,
    },
    types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicTypeEnum, IntType, StructType},
    values::{BasicValue, BasicValueEnum, CallSiteValue, FunctionValue, IntValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    ir::{AggregateType, HandlerIdx, Instruction, ProcIdx, Procedure, Type, TypeIdx, IR},
    vecmap::VecMap,
};

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    target_data: TargetData,

    structs: VecMap<TypeIdx, Option<StructType<'ctx>>>,
    procs: VecMap<ProcIdx, FunctionValue<'ctx>>,

    putint: FunctionValue<'ctx>,
}

pub fn generate_ir(ir: &IR, path: &Path, debug: bool) {
    Target::initialize_x86(&InitializationConfig::default());

    let context = Context::create();
    let module = context.create_module("main");
    let target = Target::from_name("x86-64").unwrap();
    let target_machine = target
        .create_target_machine(
            &TargetTriple::create("x86_64-pc-linux-gnu"),
            "x86-64",
            "+avx2",
            OptimizationLevel::Aggressive,
            RelocMode::Default,
            CodeModel::Default,
        )
        .unwrap();
    let target_data = target_machine.get_target_data();

    let putint = module.add_function(
        "putint",
        context
            .void_type()
            .fn_type(&[context.i64_type().into()], false),
        Some(Linkage::External),
    );
    putint.set_call_conventions(0);

    let mut codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        target_data,
        structs: VecMap::new(),
        procs: VecMap::new(),
        putint,
    };

    for typ in ir.aggregates.values() {
        let struc = codegen.generate_struct(typ);
        codegen.structs.push_value(struc);
    }

    for proc in ir.procs.values() {
        let func = codegen.generate_proc_sign(ir, proc);
        codegen.procs.push_value(func);
    }

    for (proc, function) in ir.procs.values().zip(codegen.procs.values().copied()) {
        codegen.generate_proc(ir, proc, function);
    }

    // set main func
    codegen.procs[ir.main].set_linkage(Linkage::External);

    // assume valid
    codegen.module.verify().unwrap();

    // compile
    let pm = PassManager::create(());
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();
    pm.add_gvn_pass();
    pm.add_cfg_simplification_pass();
    pm.add_basic_alias_analysis_pass();
    pm.add_promote_memory_to_register_pass();
    pm.add_instruction_combining_pass();
    pm.add_reassociate_pass();
    pm.run_on(&codegen.module);

    if debug {
        codegen.module.print_to_stderr();
    }

    target_machine
        .write_to_file(&codegen.module, FileType::Object, path)
        .unwrap();
}

impl<'ctx> CodeGen<'ctx> {
    fn generate_struct(&self, typ: &AggregateType) -> Option<StructType<'ctx>> {
        let fields: Vec<BasicTypeEnum> = typ
            .children
            .iter()
            .filter_map(|typ| BasicTypeEnum::try_from(self.get_type(typ)).ok())
            .collect();

        if fields.is_empty() {
            None
        } else {
            Some(self.context.struct_type(&fields, false))
        }
    }
    fn frame_type(&self) -> IntType<'ctx> {
        self.context.i64_type()
    }
    fn generate_proc_sign(&self, ir: &IR, proc: &Procedure) -> FunctionValue<'ctx> {
        let in_types: Vec<_> = proc
            .inputs
            .iter()
            .filter_map(|&r| BasicMetadataTypeEnum::try_from(self.get_type(&ir.types[r])).ok())
            .collect();

        let fn_type = if proc.can_break {
            let frame_type = self.frame_type();
            let out_type = self.get_type(&proc.output);
            if let Ok(basic) = BasicTypeEnum::try_from(out_type) {
                self.context
                    .struct_type(&[frame_type.into(), basic], false)
                    .fn_type(&in_types, false)
            } else {
                frame_type.fn_type(&in_types, false)
            }
        } else {
            match proc.output {
                Type::Int => self.context.i64_type().fn_type(&in_types, false),
                Type::BytePointer => self
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::default())
                    .fn_type(&in_types, false),
                Type::ArraySize => self
                    .context
                    .ptr_sized_int_type(&self.target_data, None)
                    .fn_type(&in_types, false),
                Type::Aggregate(idx) => match self.structs[idx] {
                    Some(t) => t.fn_type(&in_types, false),
                    None => self.context.void_type().fn_type(&in_types, false),
                },
                Type::Never | Type::None => self.context.void_type().fn_type(&in_types, false),
            }
        };

        self.module
            .add_function(&proc.debug_name, fn_type, Some(Linkage::Internal))
    }
    fn generate_proc(&self, ir: &IR, proc: &Procedure, function: FunctionValue<'ctx>) {
        let mut blocks: Vec<_> = (0..proc.blocks.len())
            .map(|idx| {
                self.context
                    .append_basic_block(function, &format!("L{}", idx))
            })
            .collect();

        let mut valmap = HashMap::new();
        for (n, &reg) in proc
            .inputs
            .iter()
            .filter(|&&r| !self.get_type(&ir.types[r]).is_void_type())
            .enumerate()
        {
            valmap.insert(reg, function.get_nth_param(n as u32).unwrap());
        }

        'outer: for (idx, block) in proc.blocks.values().enumerate() {
            let basic_block = blocks[idx];
            self.builder.position_at_end(basic_block);

            for instr in block.instructions.iter() {
                use Instruction as I;
                match *instr {
                    I::Init(r, v) => {
                        valmap.insert(r, self.context.i64_type().const_int(v, false).into());
                    }
                    I::InitString(r, ref v) => {
                        let slice_type = self.get_type(&ir.types[r]).into_struct_type();
                        let array_size_type =
                            self.context.ptr_sized_int_type(&self.target_data, None);

                        let const_str = self.context.const_string(v.as_bytes(), false);

                        let global_str = self.module.add_global(const_str.get_type(), None, "");
                        global_str.set_linkage(Linkage::Internal);
                        global_str.set_constant(true);
                        global_str.set_initializer(&const_str);

                        let const_str_slice = slice_type.const_named_struct(&[
                            global_str.as_pointer_value().into(),
                            array_size_type
                                .const_int(const_str.get_type().len() as u64, false)
                                .into(),
                        ]);

                        valmap.insert(r, const_str_slice.into());
                    }
                    I::JmpNZ(r, yes) => {
                        let no = block.next.unwrap();
                        self.builder
                            .build_conditional_branch(
                                valmap[&r].into_int_value(),
                                blocks[usize::from(yes)],
                                blocks[usize::from(no)],
                            )
                            .unwrap();
                        continue 'outer;
                    }
                    I::Phi(r, [(r1, b1), (r2, b2)]) => {
                        let typ = BasicTypeEnum::try_from(self.get_type(&ir.types[r])).ok();

                        if let Some(typ) = typ {
                            let phi = self.builder.build_phi(typ, "").unwrap();
                            phi.add_incoming(&[
                                (&valmap[&r1], blocks[usize::from(b1)]),
                                (&valmap[&r2], blocks[usize::from(b2)]),
                            ]);
                            valmap.insert(r, phi.as_basic_value());
                        }
                    }
                    I::Equals(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::EQ, lhs, rhs, "")
                            .unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Div(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_signed_div(lhs, rhs, "").unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Mul(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_mul(lhs, rhs, "").unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Add(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_add(lhs, rhs, "").unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Sub(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_sub(lhs, rhs, "").unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Reset(p, r, ref rs, h) => {
                        let func = self.procs[p];
                        let args: Vec<_> = rs
                            .iter()
                            .filter_map(|r| valmap.get(r).map(|&v| v.into()))
                            .collect();

                        let ret = self.builder.build_call(func, &args, "").unwrap();
                        let (frame, val) = self.get_return(&ir.procs[p], ret);

                        if let Some(frame) = frame {
                            if proc.can_break {
                                blocks[idx] = self.handle_break(function, frame, Some(h));
                            }
                        }

                        if let Some(r) = r {
                            valmap.insert(
                                r,
                                val.expect(&format!(
                                    "call {} returns no value",
                                    ir.procs[p].debug_name
                                )),
                            );
                        }
                    }
                    I::Call(p, r, ref rs) => {
                        let func = self.procs[p];
                        let args: Vec<_> = rs
                            .iter()
                            .filter_map(|r| valmap.get(r).map(|&v| v.into()))
                            .collect();

                        let ret = self.builder.build_call(func, &args, "").unwrap();
                        let (frame, val) = self.get_return(&ir.procs[p], ret);

                        if let Some(frame) = frame {
                            blocks[idx] = self.handle_break(function, frame, None);
                        }

                        if let Some(r) = r {
                            valmap.insert(
                                r,
                                val.expect(&format!(
                                    "call {} returns no value",
                                    ir.procs[p].debug_name
                                )),
                            );
                        }
                    }
                    I::Break(r, h) => {
                        if r.is_some() {
                            todo!("break with value");
                        }

                        let frame = self.frame_type().const_int(usize::from(h) as u64, false);

                        if let Some(BasicTypeEnum::StructType(ret)) =
                            function.get_type().get_return_type()
                        {
                            self.builder
                                .build_return(Some(&ret.const_named_struct(&[
                                    match ret.get_field_type_at_index(1).unwrap() {
                                        BasicTypeEnum::ArrayType(t) => t.get_poison().into(),
                                        BasicTypeEnum::FloatType(t) => t.get_poison().into(),
                                        BasicTypeEnum::IntType(t) => t.get_poison().into(),
                                        BasicTypeEnum::PointerType(t) => t.get_poison().into(),
                                        BasicTypeEnum::StructType(t) => t.get_poison().into(),
                                        BasicTypeEnum::VectorType(t) => t.get_poison().into(),
                                    },
                                ])))
                                .unwrap();
                        } else {
                            self.builder.build_return(Some(&frame)).unwrap();
                        }
                    }
                    I::Return(r) => {
                        if proc.can_break {
                            if let Some(&r) = r.and_then(|r| valmap.get(&r)) {
                                let ret_typ = function
                                    .get_type()
                                    .get_return_type()
                                    .unwrap()
                                    .into_struct_type();

                                let mut ret = ret_typ.get_poison();

                                ret = self
                                    .builder
                                    .build_insert_value(
                                        ret,
                                        self.frame_type().const_int(0, false),
                                        0,
                                        "",
                                    )
                                    .unwrap()
                                    .into_struct_value();
                                ret = self
                                    .builder
                                    .build_insert_value(ret, r, 1, "")
                                    .unwrap()
                                    .into_struct_value();

                                self.builder.build_return(Some(&ret)).unwrap();
                            } else {
                                self.builder
                                    .build_return(Some(&self.frame_type().const_int(0, false)))
                                    .unwrap();
                            }
                        } else {
                            self.builder
                                .build_return(r.map(|reg| -> &dyn BasicValue { &valmap[&reg] }))
                                .unwrap();
                        }
                    }
                    I::PrintNum(r) => {
                        self.builder
                            .build_call(self.putint, &[valmap[&r].into()], "")
                            .unwrap();
                    }
                    I::PrintStr(_) => {
                        todo!();
                    }
                    I::Aggregate(r, ref rs) => {
                        let aggr_ty = self.get_type(&ir.types[r]);

                        // do not aggregate void
                        if !aggr_ty.is_void_type() {
                            let aggr_ty = aggr_ty.into_struct_type();

                            let mut aggr = aggr_ty.get_poison();
                            for (n, &member) in rs.iter().filter_map(|r| valmap.get(r)).enumerate()
                            {
                                aggr = self
                                    .builder
                                    .build_insert_value(aggr, member, n as u32, "")
                                    .unwrap()
                                    .into_struct_value();
                            }

                            valmap.insert(r, aggr.into());
                        }
                    }
                    I::Member(r, a, n) => {
                        // skip over empty children that are uncounted
                        let Type::Aggregate(t) = ir.types[a] else { panic!() };
                        let n = ir.aggregates[t]
                            .children
                            .iter()
                            .enumerate()
                            .filter_map(|(i, t)| {
                                if self.get_type(t).is_void_type() {
                                    None
                                } else {
                                    Some(i)
                                }
                            })
                            .position(|i| i == n);

                        // get member
                        if let Some(n) = n {
                            let aggr = valmap[&a].into_struct_value();

                            let member = self
                                .builder
                                .build_extract_value(aggr, n as u32, "")
                                .unwrap();

                            valmap.insert(r, member);
                        }
                    }
                    I::Unreachable => {
                        self.builder.build_unreachable().unwrap();
                        continue 'outer;
                    }
                }
            }

            if let Some(block) = block.next {
                self.builder
                    .build_unconditional_branch(blocks[usize::from(block)])
                    .unwrap();
            }
        }
    }
    fn handle_break(
        &self,
        function: FunctionValue<'ctx>,
        frame: IntValue,
        handler: Option<HandlerIdx>,
    ) -> BasicBlock<'ctx> {
        let cmp_zero = self
            .builder
            .build_int_compare(
                IntPredicate::EQ,
                frame,
                self.frame_type().const_int(0, false),
                "",
            )
            .unwrap();

        let cmp = if let Some(handler) = handler {
            let cmp_handler = self
                .builder
                .build_int_compare(
                    IntPredicate::EQ,
                    frame,
                    self.frame_type()
                        .const_int(usize::from(handler) as u64, false),
                    "",
                )
                .unwrap();
            self.builder.build_or(cmp_zero, cmp_handler, "").unwrap()
        } else {
            cmp_zero
        };

        let branch_next = self.context.append_basic_block(function, "");
        let branch_return = self.context.append_basic_block(function, "");
        self.builder
            .build_conditional_branch(cmp, branch_next, branch_return)
            .unwrap();

        self.builder.position_at_end(branch_return);
        let ret_type = function.get_type().get_return_type();
        if let Some(BasicTypeEnum::StructType(ret_type)) = ret_type {
            let mut ret = ret_type.get_poison();
            ret = self
                .builder
                .build_insert_value(ret, frame, 0, "")
                .unwrap()
                .into_struct_value();
            self.builder.build_return(Some(&ret)).unwrap();
        } else {
            self.builder.build_return(Some(&frame)).unwrap();
        }

        self.builder.position_at_end(branch_next);
        branch_next
    }
    fn get_return(
        &self,
        proc: &Procedure,
        ret: CallSiteValue<'ctx>,
    ) -> (Option<IntValue<'ctx>>, Option<BasicValueEnum<'ctx>>) {
        let (frame, val) = if proc.can_break {
            let ret = ret.try_as_basic_value().unwrap_left();
            if ret.is_struct_value() {
                let ret = ret.into_struct_value();

                let frame = self.builder.build_extract_value(ret, 0, "").unwrap();
                let val = self.builder.build_extract_value(ret, 1, "").unwrap();

                (Some(frame.into_int_value()), Some(val))
            } else {
                (Some(ret.into_int_value()), None)
            }
        } else {
            (None, ret.try_as_basic_value().left())
        };
        (frame, val)
    }
    fn get_type(&self, typ: &Type) -> AnyTypeEnum<'ctx> {
        match *typ {
            Type::Int => self.context.i64_type().into(),
            Type::BytePointer => self
                .context
                .i8_type()
                .ptr_type(AddressSpace::default())
                .into(),
            Type::ArraySize => self
                .context
                .ptr_sized_int_type(&self.target_data, None)
                .into(),
            Type::Aggregate(idx) => match self.structs[idx] {
                Some(t) => t.into(),
                None => self.context.void_type().into(),
            },
            Type::Never | Type::None => self.context.void_type().into(),
        }
    }
}