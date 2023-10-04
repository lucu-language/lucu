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
    values::{BasicValue, BasicValueEnum, CallSiteValue, FunctionValue, GlobalValue, IntValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    ir::{
        AggregateType, Global, HandlerIdx, Instruction, ProcIdx, Procedure, ReturnType, Type,
        TypeIdx, IR,
    },
    vecmap::VecMap,
};

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    target_data: TargetData,

    structs: VecMap<TypeIdx, Option<StructType<'ctx>>>,

    procs: VecMap<ProcIdx, FunctionValue<'ctx>>,
    globals: VecMap<Global, Option<GlobalValue<'ctx>>>,

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
        globals: VecMap::new(),
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

    for glob in ir.globals.values() {
        let typ = codegen.get_type(glob);
        match BasicTypeEnum::try_from(typ) {
            Ok(typ) => {
                let global = codegen.module.add_global(typ, None, "");
                global.set_linkage(Linkage::Internal);
                global.set_constant(false);
                match typ {
                    BasicTypeEnum::ArrayType(t) => global.set_initializer(&t.get_poison()),
                    BasicTypeEnum::FloatType(t) => global.set_initializer(&t.get_poison()),
                    BasicTypeEnum::IntType(t) => global.set_initializer(&t.get_poison()),
                    BasicTypeEnum::PointerType(t) => global.set_initializer(&t.get_poison()),
                    BasicTypeEnum::StructType(t) => global.set_initializer(&t.get_poison()),
                    BasicTypeEnum::VectorType(t) => global.set_initializer(&t.get_poison()),
                }
                codegen.globals.push_value(Some(global))
            }
            Err(_) => codegen.globals.push_value(None),
        }
    }

    for ((proc, recursive), function) in ir
        .procs
        .values()
        .zip(ir.recursive.values().copied())
        .zip(codegen.procs.values().copied())
    {
        codegen.generate_proc(ir, proc, recursive, function);
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
    fn size(&self, t: BasicTypeEnum) -> u64 {
        self.target_data.get_store_size(&t)
    }
    fn return_type(&self, t: &ReturnType) -> AnyTypeEnum<'ctx> {
        if t.break_union.is_empty() {
            self.get_type(&t.output)
        } else {
            let frame_type = self.frame_type();

            let max_type = std::iter::once(&t.output)
                .chain(t.break_union.iter())
                .filter_map(|t| BasicTypeEnum::try_from(self.get_type(t)).ok())
                .max_by_key(|&t| self.size(t));

            if let Some(basic) = max_type {
                self.context
                    .struct_type(&[frame_type.into(), basic], false)
                    .into()
            } else {
                self.context.struct_type(&[frame_type.into()], false).into()
            }
        }
    }
    fn generate_proc_sign(&self, ir: &IR, proc: &Procedure) -> FunctionValue<'ctx> {
        let in_types = proc
            .inputs
            .iter()
            .filter_map(|&r| BasicMetadataTypeEnum::try_from(self.get_type(&ir.regs[r])).ok())
            .collect::<Vec<_>>();

        let fn_type = match self.return_type(&proc.output) {
            AnyTypeEnum::ArrayType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::FloatType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::IntType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::PointerType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::StructType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::VectorType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::VoidType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::FunctionType(_) => unreachable!(),
        };

        self.module
            .add_function(&proc.debug_name, fn_type, Some(Linkage::Internal))
    }
    fn generate_proc(
        &self,
        ir: &IR,
        proc: &Procedure,
        recursive: bool,
        function: FunctionValue<'ctx>,
    ) {
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
            .filter(|&&r| !self.get_type(&ir.regs[r]).is_void_type())
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
                        let slice_type = self.get_type(&ir.regs[r]).into_struct_type();
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
                    I::Branch(r, yes, no) => {
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
                        let typ = BasicTypeEnum::try_from(self.get_type(&ir.regs[r])).ok();

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
                            blocks[idx] = self.handle_break(
                                function,
                                frame,
                                val,
                                Some(h),
                                !proc.output.break_union.is_empty(),
                            );
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
                            blocks[idx] = self.handle_break(
                                function,
                                frame,
                                val,
                                ir.procs[p].output.implicit_break,
                                !proc.output.break_union.is_empty(),
                            );
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
                        let frame = self.frame_type().const_int(usize::from(h) as u64, false);
                        let val = r.and_then(|r| valmap.get(&r)).copied();

                        let ret_type = function
                            .get_type()
                            .get_return_type()
                            .unwrap()
                            .into_struct_type();

                        let mut ret = ret_type.get_poison();
                        ret = self
                            .builder
                            .build_insert_value(ret, frame, 0, "")
                            .unwrap()
                            .into_struct_value();
                        if let Some(val) = val {
                            ret = self
                                .builder
                                .build_insert_value(ret, val, 1, "")
                                .unwrap()
                                .into_struct_value();
                        }
                        self.builder.build_return(Some(&ret)).unwrap();
                    }
                    I::Return(r) => {
                        let val = r.and_then(|r| valmap.get(&r)).copied();
                        if !proc.output.break_union.is_empty() {
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
                            if let Some(r) = val {
                                ret = self
                                    .builder
                                    .build_insert_value(ret, r, 1, "")
                                    .unwrap()
                                    .into_struct_value();
                            }
                            self.builder.build_return(Some(&ret)).unwrap();
                        } else {
                            self.builder
                                .build_return(val.as_ref().map(|val| -> &dyn BasicValue { val }))
                                .unwrap();
                        }
                        continue 'outer;
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
                        let aggr_ty = self.get_type(&ir.regs[r]);

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
                        let Type::Aggregate(t) = ir.regs[a] else { panic!() };
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
                    I::SetScopedGlobal(g, r, next) => {
                        if let Some(glob) = self.globals[g] {
                            let val = valmap[&r];

                            if recursive {
                                // save previous value if this is a recursive proc
                                // TODO: will require more tests once handler return types exist
                                let tmp = self
                                    .builder
                                    .build_load(val.get_type(), glob.as_pointer_value(), ".tmp")
                                    .unwrap();

                                self.builder.position_at_end(blocks[usize::from(next)]);
                                self.builder
                                    .build_store(glob.as_pointer_value(), tmp)
                                    .unwrap();

                                self.builder.position_at_end(basic_block);
                            }

                            self.builder
                                .build_store(glob.as_pointer_value(), val)
                                .unwrap();
                        }
                    }
                    I::GetGlobal(r, g) => {
                        if let Some(glob) = self.globals[g] {
                            let typ = BasicTypeEnum::try_from(self.get_type(&ir.regs[r])).unwrap();
                            let val = self
                                .builder
                                .build_load(typ, glob.as_pointer_value(), "")
                                .unwrap();
                            valmap.insert(r, val);
                        }
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
        val: Option<BasicValueEnum>,
        handler: Option<HandlerIdx>,
        bubble_break: bool,
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

        if bubble_break {
            let ret_type = function
                .get_type()
                .get_return_type()
                .unwrap()
                .into_struct_type();

            let mut ret = ret_type.get_poison();
            ret = self
                .builder
                .build_insert_value(ret, frame, 0, "")
                .unwrap()
                .into_struct_value();
            if ret_type.count_fields() > 1 {
                if let Some(val) = val {
                    ret = self
                        .builder
                        .build_insert_value(ret, val, 1, "")
                        .unwrap()
                        .into_struct_value();
                }
            }
            self.builder.build_return(Some(&ret)).unwrap();
        } else if let Some(val) = val {
            self.builder.build_return(Some(&val)).unwrap();
        } else {
            self.builder.build_return(None).unwrap();
        }

        self.builder.position_at_end(branch_next);
        branch_next
    }
    fn get_return(
        &self,
        proc: &Procedure,
        ret: CallSiteValue<'ctx>,
    ) -> (Option<IntValue<'ctx>>, Option<BasicValueEnum<'ctx>>) {
        if !proc.output.break_union.is_empty() {
            let ret = ret.try_as_basic_value().unwrap_left().into_struct_value();
            let frame = self.builder.build_extract_value(ret, 0, "").unwrap();
            if ret.get_type().count_fields() > 1 {
                let val = self.builder.build_extract_value(ret, 1, "").unwrap();
                (Some(frame.into_int_value()), Some(val))
            } else {
                (Some(frame.into_int_value()), None)
            }
        } else {
            (None, ret.try_as_basic_value().left())
        }
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
