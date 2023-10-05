use std::{collections::HashMap, path::Path};

use inkwell::{
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::{PassManager, PassManagerBuilder},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetMachine,
    },
    types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicTypeEnum, IntType, StructType},
    values::{BasicValue, BasicValueEnum, CallSiteValue, FunctionValue, GlobalValue, IntValue},
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    ir::{AggregateType, Global, HandlerIdx, Instruction, ProcIdx, Procedure, Type, TypeIdx, IR},
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
    putstr: FunctionValue<'ctx>,
}

pub fn generate_ir(ir: &IR, path: &Path, debug: bool) {
    Target::initialize_x86(&InitializationConfig::default());

    let context = Context::create();
    let module = context.create_module("main");
    let target = Target::from_triple(&TargetMachine::get_default_triple()).unwrap();
    let target_machine = target
        .create_target_machine(
            &TargetMachine::get_default_triple(),
            &TargetMachine::get_host_cpu_name().to_string(),
            &TargetMachine::get_host_cpu_features().to_string(),
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

    let putstr = module.add_function(
        "putstr",
        context.void_type().fn_type(
            &[context
                .struct_type(
                    &[
                        context.i8_type().ptr_type(AddressSpace::default()).into(),
                        context.ptr_sized_int_type(&target_data, None).into(),
                    ],
                    false,
                )
                .into()],
            false,
        ),
        Some(Linkage::External),
    );
    putstr.set_call_conventions(0);

    let mut codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        target_data,
        structs: VecMap::new(),
        procs: VecMap::new(),
        globals: VecMap::new(),
        putint,
        putstr,
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

    for (proc, function) in ir.procs.values().zip(codegen.procs.values().copied()) {
        codegen.generate_proc(ir, proc, function);
    }

    // set main func
    codegen.procs[ir.main].set_linkage(Linkage::External);

    // assume valid
    if debug {
        codegen.module.print_to_stderr();
        println!();
    }

    codegen.module.verify().unwrap();

    // compile
    let pb = PassManagerBuilder::create();
    pb.set_inliner_with_threshold(1);
    pb.set_optimization_level(OptimizationLevel::Aggressive);

    let pm = PassManager::create(());
    pb.populate_module_pass_manager(&pm);
    pm.run_on(&codegen.module);

    if debug {
        println!("--- OPTIMIZED LLVM ---");
        codegen.module.print_to_stderr();
    }

    target_machine
        .write_to_file(&codegen.module, FileType::Object, path)
        .unwrap();
}

impl<'ctx> CodeGen<'ctx> {
    fn generate_struct(&self, typ: &AggregateType) -> Option<StructType<'ctx>> {
        // TODO: set struct name
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
    fn align(&self, t: BasicTypeEnum) -> u32 {
        self.target_data.get_abi_alignment(&t)
    }
    fn name(&self, t: BasicTypeEnum<'ctx>) -> String {
        match t {
            BasicTypeEnum::ArrayType(t) => {
                format!("{}[{}]", self.name(t.get_element_type()), t.len())
            }
            BasicTypeEnum::FloatType(t) => format!("f{}", self.target_data.get_bit_size(&t)),
            BasicTypeEnum::IntType(t) => format!("i{}", self.target_data.get_bit_size(&t)),
            BasicTypeEnum::PointerType(_) => format!("ptr"),
            BasicTypeEnum::StructType(t) => t
                .get_name()
                .map(|c| c.to_string_lossy().into_owned())
                .unwrap_or_else(|| "struct".into()),
            BasicTypeEnum::VectorType(t) => {
                format!("{}x{}", self.name(t.get_element_type()), t.get_size())
            }
        }
    }
    fn return_type(&self, proc: &Procedure) -> AnyTypeEnum<'ctx> {
        let out = self.get_type(&proc.output.output);
        let out_name = BasicTypeEnum::try_from(out)
            .ok()
            .map(|t| self.name(t))
            .unwrap_or_else(|| "void".into());

        if proc.output.break_union.is_empty() {
            out
        } else {
            let frame_type = self.frame_type();

            let max_align = std::iter::once(&proc.output.output)
                .chain((&proc.output).break_union.iter().map(|(_, t)| t))
                .filter_map(|t| BasicTypeEnum::try_from(self.get_type(t)).ok())
                .max_by_key(|&t| self.align(t));
            let max_size = std::iter::once(&proc.output.output)
                .chain((&proc.output).break_union.iter().map(|(_, t)| t))
                .filter_map(|t| BasicTypeEnum::try_from(self.get_type(t)).ok())
                .max_by_key(|&t| self.size(t));

            if let Some(mut basic) = max_align {
                // add padding if required
                let size = self.size(basic);
                let padding = max_size.map(|t| self.size(t) - size).unwrap_or(0);
                if padding > 0 {
                    basic = self
                        .context
                        .struct_type(
                            &[
                                basic,
                                self.context.i8_type().array_type(padding as u32).into(),
                            ],
                            false,
                        )
                        .into();
                }

                // create union with most aligned member
                let typ = self
                    .context
                    .opaque_struct_type(&format!("tagged_{}", out_name));
                typ.set_body(&[frame_type.into(), basic], false);
                typ.into()
            } else {
                let typ = self.context.opaque_struct_type(&format!("tagged_void"));
                typ.set_body(&[frame_type.into()], false);
                typ.into()
            }
        }
    }
    fn generate_proc_sign(&self, ir: &IR, proc: &Procedure) -> FunctionValue<'ctx> {
        let in_types = proc
            .inputs
            .iter()
            .filter_map(|&r| BasicMetadataTypeEnum::try_from(self.get_type(&ir.regs[r])).ok())
            .collect::<Vec<_>>();

        let fn_type = match self.return_type(&proc) {
            AnyTypeEnum::ArrayType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::FloatType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::IntType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::PointerType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::StructType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::VectorType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::VoidType(t) => t.fn_type(&in_types, false),
            AnyTypeEnum::FunctionType(_) => unreachable!(),
        };

        // TODO: add parameter names names to fun
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
                            .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                            .unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Div(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_signed_div(lhs, rhs, "div").unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Mul(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_mul(lhs, rhs, "mul").unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Add(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_add(lhs, rhs, "add").unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Sub(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self.builder.build_int_sub(lhs, rhs, "sub").unwrap();
                        valmap.insert(r, res.into());
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
                                proc.handles
                                    .iter()
                                    .copied()
                                    .chain(ir.procs[p].output.implicit_break.into_iter()),
                                !proc.output.break_union.is_empty(),
                            );
                        }

                        if let Some(r) = r {
                            let typ = self.get_type(&ir.regs[r]);
                            if let Ok(typ) = BasicTypeEnum::try_from(typ) {
                                let val = val.expect(&format!(
                                    "call {} returns no value",
                                    ir.procs[p].debug_name
                                ));
                                let cast = self.build_union_cast(val, typ);
                                valmap.insert(r, cast);
                            }
                        }
                    }
                    I::Yeet(r, h) => {
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
                            .build_insert_value(ret, frame, 0, "bubble")
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
                        continue 'outer;
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
                                    "bubble",
                                )
                                .unwrap()
                                .into_struct_value();
                            if let (Some(val), Some(field)) =
                                (val, ret_typ.get_field_type_at_index(1))
                            {
                                let cast = self.build_union_cast(val, field);
                                ret = self
                                    .builder
                                    .build_insert_value(ret, cast, 1, "")
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
                    I::PrintStr(r) => {
                        self.builder
                            .build_call(self.putstr, &[valmap[&r].into()], "")
                            .unwrap();
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
                                .build_extract_value(aggr, n as u32, "member")
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

                            let tmp = self
                                .builder
                                .build_load(val.get_type(), glob.as_pointer_value(), "tmp")
                                .unwrap();

                            self.builder.position_at_end(blocks[usize::from(next)]);
                            self.builder
                                .build_store(glob.as_pointer_value(), tmp)
                                .unwrap();

                            self.builder.position_at_end(basic_block);

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
        frame: IntValue<'ctx>,
        val: Option<BasicValueEnum<'ctx>>,
        handlers: impl Iterator<Item = HandlerIdx>,
        bubble_break: bool,
    ) -> BasicBlock<'ctx> {
        let mut next = self.builder.get_insert_block().unwrap();

        // return handled breaks
        let mut cmp_handled = self.context.bool_type().const_int(0, false);
        for handler in handlers {
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
            cmp_handled = self.builder.build_or(cmp_handled, cmp_handler, "").unwrap();
        }
        if !cmp_handled.is_constant_int() {
            let branch_next = self.context.append_basic_block(function, "");
            let branch_return = self.context.append_basic_block(function, "handled");
            self.builder
                .build_conditional_branch(cmp_handled, branch_return, branch_next)
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
                    .build_insert_value(ret, self.frame_type().const_int(0, false), 0, "")
                    .unwrap()
                    .into_struct_value();
                if let (Some(val), Some(field)) = (val, ret.get_type().get_field_type_at_index(1)) {
                    let cast = self.build_union_cast(val, field);
                    ret = self
                        .builder
                        .build_insert_value(ret, cast, 1, "")
                        .unwrap()
                        .into_struct_value();
                }
                self.builder.build_return(Some(&ret)).unwrap();
            } else if let (Some(val), Some(typ)) = (val, function.get_type().get_return_type()) {
                let cast = self.build_union_cast(val, typ);
                self.builder.build_return(Some(&cast)).unwrap();
            } else {
                self.builder.build_return(None).unwrap();
            }

            self.builder.position_at_end(branch_next);
            next = branch_next;
        }

        // bubble up unhandled breaks
        if bubble_break {
            let cmp_zero = self
                .builder
                .build_int_compare(
                    IntPredicate::EQ,
                    frame,
                    self.frame_type().const_int(0, false),
                    "",
                )
                .unwrap();

            let branch_next = self.context.append_basic_block(function, "");
            let branch_return = self.context.append_basic_block(function, "unhandled");
            self.builder
                .build_conditional_branch(cmp_zero, branch_next, branch_return)
                .unwrap();

            self.builder.position_at_end(branch_return);
            let ret_type = function
                .get_type()
                .get_return_type()
                .unwrap()
                .into_struct_type();

            let mut ret = ret_type.get_poison();
            ret = self
                .builder
                .build_insert_value(ret, frame, 0, "bubble")
                .unwrap()
                .into_struct_value();
            if let (Some(val), Some(field)) = (val, ret.get_type().get_field_type_at_index(1)) {
                let cast = self.build_union_cast(val, field);
                ret = self
                    .builder
                    .build_insert_value(ret, cast, 1, "")
                    .unwrap()
                    .into_struct_value();
            }
            self.builder.build_return(Some(&ret)).unwrap();

            self.builder.position_at_end(branch_next);
            next = branch_next;
        }

        next
    }
    fn build_union_cast(
        &self,
        val: BasicValueEnum<'ctx>,
        typ: BasicTypeEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        if val.get_type() == typ {
            val
        } else {
            if self.size(typ) <= self.size(val.get_type()) {
                // type is smaller than value
                let ptr = self.builder.build_alloca(val.get_type(), "").unwrap();
                self.builder.build_store(ptr, val).unwrap();

                let reptr = match typ {
                    BasicTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::IntType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::StructType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::default()),
                };
                let bitcast = self.builder.build_pointer_cast(ptr, reptr, "").unwrap();

                println!("{:?} {:?}", bitcast, ptr);
                self.builder.build_load(typ, bitcast, "").unwrap()
            } else {
                // type is bigger than value
                let ptr = self.builder.build_alloca(typ, "").unwrap();

                let reptr = match val.get_type() {
                    BasicTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::IntType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::StructType(t) => t.ptr_type(AddressSpace::default()),
                    BasicTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::default()),
                };
                let bitcast = self.builder.build_pointer_cast(ptr, reptr, "").unwrap();

                println!("{:?} {:?}", bitcast, ptr);
                self.builder.build_store(bitcast, val).unwrap();
                self.builder.build_load(typ, ptr, "").unwrap()
            }
        }
    }
    fn get_return(
        &self,
        proc: &Procedure,
        ret: CallSiteValue<'ctx>,
    ) -> (Option<IntValue<'ctx>>, Option<BasicValueEnum<'ctx>>) {
        if !proc.output.break_union.is_empty() {
            let ret = ret.try_as_basic_value().unwrap_left().into_struct_value();
            let frame = self.builder.build_extract_value(ret, 0, "tag").unwrap();
            if ret.get_type().count_fields() > 1 {
                let val = self.builder.build_extract_value(ret, 1, "val").unwrap();
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
