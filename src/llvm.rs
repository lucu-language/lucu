use std::{collections::HashMap, path::Path};

use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::{PassManager, PassManagerBuilder},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetMachine,
    },
    types::{
        AnyTypeEnum, BasicMetadataTypeEnum, BasicTypeEnum, FunctionType, IntType, StringRadix,
        StructType,
    },
    values::{
        BasicValue, BasicValueEnum, CallSiteValue, FunctionValue, GlobalValue, IntValue,
        PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    ir::{
        AggrIdx, AggregateType, Global, HandlerIdx, Instruction, ProcIdx, ProcImpl, ProcSign, Type,
        TypeIdx, Value, IR,
    },
    vecmap::VecMap,
};

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    target_data: TargetData,

    structs: VecMap<AggrIdx, Option<StructType<'ctx>>>,

    procs: VecMap<ProcIdx, FunctionValue<'ctx>>,
    globals: VecMap<Global, Option<GlobalValue<'ctx>>>,

    syscall2_fn: FunctionType<'ctx>,
    syscall4_fn: FunctionType<'ctx>,
    syscall2: PointerValue<'ctx>,
    syscall4: PointerValue<'ctx>,
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

    let syscall2_fn = context.i64_type().fn_type(
        &[context.i64_type().into(), context.i64_type().into()],
        false,
    );
    let syscall4_fn = context.i64_type().fn_type(
        &[
            context.i64_type().into(),
            context.i64_type().into(),
            context.i64_type().into(),
            context.i64_type().into(),
        ],
        false,
    );
    let syscall2 = context.create_inline_asm(
        syscall2_fn,
        "syscall".to_string(),
        "=r,{rax},{rdi}".into(),
        true,
        false,
        None,
        false,
    );
    let syscall4 = context.create_inline_asm(
        syscall4_fn,
        "syscall".to_string(),
        "=r,{rax},{rdi},{rsi},{rdx}".into(),
        true,
        false,
        None,
        false,
    );

    let mut codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        target_data,
        structs: VecMap::new(),
        procs: VecMap::new(),
        globals: VecMap::new(),

        syscall2_fn,
        syscall4_fn,
        syscall2,
        syscall4,
    };

    for typ in ir.aggregates.values() {
        let struc = codegen.generate_struct(ir, typ);
        codegen.structs.push_value(struc);
    }

    for proc in ir.proc_sign.values() {
        let func = codegen.generate_proc_sign(ir, proc);
        codegen.procs.push_value(func);
    }

    for glob in ir.globals.values().copied() {
        let typ = codegen.get_type(ir, glob);
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

    for ((sign, imp), function) in ir
        .proc_sign
        .values()
        .zip(ir.proc_impl.values())
        .zip(codegen.procs.values().copied())
    {
        codegen.generate_proc(ir, sign, imp, function);
    }

    // set main func
    let start = codegen.module.add_function(
        "_start",
        codegen.context.void_type().fn_type(&[], false),
        Some(Linkage::External),
    );
    start.add_attribute(
        AttributeLoc::Function,
        context.create_enum_attribute(Attribute::get_named_enum_kind_id("sspstrong"), 0),
    );
    start.add_attribute(
        AttributeLoc::Function,
        context.create_enum_attribute(Attribute::get_named_enum_kind_id("noreturn"), 0),
    );
    start.add_attribute(
        AttributeLoc::Function,
        context.create_string_attribute("stackrealign", ""),
    );

    let block = codegen.context.append_basic_block(start, "");
    codegen.builder.position_at_end(block);
    codegen
        .builder
        .build_call(codegen.procs[ir.main], &[], "")
        .unwrap();
    codegen
        .builder
        .build_indirect_call(
            codegen.syscall2_fn,
            codegen.syscall2,
            &[
                codegen.context.i64_type().const_int(60, true).into(),
                codegen.context.i64_type().const_int(0, true).into(),
            ],
            "",
        )
        .unwrap();
    codegen.builder.build_unreachable().unwrap();

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
    fn generate_struct(&self, ir: &IR, typ: &AggregateType) -> Option<StructType<'ctx>> {
        // TODO: set struct name
        let fields: Vec<BasicTypeEnum> = typ
            .children
            .iter()
            .copied()
            .filter_map(|typ| BasicTypeEnum::try_from(self.get_type(ir, typ)).ok())
            .collect();

        if fields.is_empty() {
            None
        } else {
            let struc = self.context.opaque_struct_type(&typ.debug_name);
            struc.set_body(&fields, false);
            Some(struc)
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
    fn return_type(&self, ir: &IR, proc: &ProcSign) -> AnyTypeEnum<'ctx> {
        let out = self.get_type(ir, proc.output);
        let out_name = BasicTypeEnum::try_from(out)
            .ok()
            .map(|t| self.name(t))
            .unwrap_or_else(|| "void".into());

        if proc.unhandled.is_empty() {
            out
        } else {
            let frame_type = self.frame_type();

            let max_align = std::iter::once(&proc.output)
                .chain(
                    proc.unhandled
                        .iter()
                        .copied()
                        .map(|h| &ir.handler_type[h].break_ty),
                )
                .copied()
                .filter_map(|t| BasicTypeEnum::try_from(self.get_type(ir, t)).ok())
                .max_by_key(|&t| self.align(t));
            let max_size = std::iter::once(&proc.output)
                .chain(
                    proc.unhandled
                        .iter()
                        .copied()
                        .map(|h| &ir.handler_type[h].break_ty),
                )
                .copied()
                .filter_map(|t| BasicTypeEnum::try_from(self.get_type(ir, t)).ok())
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
    fn generate_proc_sign(&self, ir: &IR, proc: &ProcSign) -> FunctionValue<'ctx> {
        let in_types = proc
            .inputs
            .iter()
            .filter_map(|&r| BasicMetadataTypeEnum::try_from(self.get_type(ir, ir.regs[r])).ok())
            .collect::<Vec<_>>();

        let fn_type = match self.return_type(ir, &proc) {
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
    fn generate_proc(
        &self,
        ir: &IR,
        proc: &ProcSign,
        imp: &ProcImpl,
        function: FunctionValue<'ctx>,
    ) {
        let mut blocks: Vec<_> = (0..imp.blocks.len())
            .map(|idx| {
                self.context
                    .append_basic_block(function, &format!("L{}", idx))
            })
            .collect();

        let mut valmap = HashMap::new();
        for (n, &reg) in proc
            .inputs
            .iter()
            .filter(|&&r| !self.get_type(ir, ir.regs[r]).is_void_type())
            .enumerate()
        {
            valmap.insert(reg, function.get_nth_param(n as u32).unwrap());
        }

        if let Some(captures) = &proc.captures {
            self.builder.position_at_end(blocks[0]);

            let struc = match captures.input {
                Value::Value(r, _) => valmap.get(&r).map(|b| b.into_struct_value()),
                Value::ValueIndex(_, _, _) => todo!(),
                Value::Reference(ptr) => valmap.get(&ptr).map(|val| {
                    let ty =
                        BasicTypeEnum::try_from(self.get_type(ir, captures.input.get_type(ir)))
                            .unwrap();
                    self.builder
                        .build_load(ty, val.into_pointer_value(), "")
                        .unwrap()
                        .into_struct_value()
                }),
                Value::Global(glob) => self.globals[glob].map(|val| {
                    let ty = BasicTypeEnum::try_from(self.get_type(ir, ir.globals[glob])).unwrap();
                    self.builder
                        .build_load(ty, val.as_pointer_value(), "")
                        .unwrap()
                        .into_struct_value()
                }),
            };

            if let Some(struc) = struc {
                let mut member = 0;
                for reg in captures.members.iter().copied() {
                    let mem_ty = self.get_type(ir, ir.regs[reg]);
                    if BasicTypeEnum::try_from(mem_ty).is_ok() {
                        let val = self.builder.build_extract_value(struc, member, "").unwrap();
                        valmap.insert(reg, val.into());
                        member += 1;
                    }
                }
            }
        }

        'outer: for (idx, block) in imp.blocks.values().enumerate() {
            let basic_block = blocks[idx];
            self.builder.position_at_end(basic_block);

            for instr in block.instructions.iter() {
                use Instruction as I;
                match *instr {
                    I::Init(r, v) => {
                        valmap.insert(r, self.context.i64_type().const_int(v, false).into());
                    }
                    I::InitString(r, ref v) => {
                        let slice_type = self.get_type(ir, ir.regs[r]).into_struct_type();
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
                        let typ = BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).ok();

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
                    I::Greater(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::UGT, lhs, rhs, "gt")
                            .unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Less(r, a, b) => {
                        let lhs = valmap[&a].into_int_value();
                        let rhs = valmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::ULT, lhs, rhs, "lt")
                            .unwrap();
                        valmap.insert(r, res.into());
                    }
                    I::Call(p, r, ref rs) => {
                        let func = self.procs[p];
                        let args: Vec<_> = rs
                            .iter()
                            .filter_map(|r| valmap.get(r).map(|&v| v.into()))
                            .collect();

                        let ret = self.builder.build_call(func, &args, "").unwrap();
                        let (frame, val) = self.get_return(&ir.proc_sign[p], ret);

                        if let Some(frame) = frame {
                            let unhandled = &ir.proc_sign[p].unhandled;
                            let handlers = proc
                                .handled
                                .iter()
                                .copied()
                                .filter(|h| unhandled.contains(h));
                            let redirect = proc
                                .redirect
                                .iter()
                                .copied()
                                .filter(|(h, _)| unhandled.contains(h));
                            blocks[idx] = self.handle_break(
                                function,
                                frame,
                                val,
                                handlers,
                                redirect,
                                !proc.unhandled.is_empty(),
                            );
                        }

                        if let Some(r) = r {
                            let typ = self.get_type(ir, ir.regs[r]);
                            if let Ok(typ) = BasicTypeEnum::try_from(typ) {
                                let val = val.expect(&format!(
                                    "call {} returns no value",
                                    ir.proc_sign[p].debug_name
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
                        if !proc.unhandled.is_empty() {
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
                        // setup
                        let val = valmap[&r];
                        let bufty = self.context.i8_type().array_type(21);
                        let buf = self.builder.build_alloca(bufty, "buf").unwrap();
                        let buf_last = unsafe {
                            self.builder
                                .build_gep(
                                    bufty,
                                    buf,
                                    &[
                                        self.context.i64_type().const_int(0, false),
                                        self.context.i64_type().const_int(20, false),
                                    ],
                                    "last",
                                )
                                .unwrap()
                        };
                        self.builder
                            .build_store(
                                buf_last,
                                self.context.i8_type().const_int('\n'.into(), false),
                            )
                            .unwrap();

                        // loop
                        let block_loop = self.context.append_basic_block(function, "loop");
                        self.builder.build_unconditional_branch(block_loop).unwrap();
                        self.builder.position_at_end(block_loop);

                        let number = self
                            .builder
                            .build_phi(self.context.i64_type(), "d")
                            .unwrap();
                        let last = self
                            .builder
                            .build_phi(
                                self.context.i8_type().ptr_type(AddressSpace::default()),
                                "prev",
                            )
                            .unwrap();

                        let rem = self
                            .builder
                            .build_int_unsigned_rem(
                                number.as_basic_value().into_int_value(),
                                self.context.i64_type().const_int(10, false),
                                "rem",
                            )
                            .unwrap();
                        let rem = self
                            .builder
                            .build_int_truncate(rem, self.context.i8_type(), "rem")
                            .unwrap();
                        let digit = self
                            .builder
                            .build_or(
                                rem,
                                self.context.i8_type().const_int('0'.into(), false),
                                "digit",
                            )
                            .unwrap();

                        let cur = unsafe {
                            self.builder
                                .build_gep(
                                    self.context.i8_type(),
                                    last.as_basic_value().into_pointer_value(),
                                    &[self
                                        .context
                                        .i64_type()
                                        .const_int_from_string("-1", StringRadix::Decimal)
                                        .unwrap()],
                                    "cur",
                                )
                                .unwrap()
                        };
                        self.builder.build_store(cur, digit).unwrap();

                        let div = self
                            .builder
                            .build_int_unsigned_div(
                                number.as_basic_value().into_int_value(),
                                self.context.i64_type().const_int(10, false),
                                "div",
                            )
                            .unwrap();

                        number.add_incoming(&[(&val, blocks[idx]), (&div, block_loop)]);
                        last.add_incoming(&[(&buf_last, blocks[idx]), (&cur, block_loop)]);

                        // write
                        let block_write = self.context.append_basic_block(function, "write");
                        let cmp = self
                            .builder
                            .build_int_compare(
                                IntPredicate::ULT,
                                number.as_basic_value().into_int_value(),
                                self.context.i64_type().const_int(10, false),
                                "cmp",
                            )
                            .unwrap();
                        self.builder
                            .build_conditional_branch(cmp, block_write, block_loop)
                            .unwrap();
                        self.builder.position_at_end(block_write);

                        let buf_end = unsafe {
                            self.builder
                                .build_gep(
                                    bufty,
                                    buf,
                                    &[
                                        self.context.i64_type().const_int(0, false),
                                        self.context.i64_type().const_int(21, false),
                                    ],
                                    "ptr",
                                )
                                .unwrap()
                        };
                        let buf_end = self
                            .builder
                            .build_ptr_to_int(buf_end, self.context.i64_type(), "end")
                            .unwrap();
                        let buf_start = self
                            .builder
                            .build_ptr_to_int(cur, self.context.i64_type(), "start")
                            .unwrap();
                        let buf_len = self
                            .builder
                            .build_int_sub(buf_end, buf_start, "len")
                            .unwrap();

                        self.builder
                            .build_indirect_call(
                                self.syscall4_fn,
                                self.syscall4,
                                &[
                                    self.context.i64_type().const_int(1, false).into(),
                                    self.context.i64_type().const_int(1, false).into(),
                                    buf_start.into(),
                                    buf_len.into(),
                                ],
                                "",
                            )
                            .unwrap();

                        blocks[idx] = block_write;
                    }
                    I::PrintStr(r) => {
                        let val = valmap[&r].into_struct_value();
                        let ptr = self
                            .builder
                            .build_extract_value(val, 0, "ptr")
                            .unwrap()
                            .into_pointer_value();
                        let buf = self
                            .builder
                            .build_ptr_to_int(ptr, self.context.i64_type(), "buf")
                            .unwrap();
                        let len = self.builder.build_extract_value(val, 1, "len").unwrap();
                        self.builder
                            .build_indirect_call(
                                self.syscall4_fn,
                                self.syscall4,
                                &[
                                    self.context.i64_type().const_int(1, false).into(),
                                    self.context.i64_type().const_int(1, false).into(),
                                    buf.into(),
                                    len.into(),
                                ],
                                "",
                            )
                            .unwrap();
                    }
                    I::Aggregate(r, ref rs) | I::Handler(r, ref rs) => {
                        let aggr_ty = self.get_type(ir, ir.regs[r]);

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
                        let t = match ir.types[ir.regs[a]] {
                            Type::Aggregate(t) => t,
                            _ => panic!(),
                        };
                        let n = ir.aggregates[t]
                            .children
                            .iter()
                            .copied()
                            .enumerate()
                            .filter_map(|(i, t)| {
                                if self.get_type(ir, t).is_void_type() {
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

                            self.builder.position_at_end(blocks[idx]);
                            self.builder
                                .build_store(glob.as_pointer_value(), val)
                                .unwrap();
                        }
                    }
                    I::GetGlobal(r, g) => {
                        if let Some(glob) = self.globals[g] {
                            let typ =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).unwrap();
                            let val = self
                                .builder
                                .build_load(typ, glob.as_pointer_value(), "")
                                .unwrap();
                            valmap.insert(r, val);
                        }
                    }
                    I::GetGlobalPtr(r, g) => {
                        if let Some(glob) = self.globals[g] {
                            valmap.insert(r, glob.as_pointer_value().into());
                        }
                    }
                    I::Reference(ptrr, r) => {
                        if let Some(val) = valmap.get(&r).copied() {
                            let ptr = self.builder.build_alloca(val.get_type(), "").unwrap();
                            self.builder.build_store(ptr, val).unwrap();
                            valmap.insert(ptrr, ptr.into());
                        }
                    }
                    I::Load(r, ptrr) => {
                        if let Some(val) = valmap.get(&ptrr).copied() {
                            let ty =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).unwrap();
                            let v = self
                                .builder
                                .build_load(ty, val.into_pointer_value(), "")
                                .unwrap();
                            valmap.insert(r, v);
                        }
                    }
                    I::Store(ptrr, r) => {
                        if let Some(val) = valmap.get(&r).copied() {
                            let ptr = valmap[&ptrr];
                            self.builder
                                .build_store(ptr.into_pointer_value(), val)
                                .unwrap();
                        }
                    }
                    I::RawHandler(r, h) => {
                        if let Some(&v) = valmap.get(&h) {
                            let unraw = v.into_struct_value();
                            let mems = match ir.types[ir.regs[r]] {
                                Type::RawHandler(_, ref mems) => mems,
                                _ => unreachable!(),
                            };

                            let struc_ty = self.get_type(ir, ir.regs[r]).into_struct_type();
                            let mut struc = struc_ty.get_poison();

                            for (mem, ty) in struc_ty.get_field_types().iter().copied().enumerate()
                            {
                                let mut val = self
                                    .builder
                                    .build_extract_value(unraw, mem as u32, "")
                                    .unwrap();
                                if mems.contains(&mem) {
                                    val = self
                                        .builder
                                        .build_load(ty, val.into_pointer_value(), "")
                                        .unwrap();
                                }
                                struc = self
                                    .builder
                                    .build_insert_value(struc, val, mem as u32, "")
                                    .unwrap()
                                    .into_struct_value();
                            }

                            valmap.insert(r, struc.into());
                        }
                    }
                    I::UnrawHandler(r, h) => {
                        if let Some(&v) = valmap.get(&h) {
                            let raw = v.into_struct_value();
                            let mems = match ir.types[ir.regs[h]] {
                                Type::RawHandler(_, ref mems) => mems,
                                _ => unreachable!(),
                            };

                            let struc_ty = self.get_type(ir, ir.regs[r]).into_struct_type();
                            let mut struc = struc_ty.get_poison();

                            for mem in 0..struc_ty.count_fields() {
                                let mut val =
                                    self.builder.build_extract_value(raw, mem, "").unwrap();
                                if mems.contains(&(mem as usize)) {
                                    let ptr =
                                        self.builder.build_alloca(val.get_type(), "").unwrap();
                                    self.builder.build_store(ptr, val).unwrap();
                                    val = ptr.into();
                                }
                                struc = self
                                    .builder
                                    .build_insert_value(struc, val, mem, "")
                                    .unwrap()
                                    .into_struct_value();
                            }

                            valmap.insert(r, struc.into());
                        }
                    }
                    I::Copy(r, h) => {
                        if let Some(&v) = valmap.get(&h) {
                            valmap.insert(r, v);
                        }
                    }
                    I::Uninit(r) => {
                        if let Ok(ty) = BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])) {
                            valmap.insert(
                                r,
                                match ty {
                                    BasicTypeEnum::ArrayType(t) => t.get_undef().into(),
                                    BasicTypeEnum::FloatType(t) => t.get_undef().into(),
                                    BasicTypeEnum::IntType(t) => t.get_undef().into(),
                                    BasicTypeEnum::PointerType(t) => t.get_undef().into(),
                                    BasicTypeEnum::StructType(t) => t.get_undef().into(),
                                    BasicTypeEnum::VectorType(t) => t.get_undef().into(),
                                },
                            );
                        }
                    }
                    I::Element(r, a, m) => {
                        if let Some(&a) = valmap.get(&a) {
                            let array_ty = a.get_type().into_array_type();
                            let ptr = self.builder.build_alloca(array_ty, "").unwrap();
                            self.builder.build_store(ptr, a).unwrap();

                            let mem = valmap[&m].into_int_value();
                            let elem_ty = array_ty.get_element_type();
                            let elem_ptr = unsafe {
                                self.builder
                                    .build_in_bounds_gep(
                                        array_ty,
                                        ptr,
                                        &[self.context.i64_type().const_int(0, false), mem],
                                        "",
                                    )
                                    .unwrap()
                            };

                            let elem = self.builder.build_load(elem_ty, elem_ptr, "").unwrap();
                            valmap.insert(r, elem);
                        }
                    }
                    I::ElementPtr(r, a, m) => {
                        if let Some(&ptr) = valmap.get(&a) {
                            let array_ty =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[a].inner(ir)))
                                    .unwrap();
                            let ptr = ptr.into_pointer_value();

                            let mem = valmap[&m].into_int_value();
                            let elem_ptr = unsafe {
                                self.builder
                                    .build_in_bounds_gep(
                                        array_ty,
                                        ptr,
                                        &[self.context.i64_type().const_int(0, false), mem],
                                        "",
                                    )
                                    .unwrap()
                            };

                            valmap.insert(r, elem_ptr.into());
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
        redirect: impl Iterator<Item = (HandlerIdx, HandlerIdx)>,
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

        // redirect
        for (clone, original) in redirect {
            let cmp_clone = self
                .builder
                .build_int_compare(
                    IntPredicate::EQ,
                    frame,
                    self.frame_type()
                        .const_int(usize::from(clone) as u64, false),
                    "",
                )
                .unwrap();

            let branch_next = self.context.append_basic_block(function, "");
            let branch_return = self.context.append_basic_block(function, "redirect");
            self.builder
                .build_conditional_branch(cmp_clone, branch_return, branch_next)
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
                .build_insert_value(
                    ret,
                    self.frame_type()
                        .const_int(usize::from(original) as u64, false),
                    0,
                    "",
                )
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

                self.builder.build_store(bitcast, val).unwrap();
                self.builder.build_load(typ, ptr, "").unwrap()
            }
        }
    }
    fn get_return(
        &self,
        proc: &ProcSign,
        ret: CallSiteValue<'ctx>,
    ) -> (Option<IntValue<'ctx>>, Option<BasicValueEnum<'ctx>>) {
        if !proc.unhandled.is_empty() {
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
    fn get_type(&self, ir: &IR, ty: TypeIdx) -> AnyTypeEnum<'ctx> {
        match ir.types[ty] {
            Type::Int => self.context.i64_type().into(),
            Type::ArraySize => self
                .context
                .ptr_sized_int_type(&self.target_data, None)
                .into(),
            Type::Aggregate(idx) => match self.structs[idx] {
                Some(t) => t.into(),
                None => self.context.void_type().into(),
            },
            Type::Handler(h) | Type::NakedHandler(h) => {
                let ty = ir.handler_type[h]
                    .captures
                    .iter()
                    .copied()
                    .filter_map(|t| BasicTypeEnum::try_from(self.get_type(ir, t)).ok())
                    .collect::<Vec<_>>();
                if !ty.is_empty() {
                    self.context.struct_type(&ty, false).into()
                } else {
                    self.context.void_type().into()
                }
            }
            Type::RawHandler(h, ref mems) => {
                let ty = ir.handler_type[h]
                    .captures
                    .iter()
                    .copied()
                    .enumerate()
                    .filter_map(|(i, t)| {
                        let t = if mems.contains(&i) { t.inner(ir) } else { t };
                        BasicTypeEnum::try_from(self.get_type(ir, t)).ok()
                    })
                    .collect::<Vec<_>>();
                if !ty.is_empty() {
                    self.context.struct_type(&ty, false).into()
                } else {
                    self.context.void_type().into()
                }
            }
            Type::Never | Type::None => self.context.void_type().into(),
            Type::HandlerOutput => {
                unreachable!("HandlerOutput never filled in with concrete handler type")
            }
            Type::Byte => self.context.i8_type().into(),
            Type::Bool => self.context.bool_type().into(),
            Type::Pointer(ty) => match self.get_type(ir, ty) {
                AnyTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::default()).into(),
                AnyTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::default()).into(),
                AnyTypeEnum::FunctionType(t) => t.ptr_type(AddressSpace::default()).into(),
                AnyTypeEnum::IntType(t) => t.ptr_type(AddressSpace::default()).into(),
                AnyTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::default()).into(),
                AnyTypeEnum::StructType(t) => t.ptr_type(AddressSpace::default()).into(),
                AnyTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::default()).into(),
                AnyTypeEnum::VoidType(_) => self.context.void_type().into(),
            },
            Type::ConstArray(size, ty) => match self.get_type(ir, ty) {
                AnyTypeEnum::ArrayType(t) => t.array_type(size as u32).into(),
                AnyTypeEnum::FloatType(t) => t.array_type(size as u32).into(),
                AnyTypeEnum::FunctionType(_) => todo!(),
                AnyTypeEnum::IntType(t) => t.array_type(size as u32).into(),
                AnyTypeEnum::PointerType(t) => t.array_type(size as u32).into(),
                AnyTypeEnum::StructType(t) => t.array_type(size as u32).into(),
                AnyTypeEnum::VectorType(t) => t.array_type(size as u32).into(),
                AnyTypeEnum::VoidType(_) => self.context.void_type().into(),
            },
        }
    }
}
