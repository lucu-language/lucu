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
        BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallSiteValue, FunctionValue,
        GlobalValue, IntValue, PhiValue, PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    ir::{
        AggrIdx, AggregateType, Global, HandlerIdx, Instruction, ProcIdx, ProcImpl, ProcSign, Reg,
        Type, TypeIdx, Value, IR,
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

    syscalls: Vec<(FunctionType<'ctx>, PointerValue<'ctx>)>,
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

    let uintptr = context.ptr_sized_int_type(&target_data, None);

    // TODO: this is x86_64 only
    const SYS_RET: &'static str = "rax";
    const SYS_NR: &'static str = "rax";
    const SYS_ARGS: [&'static str; 6] = ["rdi", "rsi", "rdx", "r10", "r8", "r9"];
    const SYS_CLOBBER: [&'static str; 2] = ["rcx", "r11"];

    let syscalls = (0..=6)
        .map(|n| {
            let inputs = std::iter::repeat(BasicMetadataTypeEnum::from(uintptr))
                .take(n + 1)
                .collect::<Vec<_>>();
            let ty = uintptr.fn_type(&inputs, false);

            let constrains = format!(
                "={{{}}},{{{}}},{},{}",
                SYS_RET,
                SYS_NR,
                SYS_ARGS
                    .iter()
                    .take(n)
                    .map(|r| format!("{{{}}}", r))
                    .collect::<Vec<_>>()
                    .join(","),
                SYS_CLOBBER
                    .iter()
                    .map(|r| format!("~{{{}}}", r))
                    .collect::<Vec<_>>()
                    .join(",")
            );
            let asm = context.create_inline_asm(
                ty,
                "syscall".into(),
                constrains,
                true,
                false,
                None,
                false,
            );

            (ty, asm)
        })
        .collect();

    let mut codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        target_data,
        structs: VecMap::new(),
        procs: VecMap::new(),
        globals: VecMap::new(),
        syscalls,
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
            codegen.syscalls[1].0,
            codegen.syscalls[1].1,
            &[
                codegen.iptr_type().const_int(60, true).into(),
                codegen.iptr_type().const_int(0, true).into(),
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
        self.isize_type()
    }
    fn iptr_type(&self) -> IntType<'ctx> {
        self.context.ptr_sized_int_type(&self.target_data, None)
    }
    fn isize_type(&self) -> IntType<'ctx> {
        self.context.ptr_sized_int_type(&self.target_data, None)
    }
    fn int_type(&self) -> IntType<'ctx> {
        // TODO: other architectures
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

        let mut regmap = HashMap::new();
        for (n, &reg) in proc
            .inputs
            .iter()
            .filter(|&&r| !self.get_type(ir, ir.regs[r]).is_void_type())
            .enumerate()
        {
            regmap.insert(reg, function.get_nth_param(n as u32).unwrap());
        }

        if let Some(captures) = &proc.captures {
            self.builder.position_at_end(blocks[0]);

            let struc = match captures.input {
                Value::Value(r, _) => regmap.get(&r).map(|b| b.into_struct_value()),
                Value::Reference(ptr) => regmap.get(&ptr).map(|val| {
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
                        regmap.insert(reg, val.into());
                        member += 1;
                    }
                }
            }
        }

        let mut phimap = HashMap::<Reg, (PhiValue<'ctx>, BasicBlock<'ctx>)>::new();

        'outer: for (idx, block) in imp.blocks.values().enumerate() {
            let basic_block = blocks[idx];
            self.builder.position_at_end(basic_block);

            macro_rules! insert {
                ($reg:expr, $value:expr) => {
                    let reg = $reg;
                    let value = $value;
                    regmap.insert(reg, value);
                    if let Some((phi, block)) = phimap.remove(&reg) {
                        phi.add_incoming(&[(&value, block)]);
                    }
                };
            }

            for instr in block.instructions.iter() {
                use Instruction as I;
                match *instr {
                    I::Init(r, v) => {
                        let ty = self.get_type(ir, ir.regs[r]).into_int_type();
                        insert!(r, ty.const_int(v, false).into());
                    }
                    I::Copy(r, v) => {
                        if let Some(v) = regmap.get(&v).copied() {
                            insert!(r, v);
                        }
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

                        insert!(r, const_str_slice.into());
                    }
                    I::Branch(r, yes, no) => {
                        self.builder
                            .build_conditional_branch(
                                regmap[&r].into_int_value(),
                                blocks[usize::from(yes)],
                                blocks[usize::from(no)],
                            )
                            .unwrap();
                        continue 'outer;
                    }
                    I::Phi(r, ref v) => {
                        let typ = BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).ok();

                        if let Some(typ) = typ {
                            let phi = self.builder.build_phi(typ, "").unwrap();
                            for (r, b) in v.iter().copied() {
                                if let Some(v) = regmap.get(&r).copied() {
                                    phi.add_incoming(&[(&v, blocks[usize::from(b)])]);
                                } else {
                                    phimap.insert(r, (phi, blocks[usize::from(b)]));
                                }
                            }
                            insert!(r, phi.as_basic_value());
                        }
                    }
                    I::Equals(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                            .unwrap();
                        insert!(r, res.into());
                    }
                    I::Div(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_signed_div(lhs, rhs, "div").unwrap();
                        insert!(r, res.into());
                    }
                    I::Mul(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_mul(lhs, rhs, "mul").unwrap();
                        insert!(r, res.into());
                    }
                    I::Add(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_add(lhs, rhs, "add").unwrap();
                        insert!(r, res.into());
                    }
                    I::Sub(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_sub(lhs, rhs, "sub").unwrap();
                        insert!(r, res.into());
                    }
                    I::Greater(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::UGT, lhs, rhs, "gt")
                            .unwrap();
                        insert!(r, res.into());
                    }
                    I::Less(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::ULT, lhs, rhs, "lt")
                            .unwrap();
                        insert!(r, res.into());
                    }
                    I::Call(p, r, ref rs) => {
                        let func = self.procs[p];
                        let args: Vec<_> = rs
                            .iter()
                            .filter_map(|r| regmap.get(r).map(|&v| v.into()))
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
                                insert!(r, cast);
                            }
                        }
                    }
                    I::Yeet(r, h) => {
                        let frame = self.frame_type().const_int(usize::from(h) as u64, false);
                        let val = r.and_then(|r| regmap.get(&r)).copied();

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
                        let val = r.and_then(|r| regmap.get(&r)).copied();
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
                        let val = regmap[&r];
                        let bufty = self.context.i8_type().array_type(21);
                        let buf = self.builder.build_alloca(bufty, "buf").unwrap();
                        let buf_last = unsafe {
                            self.builder
                                .build_gep(
                                    bufty,
                                    buf,
                                    &[
                                        self.isize_type().const_int(0, false),
                                        self.isize_type().const_int(20, false),
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

                        let number = self.builder.build_phi(self.int_type(), "d").unwrap();
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
                                self.int_type().const_int(10, false),
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
                                        .isize_type()
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
                                self.int_type().const_int(10, false),
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
                                self.int_type().const_int(10, false),
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
                                        self.isize_type().const_int(0, false),
                                        self.isize_type().const_int(21, false),
                                    ],
                                    "ptr",
                                )
                                .unwrap()
                        };
                        let buf_end = self
                            .builder
                            .build_ptr_to_int(buf_end, self.iptr_type(), "end")
                            .unwrap();
                        let buf_start = self
                            .builder
                            .build_ptr_to_int(cur, self.iptr_type(), "start")
                            .unwrap();
                        let buf_len = self
                            .builder
                            .build_int_sub(buf_end, buf_start, "len")
                            .unwrap();

                        self.builder
                            .build_indirect_call(
                                self.syscalls[3].0,
                                self.syscalls[3].1,
                                &[
                                    self.iptr_type().const_int(1, false).into(),
                                    self.iptr_type().const_int(1, false).into(),
                                    buf_start.into(),
                                    buf_len.into(),
                                ],
                                "",
                            )
                            .unwrap();

                        blocks[idx] = block_write;
                    }
                    I::PrintStr(r) => {
                        let val = regmap[&r].into_struct_value();
                        let ptr = self
                            .builder
                            .build_extract_value(val, 0, "ptr")
                            .unwrap()
                            .into_pointer_value();
                        let buf = self
                            .builder
                            .build_ptr_to_int(ptr, self.iptr_type(), "buf")
                            .unwrap();
                        let len = self.builder.build_extract_value(val, 1, "len").unwrap();
                        self.builder
                            .build_indirect_call(
                                self.syscalls[3].0,
                                self.syscalls[3].1,
                                &[
                                    self.iptr_type().const_int(1, false).into(),
                                    self.iptr_type().const_int(1, false).into(),
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
                            for (n, &member) in rs.iter().filter_map(|r| regmap.get(r)).enumerate()
                            {
                                aggr = self
                                    .builder
                                    .build_insert_value(aggr, member, n as u32, "")
                                    .unwrap()
                                    .into_struct_value();
                            }

                            insert!(r, aggr.into());
                        }
                    }
                    I::Member(r, a, n) => {
                        // skip over empty children that are uncounted
                        match ir.types[ir.regs[a]] {
                            Type::Aggregate(t) => {
                                // get member
                                if BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).is_ok() {
                                    let mut mem = [n];
                                    self.get_actual_indices(
                                        ir,
                                        &ir.aggregates[t].children,
                                        &mut mem,
                                    );
                                    let n = mem[0];

                                    let aggr = regmap[&a].into_struct_value();

                                    let member = self
                                        .builder
                                        .build_extract_value(aggr, n as u32, "member")
                                        .unwrap();

                                    insert!(r, member);
                                }
                            }
                            Type::Slice(_) => {
                                // get slice data
                                let slice = self.get_type(ir, ir.regs[a]).into_struct_type();
                                match n {
                                    0 => {
                                        // ptr
                                        if slice.count_fields() > 1 {
                                            let aggr = regmap[&a].into_struct_value();
                                            let member = self
                                                .builder
                                                .build_extract_value(aggr, 0, "member")
                                                .unwrap();
                                            insert!(r, member);
                                        }
                                    }
                                    1 => {
                                        // len
                                        let idx = slice.count_fields() - 1;

                                        let aggr = regmap[&a].into_struct_value();
                                        let member = self
                                            .builder
                                            .build_extract_value(aggr, idx, "member")
                                            .unwrap();
                                        insert!(r, member);
                                    }
                                    _ => unreachable!(),
                                }
                            }
                            _ => panic!(),
                        }
                    }
                    I::Unreachable => {
                        self.builder.build_unreachable().unwrap();
                        continue 'outer;
                    }
                    I::SetScopedGlobal(g, r, next) => {
                        if let Some(glob) = self.globals[g] {
                            let val = regmap[&r];

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
                            insert!(r, val);
                        }
                    }
                    I::GetGlobalPtr(r, g) => {
                        if let Some(glob) = self.globals[g] {
                            insert!(r, glob.as_pointer_value().into());
                        }
                    }
                    I::Reference(ptrr, r) => {
                        if let Some(val) = regmap.get(&r).copied() {
                            let ptr = self.builder.build_alloca(val.get_type(), "").unwrap();
                            self.builder.build_store(ptr, val).unwrap();
                            insert!(ptrr, ptr.into());
                        }
                    }
                    I::Load(r, ptrr) => {
                        if let Some(val) = regmap.get(&ptrr).copied() {
                            let ty =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).unwrap();
                            let v = self
                                .builder
                                .build_load(ty, val.into_pointer_value(), "")
                                .unwrap();
                            insert!(r, v);
                        }
                    }
                    I::Store(ptrr, r) => {
                        if let Some(val) = regmap.get(&r).copied() {
                            let ptr = regmap[&ptrr];
                            self.builder
                                .build_store(ptr.into_pointer_value(), val)
                                .unwrap();
                        }
                    }
                    I::RawHandler(r, h) => {
                        if let Some(&v) = regmap.get(&h) {
                            let unraw = v.into_struct_value();
                            let mems = match ir.types[ir.regs[r]] {
                                Type::RawHandler(handler, ref mems) => {
                                    let mut idx = Vec::from(&**mems);
                                    self.get_actual_indices(
                                        ir,
                                        &ir.handler_type[handler].captures,
                                        &mut idx,
                                    );
                                    idx
                                }
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

                            insert!(r, struc.into());
                        }
                    }
                    I::UnrawHandler(r, h) => {
                        if let Some(&v) = regmap.get(&h) {
                            let raw = v.into_struct_value();
                            let mems = match ir.types[ir.regs[h]] {
                                Type::RawHandler(handler, ref mems) => {
                                    let mut idx = Vec::from(&**mems);
                                    self.get_actual_indices(
                                        ir,
                                        &ir.handler_type[handler].captures,
                                        &mut idx,
                                    );
                                    idx
                                }
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

                            insert!(r, struc.into());
                        }
                    }
                    I::Cast(r, h) => {
                        if let Some(&v) = regmap.get(&h) {
                            let ty =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).unwrap();

                            let cast = if v.is_pointer_value() && ty.is_int_type() {
                                self.builder
                                    .build_ptr_to_int(
                                        v.into_pointer_value(),
                                        ty.into_int_type(),
                                        "",
                                    )
                                    .unwrap()
                                    .into()
                            } else if v.is_int_value() && ty.is_pointer_type() {
                                self.builder
                                    .build_int_to_ptr(
                                        v.into_int_value(),
                                        ty.into_pointer_type(),
                                        "",
                                    )
                                    .unwrap()
                                    .into()
                            } else if v.is_int_value() && ty.is_int_type() {
                                // TODO: check how this works with sign/truncation
                                self.builder
                                    .build_int_cast(v.into_int_value(), ty.into_int_type(), "")
                                    .unwrap()
                                    .into()
                            } else {
                                self.builder.build_bitcast(v, ty, "").unwrap()
                            };

                            insert!(r, cast);
                        }
                    }
                    I::Uninit(r) => {
                        if let Ok(ty) = BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])) {
                            insert!(
                                r,
                                match ty {
                                    BasicTypeEnum::ArrayType(t) => t.get_undef().into(),
                                    BasicTypeEnum::FloatType(t) => t.get_undef().into(),
                                    BasicTypeEnum::IntType(t) => t.get_undef().into(),
                                    BasicTypeEnum::PointerType(t) => t.get_undef().into(),
                                    BasicTypeEnum::StructType(t) => t.get_undef().into(),
                                    BasicTypeEnum::VectorType(t) => t.get_undef().into(),
                                }
                            );
                        }
                    }
                    I::ElementPtr(r, a, m) => {
                        if let Some(&ptr) = regmap.get(&a) {
                            let array_ty =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[a].inner(ir)))
                                    .unwrap();
                            let ptr = ptr.into_pointer_value();

                            let mem = regmap[&m].into_int_value();
                            let elem_ptr = unsafe {
                                self.builder
                                    .build_in_bounds_gep(
                                        array_ty,
                                        ptr,
                                        &[self.isize_type().const_int(0, false), mem],
                                        "",
                                    )
                                    .unwrap()
                            };

                            insert!(r, elem_ptr.into());
                        }
                    }
                    I::AdjacentPtr(r, a, m) => {
                        if let Some(&ptr) = regmap.get(&a) {
                            let pointee_ty =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[a].inner(ir)))
                                    .unwrap();
                            let ptr = ptr.into_pointer_value();

                            let mem = regmap[&m].into_int_value();
                            let elem_ptr = unsafe {
                                self.builder
                                    .build_in_bounds_gep(pointee_ty, ptr, &[mem], "")
                                    .unwrap()
                            };

                            insert!(r, elem_ptr.into());
                        }
                    }
                    I::Syscall(ret, nr, ref args) => {
                        let fargs = std::iter::once(regmap[&nr])
                            .chain(args.iter().map(|r| regmap[r]))
                            .map(|v| BasicMetadataValueEnum::from(v))
                            .collect::<Vec<_>>();

                        let val = self
                            .builder
                            .build_indirect_call(
                                self.syscalls[args.len()].0,
                                self.syscalls[args.len()].1,
                                &fargs,
                                "",
                            )
                            .unwrap()
                            .try_as_basic_value()
                            .unwrap_left();

                        if let Some(ret) = ret {
                            insert!(ret, val);
                        }
                    }
                    I::Exit(code) => {
                        self.builder
                            .build_indirect_call(
                                self.syscalls[1].0,
                                self.syscalls[1].1,
                                &[
                                    self.iptr_type().const_int(60, true).into(),
                                    self.iptr_type().const_int(code, true).into(),
                                ],
                                "",
                            )
                            .unwrap();
                        self.builder.build_unreachable().unwrap();
                        continue 'outer;
                    }
                    I::Zeroinit(r) => {
                        if let Ok(ty) = BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])) {
                            insert!(
                                r,
                                match ty {
                                    BasicTypeEnum::ArrayType(t) => t.const_zero().into(),
                                    BasicTypeEnum::FloatType(t) => t.const_zero().into(),
                                    BasicTypeEnum::IntType(t) => t.const_zero().into(),
                                    BasicTypeEnum::PointerType(t) => t.const_null().into(),
                                    BasicTypeEnum::StructType(t) => t.const_zero().into(),
                                    BasicTypeEnum::VectorType(t) => t.const_zero().into(),
                                }
                            );
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
    fn get_actual_indices(&self, ir: &IR, mut ty: &[TypeIdx], idx: &mut [usize]) {
        let mut offset = 0;
        let mut mem = 0;
        for idx in idx.iter_mut() {
            let skip = *idx - offset;

            for _ in 0..skip {
                if BasicTypeEnum::try_from(self.get_type(ir, ty[0])).is_ok() {
                    mem += 1;
                }
                ty = &ty[1..];
            }

            offset = *idx;
            *idx = mem;
        }
    }
    fn get_type(&self, ir: &IR, ty: TypeIdx) -> AnyTypeEnum<'ctx> {
        match ir.types[ty] {
            Type::Int => self.int_type().into(),
            Type::IntSize => self.isize_type().into(),
            Type::IntPtr => self.iptr_type().into(),
            Type::Slice(ty) => {
                let ptr: AnyTypeEnum = match self.get_type(ir, ty) {
                    AnyTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::default()).into(),
                    AnyTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::default()).into(),
                    AnyTypeEnum::FunctionType(t) => t.ptr_type(AddressSpace::default()).into(),
                    AnyTypeEnum::IntType(t) => t.ptr_type(AddressSpace::default()).into(),
                    AnyTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::default()).into(),
                    AnyTypeEnum::StructType(t) => t.ptr_type(AddressSpace::default()).into(),
                    AnyTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::default()).into(),
                    AnyTypeEnum::VoidType(_) => self.context.void_type().into(),
                };
                if let Ok(ptr) = BasicTypeEnum::try_from(ptr) {
                    self.context
                        .struct_type(&[ptr, self.isize_type().into()], false)
                        .into()
                } else {
                    self.context
                        .struct_type(&[self.isize_type().into()], false)
                        .into()
                }
            }
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
            Type::Int8 => self.context.i8_type().into(),
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
