use std::{collections::HashMap, path::Path};

use either::Either;
use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    passes::{PassManager, PassManagerBuilder},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetData, TargetTriple,
    },
    types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicTypeEnum, FunctionType, IntType, StructType},
    values::{
        AggregateValueEnum, BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallSiteValue,
        FunctionValue, IntValue, PhiValue, PointerValue,
    },
    AddressSpace, IntPredicate, OptimizationLevel,
};

use crate::{
    ir::{
        AggrIdx, AggregateType, HandlerIdx, Instruction, ProcForeign, ProcForeignIdx, ProcIdx,
        ProcImpl, ProcSign, Type, TypeIdx, IR,
    },
    vecmap::VecMap,
    LucuArch, LucuOS,
};

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    target_data: TargetData,

    structs: VecMap<AggrIdx, Option<StructType<'ctx>>>,

    procs: VecMap<ProcIdx, FunctionValue<'ctx>>,
    foreign: VecMap<
        ProcForeignIdx,
        Either<FunctionValue<'ctx>, (FunctionType<'ctx>, PointerValue<'ctx>)>,
    >,

    syscalls: Vec<Option<(FunctionType<'ctx>, PointerValue<'ctx>)>>,

    os: LucuOS,
    arch: LucuArch,
}

pub fn generate_ir(ir: &IR, path: &Path, debug: bool, target: &crate::Target) {
    let config = &InitializationConfig::default();
    match target.lucu_arch() {
        LucuArch::X86_32 => Target::initialize_x86(config),
        LucuArch::X86_64 => Target::initialize_x86(config),
        LucuArch::Arm32 => Target::initialize_arm(config),
        LucuArch::Arm64 => Target::initialize_aarch64(config),
        LucuArch::Wasm32 => Target::initialize_webassembly(config),
        LucuArch::Wasm64 => Target::initialize_webassembly(config),
    }

    let context = Context::create();
    let module = context.create_module("main");

    let os = target.lucu_os();
    let arch = target.lucu_arch();

    let triple = TargetTriple::create(&target.triple);
    let target_machine = Target::from_triple(&triple)
        .unwrap()
        .create_target_machine(
            &triple,
            target.cpu.as_deref().unwrap_or(""),
            target.features.as_deref().unwrap_or(""),
            OptimizationLevel::Aggressive,
            RelocMode::Default,
            CodeModel::Default,
        )
        .unwrap();
    let target_data = target_machine.get_target_data();
    let reg_ty = context.custom_width_int_type(arch.register_size());

    let syscalls = match os {
        LucuOS::Linux => (0..=6)
            .map(|n| {
                const SYS_RET: &str = "rax";
                const SYS_NR: &str = "rax";
                const SYS_ARGS: [&str; 6] = ["rdi", "rsi", "rdx", "r10", "r8", "r9"];
                const SYS_CLOBBER: [&str; 2] = ["rcx", "r11"];

                let inputs = std::iter::repeat(BasicMetadataTypeEnum::from(reg_ty))
                    .take(n + 1)
                    .collect::<Vec<_>>();
                let ty = reg_ty.fn_type(&inputs, false);

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

                Some((ty, asm))
            })
            .collect::<Vec<_>>(),
        _ => vec![],
    };

    let builder = context.create_builder();
    let mut codegen = CodeGen {
        context: &context,
        module,
        builder,
        target_data,
        structs: VecMap::new(),
        procs: VecMap::new(),
        foreign: VecMap::new(),
        syscalls,
        os,
        arch,
    };

    for typ in ir.aggregates.values() {
        let struc = codegen.generate_struct(typ);
        codegen.structs.push_value(struc);
    }
    for idx in ir.aggregates.keys(AggrIdx) {
        codegen.fill_struct(ir, idx);
    }

    for proc in ir.proc_foreign.values() {
        let func = codegen.generate_foreign_proc_sign(ir, proc);
        codegen.foreign.push_value(func);
    }

    for (idx, proc) in ir.proc_sign.iter(ProcIdx) {
        let func = codegen.generate_proc_sign(ir, proc, idx == ir.entry);
        codegen.procs.push_value(func);
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
    let start = codegen.procs[ir.entry];
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

    // __stack_chk_guard and __stack_chk_fail
    let guard = codegen
        .module
        .add_global(codegen.iptr_type(), None, "__stack_chk_guard");
    guard.set_linkage(Linkage::Internal);
    guard.set_initializer(&codegen.iptr_type().get_undef());

    let fail = codegen.module.add_function(
        "__stack_chk_fail",
        context.void_type().fn_type(&[], false),
        Some(Linkage::Internal),
    );

    let fail_block = context.append_basic_block(fail, "");
    codegen.builder.position_at_end(fail_block);
    // codegen.builder.build_call(trap, &[], "").unwrap();
    codegen.builder.build_unreachable().unwrap();

    // memset
    let u8_ptr = context.i8_type().ptr_type(AddressSpace::default());
    let uptr = context.ptr_sized_int_type(&codegen.target_data, None);

    let memset = codegen.module.add_function(
        "memset",
        u8_ptr.fn_type(
            &[
                u8_ptr.into(),
                context.i32_type().into(), // TODO: C int
                uptr.into(),
            ],
            false,
        ),
        Some(Linkage::Internal),
    );

    let start = memset.get_nth_param(0).unwrap().into_pointer_value();
    let char = memset.get_nth_param(1).unwrap().into_int_value();
    let size = memset.get_nth_param(2).unwrap().into_int_value();

    let memset_entry = context.append_basic_block(memset, "");
    let memset_init = context.append_basic_block(memset, "init");
    let memset_loop = context.append_basic_block(memset, "loop");
    let memset_ret = context.append_basic_block(memset, "end");

    codegen.builder.position_at_end(memset_entry);
    let char = codegen
        .builder
        .build_int_truncate(char, context.i8_type(), "")
        .unwrap();
    let end = unsafe {
        codegen
            .builder
            .build_gep(context.i8_type(), start, &[size], "end")
            .unwrap()
    };
    codegen
        .builder
        .build_unconditional_branch(memset_init)
        .unwrap();

    codegen.builder.position_at_end(memset_init);
    let phi = codegen.builder.build_phi(u8_ptr, "current").unwrap();
    let current = phi.as_basic_value().into_pointer_value();
    let lhs = codegen
        .builder
        .build_ptr_to_int(current, uptr, "lhs")
        .unwrap();
    let rhs = codegen.builder.build_ptr_to_int(end, uptr, "rhs").unwrap();
    let cmp = codegen
        .builder
        .build_int_compare(IntPredicate::EQ, lhs, rhs, "cmp")
        .unwrap();
    codegen
        .builder
        .build_conditional_branch(cmp, memset_ret, memset_loop)
        .unwrap();

    codegen.builder.position_at_end(memset_loop);
    codegen.builder.build_store(current, char).unwrap();
    let next = unsafe {
        codegen
            .builder
            .build_gep(
                context.i8_type(),
                current,
                &[uptr.const_int(1, false)],
                "next",
            )
            .unwrap()
    };
    phi.add_incoming(&[(&start, memset_entry), (&next, memset_loop)]);
    codegen
        .builder
        .build_unconditional_branch(memset_init)
        .unwrap();

    codegen.builder.position_at_end(memset_ret);
    codegen.builder.build_return(Some(&start)).unwrap();

    let used_const = u8_ptr.const_array(&[
        guard.as_pointer_value().const_cast(u8_ptr),
        fail.as_global_value().as_pointer_value().const_cast(u8_ptr),
        memset
            .as_global_value()
            .as_pointer_value()
            .const_cast(u8_ptr),
    ]);

    let used = codegen
        .module
        .add_global(used_const.get_type(), None, "llvm.compiler.used");
    used.set_linkage(Linkage::Appending);
    used.set_section(Some("llvm.metadata"));
    used.set_initializer(&used_const);

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
        .write_to_file(
            &codegen.module,
            FileType::Assembly,
            &path.with_extension("asm"),
        )
        .unwrap();

    target_machine
        .write_to_file(&codegen.module, FileType::Object, path)
        .unwrap();
}

impl<'ctx> CodeGen<'ctx> {
    fn generate_struct(&self, typ: &AggregateType) -> Option<StructType<'ctx>> {
        let struc = self.context.opaque_struct_type(&typ.debug_name);
        Some(struc)
    }
    fn fill_struct(&self, ir: &IR, idx: AggrIdx) {
        let typ = &ir.aggregates[idx];
        let struc = self.structs[idx].unwrap();

        let fields: Vec<BasicTypeEnum> = typ
            .children
            .iter()
            .copied()
            .filter_map(|typ| BasicTypeEnum::try_from(self.get_type(ir, typ)).ok())
            .collect();

        struc.set_body(&fields, false);
    }
    fn frame_type(&self) -> IntType<'ctx> {
        self.isize_type()
    }
    fn iptr_type(&self) -> IntType<'ctx> {
        self.context.custom_width_int_type(self.arch.ptr_size())
    }
    fn isize_type(&self) -> IntType<'ctx> {
        self.context
            .custom_width_int_type(self.arch.array_len_size())
    }
    fn int_type(&self) -> IntType<'ctx> {
        self.context
            .custom_width_int_type(self.arch.register_size())
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
            BasicTypeEnum::PointerType(_) => "ptr".into(),
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
                .chain(proc.unhandled.iter().copied().map(|h| &ir.break_types[h]))
                .copied()
                .filter_map(|t| BasicTypeEnum::try_from(self.get_type(ir, t)).ok())
                .max_by_key(|&t| self.align(t));
            let max_size = std::iter::once(&proc.output)
                .chain(proc.unhandled.iter().copied().map(|h| &ir.break_types[h]))
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
                let typ = self.context.opaque_struct_type("tagged_void");
                typ.set_body(&[frame_type.into()], false);
                typ.into()
            }
        }
    }
    fn generate_proc_sign(&self, ir: &IR, proc: &ProcSign, entry: bool) -> FunctionValue<'ctx> {
        let in_types = proc
            .inputs
            .iter()
            .filter_map(|&r| BasicMetadataTypeEnum::try_from(self.get_type(ir, ir.regs[r])).ok())
            .collect::<Vec<_>>();

        let fn_type = match self.return_type(ir, proc) {
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
        let fn_name = &format!("${}", proc.debug_name);
        let func = self.module.add_function(
            if entry { "_start" } else { &fn_name },
            fn_type,
            Some(if entry {
                Linkage::External
            } else {
                Linkage::Internal
            }),
        );

        func
    }
    fn generate_foreign_proc_sign(
        &self,
        ir: &IR,
        proc: &ProcForeign,
    ) -> Either<FunctionValue<'ctx>, (FunctionType<'ctx>, PointerValue<'ctx>)> {
        let in_types = proc
            .inputs
            .iter()
            .filter_map(|&ty| BasicMetadataTypeEnum::try_from(self.get_type(ir, ty)).ok())
            .collect::<Vec<_>>();

        let fn_type = match self.get_type(ir, proc.output) {
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
        match &proc.asm {
            Some(asm) => {
                let func = self.context.create_inline_asm(
                    fn_type,
                    asm.assembly.clone(),
                    asm.constraints.clone(),
                    asm.sideeffects,
                    false,
                    None,
                    false,
                );
                Either::Right((fn_type, func))
            }
            None => {
                let func = self
                    .module
                    .add_function(&proc.symbol, fn_type, Some(Linkage::External));

                if matches!(self.arch, LucuArch::Wasm32 | LucuArch::Wasm64) {
                    func.add_attribute(
                        AttributeLoc::Function,
                        self.context.create_string_attribute(
                            "wasm-import-module",
                            self.os.wasm_import_module(),
                        ),
                    );
                }

                Either::Left(func)
            }
        }
    }
    fn generate_proc(
        &self,
        ir: &IR,
        proc: &ProcSign,
        imp: &ProcImpl,
        function: FunctionValue<'ctx>,
    ) {
        // do not probe the stack
        // TODO: link with a library on windows that has a stack prober
        function.add_attribute(
            AttributeLoc::Function,
            self.context
                .create_string_attribute("no-stack-arg-probe", ""),
        );

        let blocks: Vec<_> = (0..imp.blocks.len())
            .map(|idx| {
                self.context
                    .append_basic_block(function, &format!("L{}", idx))
            })
            .collect();
        let mut blocks_end = blocks.clone();

        let mut regmap = HashMap::new();
        for (n, &reg) in proc
            .inputs
            .iter()
            .filter(|&&r| !self.get_type(ir, ir.regs[r]).is_void_type())
            .enumerate()
        {
            regmap.insert(reg, function.get_nth_param(n as u32).unwrap());
        }

        let phis: Vec<_> = imp
            .blocks
            .values()
            .enumerate()
            .map(|(idx, block)| {
                let mut phis = Vec::new();

                self.builder.position_at_end(blocks[idx]);
                for &(reg, _) in block.phis.iter() {
                    let ty = self.get_type(ir, ir.regs[reg]);
                    if let Ok(ty) = BasicTypeEnum::try_from(ty) {
                        let phi = self.builder.build_phi(ty, "").unwrap();
                        phis.push(phi);
                        regmap.insert(reg, phi.as_basic_value());
                    }
                }

                phis
            })
            .collect();

        'outer: for (idx, block) in imp.blocks.values().enumerate() {
            let basic_block = blocks[idx];
            self.builder.position_at_end(basic_block);

            for instr in block.instructions.iter() {
                use Instruction as I;
                match *instr {
                    I::Init(r, v) => {
                        let ty = self.get_type(ir, ir.regs[r]).into_int_type();
                        regmap.insert(r, ty.const_int(v, false).into());
                    }
                    I::Copy(r, v) => {
                        if let Some(v) = regmap.get(&v).copied() {
                            regmap.insert(r, v);
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

                        regmap.insert(r, const_str_slice.into());
                    }
                    I::Jump(b) => {
                        self.builder
                            .build_unconditional_branch(blocks[usize::from(b)])
                            .unwrap();
                        continue 'outer;
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
                    I::Equals(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                            .unwrap();
                        regmap.insert(r, res.into());
                    }
                    I::Div(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_signed_div(lhs, rhs, "div").unwrap();
                        regmap.insert(r, res.into());
                    }
                    I::Mul(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_mul(lhs, rhs, "mul").unwrap();
                        regmap.insert(r, res.into());
                    }
                    I::Add(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_add(lhs, rhs, "add").unwrap();
                        regmap.insert(r, res.into());
                    }
                    I::Sub(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self.builder.build_int_sub(lhs, rhs, "sub").unwrap();
                        regmap.insert(r, res.into());
                    }
                    I::Greater(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::UGT, lhs, rhs, "gt")
                            .unwrap();
                        regmap.insert(r, res.into());
                    }
                    I::Less(r, a, b) => {
                        let lhs = regmap[&a].into_int_value();
                        let rhs = regmap[&b].into_int_value();
                        let res = self
                            .builder
                            .build_int_compare(IntPredicate::ULT, lhs, rhs, "lt")
                            .unwrap();
                        regmap.insert(r, res.into());
                    }
                    I::CallForeign(p, r, ref rs) => {
                        let func = self.foreign[p];
                        let args: Vec<_> = rs
                            .iter()
                            .filter_map(|r| regmap.get(r).map(|&v| v.into()))
                            .collect();

                        let ret = match func {
                            Either::Left(func) => self.builder.build_call(func, &args, "").unwrap(),
                            Either::Right((ty, ptr)) => self
                                .builder
                                .build_indirect_call(ty, ptr, &args, "")
                                .unwrap(),
                        };

                        if let Some(r) = r {
                            if let Either::Left(v) = ret.try_as_basic_value() {
                                regmap.insert(r, v);
                            }
                        }
                    }
                    I::Call(p, r, ref rs, ref handled) => {
                        let func = self.procs[p];
                        let args: Vec<_> = rs
                            .iter()
                            .filter_map(|r| regmap.get(r).map(|&v| v.into()))
                            .collect();

                        let ret = self.builder.build_call(func, &args, "").unwrap();
                        let (frame, val) = self.get_return(&ir.proc_sign[p], ret);

                        if let Some(frame) = frame {
                            let handlers = handled.iter().copied().map(|(h, b)| {
                                (
                                    h,
                                    blocks[usize::from(b)],
                                    phis[usize::from(b)].get(0).copied(),
                                )
                            });
                            blocks_end[idx] = self.handle_break(
                                ir,
                                function,
                                frame,
                                val,
                                handlers,
                                !proc.unhandled.is_empty(),
                            );
                        }

                        if let Some(r) = r {
                            let typ = self.get_type(ir, ir.regs[r]);
                            if let Ok(typ) = BasicTypeEnum::try_from(typ) {
                                let val = val.unwrap_or_else(|| {
                                    panic!("call {} returns no value", ir.proc_sign[p].debug_name)
                                });
                                let cast = self.build_union_cast(val, typ);
                                regmap.insert(r, cast);
                            }
                        }
                    }
                    I::Yeet(r, h, b) => match b {
                        Some(b) => {
                            let val = r.and_then(|r| regmap.get(&r)).copied();
                            let phi = phis[usize::from(b)].get(0).copied();

                            if let (Some(val), Some(phi)) = (val, phi) {
                                phi.add_incoming(&[(&val, basic_block)]);
                            }

                            self.builder
                                .build_unconditional_branch(blocks[usize::from(b)])
                                .unwrap();
                            continue 'outer;
                        }
                        None => {
                            let frame = self
                                .frame_type()
                                .const_int(usize::from(h.unwrap()) as u64, false);
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
                    },
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
                    I::Aggregate(r, ref rs) => {
                        let aggr_ty = self.get_type(ir, ir.regs[r]);

                        // do not aggregate void
                        if !aggr_ty.is_void_type() {
                            let mut aggr: AggregateValueEnum = match aggr_ty {
                                AnyTypeEnum::ArrayType(ty) => ty.get_poison().into(),
                                AnyTypeEnum::StructType(ty) => ty.get_poison().into(),
                                _ => unreachable!(),
                            };

                            for (n, &member) in rs.iter().filter_map(|r| regmap.get(r)).enumerate()
                            {
                                aggr = self
                                    .builder
                                    .build_insert_value(aggr, member, n as u32, "")
                                    .unwrap()
                            }

                            regmap.insert(
                                r,
                                match aggr {
                                    AggregateValueEnum::ArrayValue(ty) => ty.into(),
                                    AggregateValueEnum::StructValue(ty) => ty.into(),
                                },
                            );
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

                                    regmap.insert(r, member);
                                }
                            }
                            Type::ConstArray(_, _) => {
                                if let Some(aggr) = regmap.get(&a).map(|v| v.into_array_value()) {
                                    let member = self
                                        .builder
                                        .build_extract_value(aggr, n as u32, "member")
                                        .unwrap();
                                    regmap.insert(r, member);
                                }
                            }
                            _ => panic!(),
                        }
                    }
                    I::Unreachable => {
                        self.builder.build_unreachable().unwrap();
                        continue 'outer;
                    }
                    I::Reference(ptrr, r) => {
                        if let Some(val) = regmap.get(&r).copied() {
                            let ptr = self.builder.build_alloca(val.get_type(), "").unwrap();
                            self.builder.build_store(ptr, val).unwrap();
                            regmap.insert(ptrr, ptr.into());
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
                            regmap.insert(r, v);
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

                            regmap.insert(r, cast);
                        }
                    }
                    I::Uninit(r) => {
                        if let Ok(ty) = BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])) {
                            regmap.insert(
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
                    I::ElementPtr(r, a, n) => {
                        // skip over empty children that are uncounted
                        match ir.types[ir.regs[a].inner(ir)] {
                            Type::Handler(_, t) | Type::Aggregate(t) => {
                                // get member
                                if BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])).is_ok() {
                                    let mut mem = [n];
                                    self.get_actual_indices(
                                        ir,
                                        &ir.aggregates[t].children,
                                        &mut mem,
                                    );
                                    let n = mem[0];

                                    let ptr = regmap[&a].into_pointer_value();
                                    let elem_ptr = unsafe {
                                        self.builder
                                            .build_in_bounds_gep(
                                                self.structs[t].unwrap(),
                                                ptr,
                                                &[
                                                    self.context.i64_type().const_int(0, false),
                                                    self.context
                                                        .i32_type()
                                                        .const_int(n as u64, false),
                                                ],
                                                "",
                                            )
                                            .unwrap()
                                    };

                                    regmap.insert(r, elem_ptr.into());
                                }
                            }
                            _ => panic!(),
                        }
                    }
                    I::AdjacentPtr(r, a, m) => {
                        if let Some(&ptr) = regmap.get(&a) {
                            let pointee_ty =
                                BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r].inner(ir)))
                                    .unwrap();
                            let ptr = ptr.into_pointer_value();

                            let mem = regmap[&m].into_int_value();
                            let elem_ptr = unsafe {
                                self.builder
                                    .build_in_bounds_gep(pointee_ty, ptr, &[mem], "")
                                    .unwrap()
                            };

                            regmap.insert(r, elem_ptr.into());
                        }
                    }
                    I::Syscall(ret, nr, ref args) => {
                        let fargs = std::iter::once(regmap[&nr])
                            .chain(args.iter().map(|r| regmap[r]))
                            .map(BasicMetadataValueEnum::from)
                            .collect::<Vec<_>>();

                        let val = self
                            .builder
                            .build_indirect_call(
                                self.syscalls[args.len()].unwrap().0,
                                self.syscalls[args.len()].unwrap().1,
                                &fargs,
                                "",
                            )
                            .unwrap()
                            .try_as_basic_value()
                            .unwrap_left();

                        if let Some(ret) = ret {
                            regmap.insert(ret, val);
                        }
                    }
                    I::WasmTrap => {
                        assert!(self.arch.is_wasm());
                        let asm_ty = self.context.void_type().fn_type(&[], false);
                        let asm = self.context.create_inline_asm(
                            asm_ty,
                            "unreachable".into(),
                            "".into(),
                            true,
                            false,
                            None,
                            false,
                        );
                        self.builder
                            .build_indirect_call(asm_ty, asm, &[], "")
                            .unwrap();
                        self.builder.build_unreachable().unwrap();
                        continue 'outer;
                    }
                    I::Zeroinit(r) => {
                        if let Ok(ty) = BasicTypeEnum::try_from(self.get_type(ir, ir.regs[r])) {
                            regmap.insert(
                                r,
                                match ty {
                                    BasicTypeEnum::ArrayType(t) => t.const_zero().into(),
                                    BasicTypeEnum::FloatType(t) => t.const_zero().into(),
                                    BasicTypeEnum::IntType(t) => t.const_zero().into(),
                                    BasicTypeEnum::PointerType(t) => t.const_null().into(),
                                    BasicTypeEnum::StructType(t) => t.const_zero().into(),
                                    BasicTypeEnum::VectorType(t) => t.const_zero().into(),
                                },
                            );
                        }
                    }
                }
            }
        }

        // populate phi values
        for (phis, block) in phis.into_iter().zip(imp.blocks.values()) {
            let mut phis = phis.into_iter();
            for &(reg, ref regs) in block.phis.iter() {
                let ty = self.get_type(ir, ir.regs[reg]);
                if BasicTypeEnum::try_from(ty).is_err() {
                    continue;
                }

                let phi = phis.next().unwrap();
                for (val, from) in regs.iter().filter_map(|&(reg, from)| {
                    Some((regmap.get(&reg).copied()?, blocks_end[usize::from(from)]))
                }) {
                    phi.add_incoming(&[(&val, from)])
                }
            }
        }
    }
    fn handle_break(
        &self,
        ir: &IR,
        function: FunctionValue<'ctx>,
        frame: IntValue<'ctx>,
        val: Option<BasicValueEnum<'ctx>>,
        handlers: impl Iterator<Item = (HandlerIdx, BasicBlock<'ctx>, Option<PhiValue<'ctx>>)>,
        bubble_break: bool,
    ) -> BasicBlock<'ctx> {
        // branch handled breaks
        for (handler, block, phi) in handlers {
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

            let branch_next = self.context.append_basic_block(function, "");
            let branch_break = self.context.append_basic_block(function, "handled");
            self.builder
                .build_conditional_branch(cmp_handler, branch_break, branch_next)
                .unwrap();

            self.builder.position_at_end(branch_break);
            let ty = self.get_type(ir, ir.break_types[handler]);
            if let (Some(val), Some(field), Some(phi)) =
                (val, BasicTypeEnum::try_from(ty).ok(), phi)
            {
                let cast = self.build_union_cast(val, field);
                phi.add_incoming(&[(&cast, branch_break)]);
            }
            self.builder.build_unconditional_branch(block).unwrap();

            self.builder.position_at_end(branch_next);
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
        }

        self.builder.get_insert_block().unwrap()
    }
    fn build_union_cast(
        &self,
        val: BasicValueEnum<'ctx>,
        typ: BasicTypeEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        if val.get_type() == typ {
            val
        } else if self.size(typ) <= self.size(val.get_type()) {
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
            Type::Aggregate(idx) | Type::Handler(_, idx) => match self.structs[idx] {
                Some(t) => t.into(),
                None => self.context.void_type().into(),
            },
            Type::Unit | Type::Never => self.context.void_type().into(),
            Type::Int8 => self.context.i8_type().into(),
            Type::Int16 => self.context.i16_type().into(),
            Type::Int32 => self.context.i32_type().into(),
            Type::Int64 => self.context.i64_type().into(),
            Type::Bool => self.context.bool_type().into(),
            Type::Pointer(ty) => {
                if matches!(ir.types[ty], Type::Never) {
                    self.context
                        .i8_type()
                        .ptr_type(AddressSpace::default())
                        .into()
                } else {
                    match self.get_type(ir, ty) {
                        AnyTypeEnum::ArrayType(t) => t.ptr_type(AddressSpace::default()).into(),
                        AnyTypeEnum::FloatType(t) => t.ptr_type(AddressSpace::default()).into(),
                        AnyTypeEnum::FunctionType(t) => t.ptr_type(AddressSpace::default()).into(),
                        AnyTypeEnum::IntType(t) => t.ptr_type(AddressSpace::default()).into(),
                        AnyTypeEnum::PointerType(t) => t.ptr_type(AddressSpace::default()).into(),
                        AnyTypeEnum::StructType(t) => t.ptr_type(AddressSpace::default()).into(),
                        AnyTypeEnum::VectorType(t) => t.ptr_type(AddressSpace::default()).into(),
                        AnyTypeEnum::VoidType(_) => self.context.void_type().into(),
                    }
                }
            }
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
