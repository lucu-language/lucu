use std::path::Path;
use std::process::Command;

use compact_str::CompactString;
use inkwell::OptimizationLevel;
use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::context::Context;
use inkwell::module::Linkage;
use inkwell::targets::{InitializationConfig, Target, TargetMachine, TargetMachineOptions};
use lucu::ast::Cast;
use lucu::mu::table::{ExpressionTable, TypeTable};
use lucu::mu::{Base, Callable, Constant, Operation};
use mu::{ExpressionTable as _, TypeTable as _};

pub(super) fn test() {
    // CREATE
    let tt = unsafe { TypeTable::new() };
    let et = unsafe { ExpressionTable::new() };

    let unit_t = tt.unit();
    let never_t = tt.never();
    let bool_t = tt.base(Base::Boolean);
    let uptr_t = tt.base(Base::UPTR);
    let cstr_t = tt.base(Base::CString);

    let syscall1 = tt.insert_tuple([uptr_t, uptr_t]);
    let syscall3 = tt.insert_tuple([uptr_t, uptr_t, uptr_t, uptr_t]);

    let branch_sig = tt.function(unit_t, unit_t);

    // let
    let boolean = et.operation(Operation::Constant(bool_t, Constant::Integer(1)));
    let abstraction = et.lambda(
        unit_t,
        et.sequence(
            [
                et.let_chain(
                    [
                        et.cast(
                            cstr_t,
                            uptr_t,
                            Cast::Transmute,
                            et.constant(
                                cstr_t,
                                Constant::String(CompactString::const_new("Hello, World!\n")),
                            ),
                        ),
                        et.constant(uptr_t, Constant::Integer(14)),
                    ],
                    et.apply_operation_multi(
                        Operation::Callable(Callable::If),
                        tt.insert_tuple([bool_t, branch_sig]),
                        [
                            boolean,
                            et.lambda(
                                unit_t,
                                et.apply_multi(
                                    et.operation(Operation::Callable(Callable::Syscall {
                                        args: 3,
                                    })),
                                    syscall3,
                                    [
                                        // nr
                                        et.constant(uptr_t, Constant::Integer(1)),
                                        // file
                                        et.constant(uptr_t, Constant::Integer(0)),
                                        // msg ptr
                                        et.reference(uptr_t, 2),
                                        // msg len
                                        et.reference(uptr_t, 1),
                                    ],
                                ),
                            ),
                        ],
                    ),
                ),
                et.apply_operation_multi(
                    Operation::Callable(Callable::Syscall { args: 1 }),
                    syscall1,
                    [
                        // nr
                        et.constant(uptr_t, Constant::Integer(60)),
                        // exit code
                        et.constant(uptr_t, Constant::Integer(0)),
                    ],
                ),
            ],
            et.operation(Operation::Unreachable),
        ),
    );

    // COMPILE
    Target::initialize_native(&InitializationConfig::default()).unwrap();

    let triple = TargetMachine::get_default_triple();
    let machine = Target::from_triple(&triple)
        .unwrap()
        .create_target_machine_from_options(
            &triple,
            TargetMachineOptions::new().set_level(OptimizationLevel::Aggressive),
        )
        .unwrap();

    let context = Context::create();
    let llvm = mu_llvm::Context::new(&context, &tt, &et, &lucu_llvm::Builder, machine, "main");
    let fun = llvm.build_function(abstraction, "_start", Some(Linkage::External));
    fun.add_attribute(
        AttributeLoc::Function,
        context.create_enum_attribute(Attribute::get_named_enum_kind_id("sspstrong"), 0),
    );
    fun.add_attribute(
        AttributeLoc::Function,
        context.create_enum_attribute(Attribute::get_named_enum_kind_id("noreturn"), 0),
    );
    fun.add_attribute(
        AttributeLoc::Function,
        context.create_string_attribute("stackrealign", ""),
    );

    eprintln!(" --- LLVM --- ");
    llvm.eprint();
    llvm.optimize().unwrap();
    eprintln!(" --- LLVM O3 --- ");
    llvm.eprint();

    llvm.write_asm(Path::new("out.asm")).unwrap();
    llvm.write_object(Path::new("out.o")).unwrap();
    Command::new("ld")
        .arg("out.o")
        .arg("-o")
        .arg("out")
        .arg("-e_start")
        .status()
        .unwrap();
}
