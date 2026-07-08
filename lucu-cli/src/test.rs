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

    let unit_t = tt.insert_unit();
    let never_t = tt.insert_never();
    let uptr_t = tt.insert_base(Base::UPTR);
    let cstr_t = tt.insert_base(Base::CString);

    let syscall1 = tt.insert_tuple([uptr_t, uptr_t]);
    let syscall3 = tt.insert_tuple([uptr_t, uptr_t, uptr_t, uptr_t]);

    let main_sig = tt.insert_function(unit_t, never_t);

    // hello world
    let syscall = et.push_expression(mu::ExpressionEnum::Operation(Operation::Callable(
        Callable::Syscall { args: 3 },
    )));
    let nr = et.push_expression(mu::ExpressionEnum::Operation(Operation::Constant(
        uptr_t,
        Constant::Integer(1),
    )));
    let file = et.push_expression(mu::ExpressionEnum::Operation(Operation::Constant(
        uptr_t,
        Constant::Integer(0),
    )));
    let transmute = et.push_expression(mu::ExpressionEnum::Operation(Operation::Callable(
        Callable::Cast {
            from: cstr_t,
            to: uptr_t,
            op: Cast::Transmute,
        },
    )));
    let msg_ptr = et.push_expression(mu::ExpressionEnum::Operation(Operation::Constant(
        cstr_t,
        Constant::String(CompactString::const_new("Hello, World!\n")),
    )));
    let msg_uptr = et.push_expression(mu::ExpressionEnum::Apply(transmute, msg_ptr));
    let msg_len = et.push_expression(mu::ExpressionEnum::Operation(Operation::Constant(
        uptr_t,
        Constant::Integer(14),
    )));
    let syscall_members = et.push_expressions([nr, file, msg_uptr, msg_len]);
    let syscall_struct =
        et.push_expression(mu::ExpressionEnum::Construct(syscall3, syscall_members));
    let syscall_apply0 = et.push_expression(mu::ExpressionEnum::Apply(syscall, syscall_struct));

    // exit
    let syscall = et.push_expression(mu::ExpressionEnum::Operation(Operation::Callable(
        Callable::Syscall { args: 1 },
    )));
    let nr = et.push_expression(mu::ExpressionEnum::Operation(Operation::Constant(
        uptr_t,
        Constant::Integer(60),
    )));
    let exit_code = et.push_expression(mu::ExpressionEnum::Operation(Operation::Constant(
        uptr_t,
        Constant::Integer(0),
    )));
    let syscall_members = et.push_expressions([nr, exit_code]);
    let syscall_struct =
        et.push_expression(mu::ExpressionEnum::Construct(syscall1, syscall_members));
    let syscall_apply1 = et.push_expression(mu::ExpressionEnum::Apply(syscall, syscall_struct));

    // function
    let body = et.push_expressions([syscall_apply0, syscall_apply1]);
    let unreachable = et.push_expression(mu::ExpressionEnum::Operation(Operation::Unreachable));
    let sequence = et.push_expression(mu::ExpressionEnum::Sequence(body, unreachable));
    let abstraction = et.push_expression(mu::ExpressionEnum::Abstract(main_sig, sequence));

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
