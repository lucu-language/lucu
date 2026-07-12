use std::path::Path;
use std::process::Command;

use compact_str::CompactString;
use inkwell::OptimizationLevel;
use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::context::Context;
use inkwell::module::Linkage;
use inkwell::targets::{InitializationConfig, Target, TargetMachine, TargetMachineOptions};
use lucu::ast::{Cast, EqualityOp, MathOp, PredicateOp, UnOp};
use lucu::mu::table::{ExpressionTable, TypeTable};
use lucu::mu::{Base, Callable, Constant, Operation};
use lucu::type_table::{IntSize, Integer};
use mu::{ExpressionTable as _, TypeTable as _};

pub(super) fn test() {
    // CREATE
    let tt = unsafe { TypeTable::new() };
    let et = unsafe { ExpressionTable::new() };

    let i8_t = tt.base(Base::Integer(Integer::signed(IntSize::Exact(8))));
    let unit_t = tt.unit();
    let uptr_t = tt.base(Base::UPTR);
    let usize_t = tt.base(Base::USIZE);
    let array_size = 16;
    let i8_ptr_t = tt.base(Base::Pointer(i8_t));
    let uptr_ptr_t = tt.base(Base::Pointer(uptr_t));
    let uptr_slice_ptr_t = tt.base(Base::PointerSlice(uptr_t));
    let uptr_array_t = tt.base(Base::Array(uptr_t, array_size));
    let uptr_array_ptr_t = tt.base(Base::Pointer(uptr_array_t));
    let uptr_array_ptr_tuple = tt.insert_tuple([uptr_array_ptr_t]);
    let uptr_array_ptr_tuple_t = tt.insert_type(mu::TypeEnum::Product(uptr_array_ptr_tuple));
    let str_t = tt.base(Base::PointerSlice(i8_t));
    let unit_tuple = tt.insert_tuple([unit_t]);

    // let
    let abstraction = et.lambda(
        unit_tuple,
        et.sequence(
            [
                et.let_chain(
                    [
                        et.if_else(
                            et.call(
                                Callable::PredicateOp {
                                    ty: i8_t,
                                    op: PredicateOp::Equality(EqualityOp::Equals),
                                },
                                [
                                    // 1 % -123 == 1
                                    et.call(
                                        Callable::MathOp {
                                            ty: i8_t,
                                            op: MathOp::Mod,
                                        },
                                        [
                                            et.constant(i8_t, Constant::Integer(1)),
                                            et.call(
                                                Callable::UnOp {
                                                    ty: i8_t,
                                                    op: UnOp::Negate,
                                                },
                                                [et.constant(i8_t, Constant::Integer(123))],
                                            ),
                                        ],
                                    ),
                                    et.constant(i8_t, Constant::Integer(1)),
                                ],
                            ),
                            et.constant(
                                str_t,
                                Constant::String(CompactString::const_new("Hello, World!\n")),
                            ),
                            et.constant(
                                str_t,
                                Constant::String(CompactString::const_new("Wrong value?\n")),
                            ),
                        ),
                        et.call(
                            Callable::LetReference {
                                ty: uptr_array_t,
                                to: uptr_t,
                            },
                            [
                                et.constant(uptr_array_t, Constant::Uninit),
                                et.lambda(
                                    uptr_array_ptr_tuple,
                                    et.let_chain(
                                        [
                                            et.call(
                                                Callable::PointerArraySlice {
                                                    ty: uptr_t,
                                                    size: array_size,
                                                },
                                                [
                                                    et.member(
                                                        et.reference(uptr_array_ptr_tuple_t, 0),
                                                        0,
                                                    ),
                                                    et.constant(usize_t, Constant::Zero),
                                                    et.constant(
                                                        usize_t,
                                                        Constant::Integer(array_size as u64),
                                                    ),
                                                ],
                                            ),
                                            et.call(
                                                Callable::PointerSliceIndex { ty: uptr_t },
                                                [
                                                    et.reference(uptr_slice_ptr_t, 0),
                                                    et.constant(usize_t, Constant::Integer(6)),
                                                ],
                                            ),
                                            et.call(
                                                Callable::PointerSliceIndex { ty: uptr_t },
                                                [
                                                    et.reference(uptr_slice_ptr_t, 1),
                                                    et.constant(usize_t, Constant::Integer(7)),
                                                ],
                                            ),
                                        ],
                                        et.sequence(
                                            [
                                                et.call(
                                                    Callable::Write { ty: uptr_t },
                                                    [
                                                        et.reference(uptr_ptr_t, 0),
                                                        et.constant(uptr_t, Constant::Integer(13)),
                                                    ],
                                                ),
                                                et.call(
                                                    Callable::Write { ty: uptr_t },
                                                    [
                                                        et.reference(uptr_ptr_t, 1),
                                                        et.constant(uptr_t, Constant::Integer(14)),
                                                    ],
                                                ),
                                            ],
                                            et.call(
                                                Callable::Read { ty: uptr_t },
                                                [et.reference(uptr_ptr_t, 1)],
                                            ),
                                        ),
                                    ),
                                ),
                            ],
                        ),
                    ],
                    et.if_stmt(
                        &tt,
                        et.call(
                            Callable::PredicateOp {
                                ty: usize_t,
                                op: PredicateOp::Equality(EqualityOp::Equals),
                            },
                            [
                                et.call(Callable::Len { ty: i8_t }, [et.reference(str_t, 1)]),
                                et.cast(uptr_t, usize_t, Cast::Truncate, et.reference(uptr_t, 0)),
                            ],
                        ),
                        et.call(
                            Callable::Syscall { args: 3 },
                            [
                                // nr
                                et.constant(uptr_t, Constant::Integer(1)),
                                // file
                                et.constant(uptr_t, Constant::Integer(0)),
                                // msg ptr
                                et.cast(
                                    i8_ptr_t,
                                    uptr_t,
                                    Cast::Transmute,
                                    et.call(
                                        Callable::PointerSliceIndex { ty: i8_t },
                                        [
                                            et.reference(str_t, 2),
                                            et.constant(usize_t, Constant::Zero),
                                        ],
                                    ),
                                ),
                                // msg len
                                et.reference(uptr_t, 1),
                            ],
                        ),
                    ),
                ),
                et.call(
                    Callable::Syscall { args: 1 },
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
    llvm.verify().unwrap();
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
