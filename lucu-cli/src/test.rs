use std::process::Command;
use std::sync::Arc;

use lucu::ir::{Block, FunctionDefinition, IR, Instruction};
use lucu::llvm;
use lucu::module::Module;
use lucu::pass::ModuleGraph;
use lucu::type_table::{
    ConstantEnum, EffectEnum, FunctionSignatureValue, RegionEnum, Sentinel, Thunk, TypeEnum,
    TypeTable,
};

pub(super) fn test() {
    let tt = TypeTable::new();
    let unit_t = tt.insert_type(TypeEnum::Unit);
    let unit_e = tt.insert_effect(EffectEnum::empty());
    let sig = tt.insert_function_signature(FunctionSignatureValue {
        type_params: None,
        implicit_regions: 0,
        params: None,
        thunk: Thunk {
            returns: unit_t,
            effect: unit_e,
        },
    });

    let region_static = tt.insert_region(RegionEnum::Static);

    let u8_t = tt.insert_type(TypeEnum::U8);
    let uptr_t = tt.insert_type(TypeEnum::UPTR);
    let cstring_t = tt.insert_type(TypeEnum::PointerSlice(u8_t, region_static, Some(Sentinel)));

    let ir = IR::default();
    let function = ir.push_function(FunctionDefinition {
        name: "_start".into(),
        type_params: Arc::new([]),
        sig,
        closure: Arc::new([]),
        blocks: Box::new([Block {
            instructions: Box::new([
                // write syscall
                (
                    uptr_t,
                    Instruction::Constant(tt.insert_constant(ConstantEnum::Integer(1))),
                ),
                // stdout
                (
                    uptr_t,
                    Instruction::Constant(tt.insert_constant(ConstantEnum::Integer(0))),
                ),
                // message ptr
                (
                    cstring_t,
                    Instruction::Constant(
                        tt.insert_constant(ConstantEnum::String("Hello, World!\n".into())),
                    ),
                ),
                // message length
                (
                    uptr_t,
                    Instruction::Constant(tt.insert_constant(ConstantEnum::Integer(14))),
                ),
                // syscall
                (
                    uptr_t,
                    Instruction::Syscall {
                        nr: 0,
                        args: Box::new([1, 2, 3]),
                    },
                ),
                // exit syscall
                (
                    uptr_t,
                    Instruction::Constant(tt.insert_constant(ConstantEnum::Integer(60))),
                ),
                // exit code
                (
                    uptr_t,
                    Instruction::Constant(tt.insert_constant(ConstantEnum::Integer(0))),
                ),
                // syscall
                (
                    uptr_t,
                    Instruction::Syscall {
                        nr: 5,
                        args: Box::new([6]),
                    },
                ),
            ]),
            next: None,
        }]),
    });
    ir.function_map
        .write()
        .unwrap()
        .insert((Module::MAIN, "_start".into()), function);

    llvm::export(
        &tt,
        &ModuleGraph::new(),
        &ir,
        "out.o".as_ref(),
        true,
        &Module::MAIN,
    );
    Command::new("ld")
        .arg("out.o")
        .arg("-o")
        .arg("out")
        .arg("-e_start")
        .status()
        .unwrap();
}
