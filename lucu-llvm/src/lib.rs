use std::num::NonZeroU32;

use inkwell::AddressSpace;
use inkwell::module::Linkage;
use inkwell::types::BasicTypeEnum;
use lucu::ast::Cast;
use lucu::mu::table::{ExpressionTable, TypeTable};
use lucu::mu::{Base, Callable, Constant, Operation};
use lucu::type_table::{IntSize, Integer};

pub struct Builder;

impl mu_llvm::Builder for Builder {
    type Base = Base;
    type TT = TypeTable;
    type ET = ExpressionTable;
    type Callable = Callable;

    fn get_base_type<'ctx>(
        base: &Base,
        llvm: &mu_llvm::Context<'ctx, Self>,
    ) -> mu_llvm::Type<'ctx> {
        mu_llvm::Type::Data(match base {
            Base::Boolean => Some(llvm.context.bool_type().into()),
            Base::Integer(integer) => match *integer {
                Integer::Integer(_, int_size) => match int_size {
                    IntSize::Exact(n) => NonZeroU32::new(n)
                        .map(|bits| llvm.context.custom_width_int_type(bits).unwrap().into()),
                    IntSize::Index => {
                        // TODO
                        Some(
                            llvm.context
                                .ptr_sized_int_type(&llvm.target_data, None)
                                .into(),
                        )
                    }
                    IntSize::Address => Some(
                        llvm.context
                            .ptr_sized_int_type(&llvm.target_data, None)
                            .into(),
                    ),
                    IntSize::Register => {
                        // TODO
                        Some(llvm.context.i64_type().into())
                    }
                    IntSize::CChar => todo!(),
                    IntSize::CShort => todo!(),
                    IntSize::CInt => todo!(),
                    IntSize::CLong => todo!(),
                    IntSize::CLongLong => todo!(),
                },
                Integer::CChar => todo!(),
            },
            Base::CString => Some(llvm.context.ptr_type(AddressSpace::default()).into()),
        })
    }

    fn build_operation<'ctx>(
        op: &Operation,
        llvm: &mu_llvm::Context<'ctx, Self>,
    ) -> mu_llvm::Value<'ctx, Callable> {
        match op {
            Operation::Unreachable => {
                let _ = llvm.builder.build_unreachable().unwrap();
                mu_llvm::Value::Data(None)
            }
            Operation::Constant(ty, constant) => {
                mu_llvm::Value::Data(llvm.get_type(*ty).get_data_type(llvm).map(
                    |ty| match *constant {
                        Constant::Integer(i) => ty.into_int_type().const_int(i, false).into(),
                        Constant::Zero => ty.const_zero(),
                        Constant::Uninit => match ty {
                            BasicTypeEnum::ArrayType(array_type) => array_type.get_undef().into(),
                            BasicTypeEnum::FloatType(float_type) => float_type.get_undef().into(),
                            BasicTypeEnum::IntType(int_type) => int_type.get_undef().into(),
                            BasicTypeEnum::PointerType(pointer_type) => {
                                pointer_type.get_undef().into()
                            }
                            BasicTypeEnum::StructType(struct_type) => {
                                struct_type.get_undef().into()
                            }
                            BasicTypeEnum::VectorType(vector_type) => {
                                vector_type.get_undef().into()
                            }
                            BasicTypeEnum::ScalableVectorType(scalable_vector_type) => {
                                scalable_vector_type.get_undef().into()
                            }
                        },
                        Constant::String(ref value) => {
                            let const_str = llvm.context.const_string(value.as_bytes(), true);
                            let global_str = llvm.module.add_global(const_str.get_type(), None, "");
                            global_str.set_linkage(Linkage::Internal);
                            global_str.set_constant(true);
                            global_str.set_initializer(&const_str);
                            global_str.as_pointer_value().into()
                        }
                    },
                ))
            }
            Operation::Callable(callable) => mu_llvm::Value::Callable(callable.clone()),
        }
    }

    fn build_callable<'ctx>(
        op: &Callable,
        op_ty: mu::Function,
        params: impl IntoIterator<Item = mu_llvm::Value<'ctx, Callable>>,
        llvm: &mu_llvm::Context<'ctx, Self>,
    ) -> mu_llvm::Value<'ctx, Callable> {
        let mut params = params.into_iter();
        match *op {
            Callable::Cast { to, op, .. } => {
                let param = params.next().unwrap().build(llvm);
                let ty = llvm.get_type(to).get_data_type(llvm);
                mu_llvm::Value::Data(ty.map(|llvm_ty| match op {
                    Cast::Truncate => {
                        let val = param.unwrap();
                        llvm.builder
                            .build_int_truncate_or_bit_cast(
                                val.into_int_value(),
                                llvm_ty.into_int_type(),
                                "",
                            )
                            .unwrap()
                            .into()
                    }
                    Cast::Extend => match param {
                        Some(val) => {
                            let mu::TypeEnum::Base(Base::Integer(i)) = llvm.tt[to] else {
                                panic!()
                            };
                            // TODO: is 'char' signed
                            if i.is_signed(true) {
                                llvm.builder.build_int_s_extend_or_bit_cast(
                                    val.into_int_value(),
                                    llvm_ty.into_int_type(),
                                    "",
                                )
                            } else {
                                llvm.builder.build_int_z_extend_or_bit_cast(
                                    val.into_int_value(),
                                    llvm_ty.into_int_type(),
                                    "",
                                )
                            }
                            .unwrap()
                            .into()
                        }
                        None => llvm_ty.const_zero(),
                    },
                    Cast::Transmute => {
                        // NOTE: do we want to do ptrtoint here?
                        // maybe we should not allow transmuting from integers back to pointers
                        let val = param.unwrap();
                        if val.is_pointer_value() && llvm_ty.is_int_type() {
                            llvm.builder
                                .build_ptr_to_int(
                                    val.into_pointer_value(),
                                    llvm_ty.into_int_type(),
                                    "",
                                )
                                .unwrap()
                                .into()
                        } else if val.is_int_value() && llvm_ty.is_pointer_type() {
                            llvm.builder
                                .build_int_to_ptr(
                                    val.into_int_value(),
                                    llvm_ty.into_pointer_type(),
                                    "",
                                )
                                .unwrap()
                                .into()
                        } else {
                            llvm.builder.build_bit_cast(val, llvm_ty, "").unwrap()
                        }
                    }
                }))
            }
            Callable::UnOp { ty, op } => todo!(),
            Callable::BinOp { ty, op } => todo!(),
            Callable::If => {
                let types = op_ty.from();
                let branch_sig = llvm.tt[types][1].into_function(llvm.tt);

                let bool = params.next().unwrap().build(llvm);
                let branch = params.next().unwrap();

                let then_block = llvm.build_block("");
                let next_block = llvm.build_block("");
                llvm.builder
                    .build_conditional_branch(
                        bool.unwrap().into_int_value(),
                        then_block,
                        next_block,
                    )
                    .unwrap();
                llvm.builder.position_at_end(then_block);
                llvm.build_call(branch_sig, branch, [mu_llvm::Value::Data(None)]);
                llvm.builder.build_unconditional_branch(next_block).unwrap();
                llvm.builder.position_at_end(next_block);
                mu_llvm::Value::Data(None)
            }
            Callable::IfElse { to } => {
                let types = op_ty.from();
                let branch_sig = llvm.tt[types][1].into_function(llvm.tt);

                let bool = params.next().unwrap().build(llvm);
                let branch_true = params.next().unwrap();
                let branch_false = params.next().unwrap();

                let then_block = llvm.build_block("");
                let else_block = llvm.build_block("");
                let next_block = llvm.build_block("");
                llvm.builder
                    .build_conditional_branch(
                        bool.unwrap().into_int_value(),
                        then_block,
                        else_block,
                    )
                    .unwrap();
                llvm.builder.position_at_end(then_block);
                let val_true =
                    llvm.build_call(branch_sig, branch_true, [mu_llvm::Value::Data(None)]);
                llvm.builder.build_unconditional_branch(next_block).unwrap();
                llvm.builder.position_at_end(else_block);
                let val_false =
                    llvm.build_call(branch_sig, branch_false, [mu_llvm::Value::Data(None)]);
                llvm.builder.build_unconditional_branch(next_block).unwrap();
                llvm.builder.position_at_end(next_block);
                mu_llvm::Value::Data(llvm.get_type(to).get_data_type(llvm).map(|ty| {
                    let val_true = val_true.build(llvm).unwrap();
                    let val_false = val_false.build(llvm).unwrap();
                    let phi = llvm.builder.build_phi(ty, "").unwrap();
                    phi.add_incoming(&[(&val_true, then_block), (&val_false, else_block)]);
                    phi.as_basic_value()
                }))
            }
            Callable::Syscall { .. } => {
                let nr = params.next().unwrap().build(llvm).unwrap().into_int_value();
                let args = params
                    .map(|arg| arg.build(llvm).unwrap().into_int_value())
                    .collect::<Box<_>>();
                mu_llvm::Value::Data(Some(llvm.build_syscall(nr, args)))
            }
        }
    }
}
