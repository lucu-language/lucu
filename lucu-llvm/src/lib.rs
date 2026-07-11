use std::num::NonZeroU32;

use inkwell::module::Linkage;
use inkwell::types::BasicTypeEnum;
use inkwell::{AddressSpace, IntPredicate};
use lucu::ast::{self, Cast};
use lucu::mu::table::{ExpressionTable, TypeTable};
use lucu::mu::{Base, Callable, Constant, Operation};
use lucu::type_table::{IntSize, Integer};

pub struct Builder;

impl Builder {
    pub fn is_signed<'ctx>(ty: mu::Type, llvm: &mu_llvm::Context<'ctx, Self>) -> bool {
        match llvm.tt[ty] {
            mu::TypeEnum::Base(Base::Integer(i)) => {
                match i {
                    Integer::Integer(signed, _) => signed,
                    // TODO: is 'char' signed?
                    Integer::CChar => true,
                }
            }
            mu::TypeEnum::Base(Base::Boolean) => false,
            _ => panic!(),
        }
    }
}

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
                Integer::Integer(_, IntSize::Exact(n)) => NonZeroU32::new(n)
                    .map(|bits| llvm.context.custom_width_int_type(bits).unwrap().into()),
                Integer::Integer(_, IntSize::Index) => {
                    // TODO
                    Some(
                        llvm.context
                            .ptr_sized_int_type(&llvm.target_data, None)
                            .into(),
                    )
                }
                Integer::Integer(_, IntSize::Address) => Some(
                    llvm.context
                        .ptr_sized_int_type(&llvm.target_data, None)
                        .into(),
                ),
                Integer::Integer(_, IntSize::Register) => {
                    // TODO
                    // NOTE: this assumes a 64-bit system
                    Some(llvm.context.i64_type().into())
                }
                Integer::Integer(_, IntSize::CChar) | Integer::CChar => {
                    // TODO
                    Some(llvm.context.i8_type().into())
                }
                Integer::Integer(_, IntSize::CShort) => {
                    // TODO
                    Some(llvm.context.i16_type().into())
                }
                Integer::Integer(_, IntSize::CInt) => {
                    // TODO
                    Some(llvm.context.i32_type().into())
                }
                Integer::Integer(_, IntSize::CLong) => {
                    // TODO
                    // NOTE: on windows this is i32
                    Some(llvm.context.i64_type().into())
                }
                Integer::Integer(_, IntSize::CLongLong) => {
                    // TODO
                    Some(llvm.context.i64_type().into())
                }
            },
            Base::CString => Some(llvm.context.ptr_type(AddressSpace::default()).into()),
        })
    }

    fn build_operation<'ctx>(
        op: &Operation,
        llvm: &mu_llvm::Context<'ctx, Self>,
    ) -> mu_llvm::Value<'ctx, Self> {
        match op {
            Operation::Unreachable => {
                let _ = llvm.builder.build_unreachable().unwrap();
                mu_llvm::Value::Data(None)
            }
            Operation::Constant(ty, constant) => {
                mu_llvm::Value::Data(llvm.get_type(*ty).basic_type(llvm).map(
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
        params: impl IntoIterator<Item = mu_llvm::ValueOrExpression<'ctx, Self>>,
        llvm: &mu_llvm::Context<'ctx, Self>,
    ) -> mu_llvm::Value<'ctx, Self> {
        let mut params = params.into_iter();
        match *op {
            Callable::Cast { to, op, .. } => {
                let param = params.next().unwrap().build(llvm).basic_value(llvm);
                let ty = llvm.get_type(to).basic_type(llvm);
                mu_llvm::Value::Data(ty.map(|llvm_ty| {
                    match op {
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
                            Some(val) => if Self::is_signed(to, llvm) {
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
                            .into(),
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
                    }
                }))
            }
            Callable::UnOp { op, .. } => {
                let param = params.next().unwrap().build(llvm).basic_value(llvm);
                mu_llvm::Value::Data(param.map(|v| {
                    match op {
                        ast::UnOp::Negate => {
                            // TODO: non-int values
                            llvm.builder
                                .build_int_neg(v.into_int_value(), "")
                                .unwrap()
                                .into()
                        }
                        ast::UnOp::Plus => v,
                    }
                }))
            }
            Callable::PredicateOp { ty, op } => {
                let lhs = params.next().unwrap().build(llvm).basic_value(llvm);
                let rhs = params.next().unwrap().build(llvm).basic_value(llvm);
                let zip = lhs.zip(rhs);
                zip.map(|(vl, vr)| {
                    // TODO: non-int values
                    let il = vl.into_int_value();
                    let ir = vr.into_int_value();
                    let predicate = match op {
                        ast::PredicateOp::Equality(op) => match op {
                            ast::EqualityOp::Equals => IntPredicate::EQ,
                            ast::EqualityOp::NotEquals => IntPredicate::NE,
                        },
                        ast::PredicateOp::Inequality(op) => match (op, Self::is_signed(ty, llvm)) {
                            (ast::InequalityOp::Greater, true) => IntPredicate::SGT,
                            (ast::InequalityOp::Greater, false) => IntPredicate::UGT,
                            (ast::InequalityOp::GreaterEquals, true) => IntPredicate::SGE,
                            (ast::InequalityOp::GreaterEquals, false) => IntPredicate::UGE,
                            (ast::InequalityOp::Less, true) => IntPredicate::SLT,
                            (ast::InequalityOp::Less, false) => IntPredicate::ULT,
                            (ast::InequalityOp::LessEquals, true) => IntPredicate::SLE,
                            (ast::InequalityOp::LessEquals, false) => IntPredicate::ULE,
                        },
                    };
                    llvm.builder
                        .build_int_compare(predicate, il, ir, "")
                        .unwrap()
                })
                .unwrap_or_else(|| {
                    // unit equals itself
                    llvm.context
                        .bool_type()
                        .const_int(op.equals() as u64, false)
                })
                .into()
            }
            Callable::MathOp { ty, op } => {
                let lhs = params.next().unwrap().build(llvm).basic_value(llvm);
                let rhs = params.next().unwrap().build(llvm).basic_value(llvm);
                let zip = lhs.zip(rhs);
                mu_llvm::Value::Data(zip.map(|(vl, vr)| {
                    // TODO: non-int values
                    let il = vl.into_int_value();
                    let ir = vr.into_int_value();
                    match op {
                        ast::MathOp::Add => llvm.builder.build_int_add(il, ir, ""),
                        ast::MathOp::Sub => llvm.builder.build_int_sub(il, ir, ""),
                        ast::MathOp::Div => {
                            if Self::is_signed(ty, llvm) {
                                llvm.builder.build_int_signed_div(il, ir, "")
                            } else {
                                llvm.builder.build_int_unsigned_div(il, ir, "")
                            }
                        }
                        ast::MathOp::Mul => llvm.builder.build_int_mul(il, ir, ""),
                        ast::MathOp::Mod => {
                            if Self::is_signed(ty, llvm) {
                                // NOTE: this is NOT the euclidian remainder
                                // we take the more "programmer"-y one because that satisfies:
                                // (quotient * rhs) + remainder == lhs
                                llvm.builder.build_int_signed_rem(il, ir, "")
                            } else {
                                llvm.builder.build_int_unsigned_rem(il, ir, "")
                            }
                        }
                    }
                    .unwrap()
                    .into()
                }))
            }
            Callable::If => {
                let types = op_ty.from();
                let branch_sig = llvm.tt[types][1].into_function(llvm.tt);

                let bool = params.next().unwrap().build(llvm).basic_value(llvm);
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
                branch.build_call(branch_sig, [mu_llvm::Value::Data(None).into()], llvm);
                llvm.builder.build_unconditional_branch(next_block).unwrap();
                llvm.builder.position_at_end(next_block);
                mu_llvm::Value::Data(None)
            }
            Callable::IfElse { to } => {
                let types = op_ty.from();
                let branch_sig = llvm.tt[types][1].into_function(llvm.tt);

                let bool = params.next().unwrap().build(llvm).basic_value(llvm);
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
                    branch_true.build_call(branch_sig, [mu_llvm::Value::Data(None).into()], llvm);
                llvm.builder.build_unconditional_branch(next_block).unwrap();
                llvm.builder.position_at_end(else_block);
                let val_false =
                    branch_false.build_call(branch_sig, [mu_llvm::Value::Data(None).into()], llvm);
                llvm.builder.build_unconditional_branch(next_block).unwrap();
                llvm.builder.position_at_end(next_block);
                mu_llvm::Value::Data(llvm.get_type(to).basic_type(llvm).map(|ty| {
                    let val_true = val_true.basic_value(llvm).unwrap();
                    let val_false = val_false.basic_value(llvm).unwrap();
                    let phi = llvm.builder.build_phi(ty, "").unwrap();
                    phi.add_incoming(&[(&val_true, then_block), (&val_false, else_block)]);
                    phi.as_basic_value()
                }))
            }
            Callable::Syscall { .. } => {
                let nr = params
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                let args = params
                    .map(|arg| arg.build(llvm).basic_value(llvm).unwrap().into_int_value())
                    .collect::<Box<_>>();
                mu_llvm::Value::Data(Some(llvm.build_syscall(nr, args)))
            }
        }
    }
}
