use std::collections::HashMap;
use std::num::NonZeroU32;
use std::sync::OnceLock;

use inkwell::module::Linkage;
use inkwell::targets::TargetMachine;
use inkwell::types::{BasicMetadataTypeEnum, BasicType as _, BasicTypeEnum};
use inkwell::values::{BasicMetadataValueEnum, FunctionValue};
use inkwell::{AddressSpace, IntPredicate};
use lucu::ast::{self, Cast};
use lucu::mu::table::Table;
use lucu::mu::{Base, Callable, Constant, Function, Item, Operation};
use lucu::type_table::{IntSize, Integer};
use mu::Table as _;

pub struct Builder<'ctx> {
    functions: OnceLock<HashMap<Item, FunctionValue<'ctx>>>,
}

impl<'ctx> Builder<'ctx> {
    pub fn build(
        context: &'ctx inkwell::context::Context,
        table: &'ctx Table,
        target_machine: TargetMachine,
        module_name: &str,
        funs: &[Function],
    ) -> mu_llvm::Context<'ctx, Self> {
        let llvm = mu_llvm::Context::new(
            context,
            table,
            Builder {
                functions: OnceLock::new(),
            },
            target_machine,
            module_name,
        );

        let mut map = HashMap::new();
        for fun in funs.iter() {
            let fval = llvm.add_function(
                fun.ty,
                false,
                None,
                Some(
                    fun.linkage
                        .map(|l| match l {
                            lucu::mu::Linkage::Internal => Linkage::Private,
                            lucu::mu::Linkage::External => Linkage::External,
                        })
                        .unwrap_or(Linkage::Private),
                ),
            );
            map.insert(fun.item.clone(), fval);
        }
        let Ok(_) = llvm.base.functions.set(map) else {
            panic!()
        };
        for fun in funs.iter() {
            let fval = llvm.base.functions.get().unwrap()[&fun.item];
            llvm.build_function(fun.ty, fval, fun.body);
        }

        llvm
    }
    pub fn is_signed(ty: mu::Type, llvm: &mu_llvm::Context<'ctx, Self>) -> bool {
        match llvm.table[ty] {
            mu::TypeEnum::Base(Base::Integer(i)) => {
                match i {
                    Integer::Integer(signed, _) => signed,
                    // TODO: is 'char' signed?
                    Integer::CChar => true,
                }
            }
            _ => false,
        }
    }
}

impl<'ctx> mu_llvm::Builder<'ctx> for Builder<'ctx> {
    type Base = Base;
    type Table = Table;
    type Callable = Callable;

    fn has_zero_niche(base: &Base, llvm: &mu_llvm::Context<'ctx, Self>) -> bool {
        match *base {
            Base::Integer(_) => false,
            Base::Pointer(_) | Base::MultiPointer(_) | Base::PointerSlice(_) => true,
            Base::Array(ty, n) => n > 0 && llvm.has_zero_niche(ty),
        }
    }

    fn get_type(base: &Base, llvm: &mu_llvm::Context<'ctx, Self>) -> mu_llvm::Type<'ctx> {
        mu_llvm::Type::Data(match *base {
            Base::Integer(integer) => match integer {
                Integer::Integer(_, IntSize::Exact(n)) => NonZeroU32::new(n)
                    .map(|bits| llvm.context.custom_width_int_type(bits).unwrap().into()),
                Integer::Integer(_, IntSize::Size) => {
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
            Base::Pointer(inner) | Base::MultiPointer(inner) => llvm
                .get_type(inner)
                .nonzero_sized()
                .then(|| llvm.context.ptr_type(AddressSpace::default()).into()),
            Base::PointerSlice(inner) => {
                llvm.get_type(llvm.table.insert_type(mu::TypeEnum::Product(
                    llvm.table.insert_tuple([
                        llvm.table.base(Base::Pointer(inner)),
                        llvm.table.base(Base::SIZE),
                    ]),
                )))
                .basic_type(llvm)
            }
            Base::Array(inner, size) => {
                if size == 0 {
                    None
                } else {
                    llvm.get_type(inner)
                        .basic_type(llvm)
                        .map(|ty| ty.array_type(size).into())
                }
            }
        })
    }

    fn build_operation(
        op: &Operation,
        llvm: &mu_llvm::Context<'ctx, Self>,
    ) -> mu_llvm::Value<'ctx, Self> {
        match op {
            Operation::Unreachable => mu_llvm::Value::Data(None),
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
                            // TODO: support UTF-16, UTF-32
                            let const_str = llvm.context.const_string(value.as_bytes(), false);
                            let global_str = llvm.module.add_global(const_str.get_type(), None, "");
                            global_str.set_linkage(Linkage::Internal);
                            global_str.set_constant(true);
                            global_str.set_initializer(&const_str);
                            match ty {
                                // pointer
                                BasicTypeEnum::PointerType(_) => {
                                    global_str.as_pointer_value().into()
                                }
                                // slice
                                BasicTypeEnum::StructType(ty) => {
                                    let mut out = ty.get_poison();
                                    out = llvm
                                        .builder
                                        .build_insert_value(
                                            out,
                                            global_str.as_pointer_value(),
                                            0,
                                            "",
                                        )
                                        .unwrap()
                                        .into_struct_value();
                                    out = llvm
                                        .builder
                                        .build_insert_value(
                                            out,
                                            ty.get_field_type_at_index(1)
                                                .unwrap()
                                                .into_int_type()
                                                .const_int(value.len() as u64, false),
                                            1,
                                            "",
                                        )
                                        .unwrap()
                                        .into_struct_value();
                                    out.into()
                                }
                                _ => panic!(),
                            }
                        }
                    },
                ))
            }
            Operation::Callable(callable) => mu_llvm::Value::Callable(callable.clone()),
        }
    }

    fn build_callable(
        op: &Callable,
        _op_ty: mu::FunctionType,
        args: impl IntoIterator<Item = mu_llvm::ValueOrExpression<'ctx, Self>>,
        llvm: &mu_llvm::Context<'ctx, Self>,
    ) -> mu_llvm::Value<'ctx, Self> {
        let mut args = args.into_iter();
        match *op {
            Callable::ModuleFunction { ref item, .. } => {
                let fun = llvm.base.functions.get().unwrap()[item];
                llvm.build_direct_call(fun, args.map(|v| v.build(llvm)))
            }
            Callable::ArrayConstruct { ty, size } => match llvm.get_type(ty).basic_type(llvm) {
                Some(ty) => {
                    let mut array = ty.array_type(size).get_poison();
                    for (index, param) in args.enumerate() {
                        array = llvm
                            .builder
                            .build_insert_value(
                                array,
                                param.build(llvm).basic_value(llvm).unwrap(),
                                index as u32,
                                "",
                            )
                            .unwrap()
                            .into_array_value();
                    }
                    mu_llvm::Value::Data(Some(array.into()))
                }
                None => {
                    args.map(|v| v.build(llvm)).for_each(drop);
                    mu_llvm::Value::Data(None)
                }
            },
            Callable::Asm {
                ref assembly,
                ref constraints,
                side_effects,
                from,
                to,
            } => {
                let from = llvm.get_type(from).basic_type(llvm).unwrap();
                let (params, args) = if from.is_array_type() {
                    let from = from.into_array_type();
                    let params = std::iter::repeat_n(
                        BasicMetadataTypeEnum::from(from.get_element_type()),
                        from.len() as usize,
                    )
                    .collect::<Box<_>>();
                    let arg_array = args
                        .next()
                        .unwrap()
                        .build(llvm)
                        .basic_value(llvm)
                        .unwrap()
                        .into_array_value();
                    let args = (0..from.len())
                        .map(|n| {
                            BasicMetadataValueEnum::from(
                                llvm.builder.build_extract_value(arg_array, n, "").unwrap(),
                            )
                        })
                        .collect::<Box<_>>();
                    (params, args)
                } else {
                    // TODO: support more types
                    (
                        vec![from.into()].into_boxed_slice(),
                        vec![
                            args.next()
                                .unwrap()
                                .build(llvm)
                                .basic_value(llvm)
                                .unwrap()
                                .into(),
                        ]
                        .into_boxed_slice(),
                    )
                };

                let to = llvm.get_type(to).basic_type(llvm);
                let ty = match to {
                    Some(to) => to.fn_type(&params, false),
                    None => llvm.context.void_type().fn_type(&params, false),
                };
                let asm = llvm.context.create_inline_asm(
                    ty,
                    assembly.as_str().into(),
                    constraints.as_str().into(),
                    side_effects,
                    false,
                    None,
                    false,
                );
                mu_llvm::Value::Data(
                    llvm.builder
                        .build_indirect_call(ty, asm, &args, "")
                        .unwrap()
                        .try_as_basic_value()
                        .basic(),
                )
            }
            Callable::Loop => {
                let block = llvm.build_block("");
                llvm.builder.build_unconditional_branch(block).unwrap();
                llvm.builder.position_at_end(block);
                args.next().unwrap().build_call(
                    mu::FunctionType::new(
                        llvm.table.insert_tuple([]),
                        llvm.table.unit(),
                        llvm.table,
                    ),
                    [],
                    llvm,
                );
                llvm.builder.build_unconditional_branch(block).unwrap();

                let next = llvm.build_block("");
                llvm.builder.position_at_end(next);
                mu_llvm::Value::Data(None)
            }
            Callable::Cast { to, op, .. } => {
                let param = args.next().unwrap().build(llvm).basic_value(llvm);
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
                let param = args.next().unwrap().build(llvm).basic_value(llvm);
                mu_llvm::Value::Data(param.map(|v| {
                    match op {
                        ast::UnOp::Negate => {
                            // TODO: non-int values
                            llvm.builder
                                .build_int_neg(v.into_int_value(), "")
                                .unwrap()
                                .into()
                        }
                        ast::UnOp::Complement | ast::UnOp::Not => llvm
                            .builder
                            .build_not(v.into_int_value(), "")
                            .unwrap()
                            .into(),
                        ast::UnOp::Plus => v,
                    }
                }))
            }
            Callable::PredicateOp { ty, op } => {
                let lhs = args.next().unwrap().build(llvm).basic_value(llvm);
                let rhs = args.next().unwrap().build(llvm).basic_value(llvm);
                let zip = lhs.zip(rhs);
                zip.map(|(vl, vr)| {
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
                    if vl.is_int_value() {
                        llvm.builder
                            .build_int_compare(
                                predicate,
                                vl.into_int_value(),
                                vr.into_int_value(),
                                "",
                            )
                            .unwrap()
                    } else if vl.is_pointer_value() {
                        llvm.builder
                            .build_int_compare(
                                predicate,
                                vl.into_pointer_value(),
                                vr.into_pointer_value(),
                                "",
                            )
                            .unwrap()
                    } else {
                        todo!()
                    }
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
                let lhs = args.next().unwrap().build(llvm).basic_value(llvm);
                let rhs = args.next().unwrap().build(llvm).basic_value(llvm);
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
                        ast::MathOp::And => llvm.builder.build_and(il, ir, ""),
                        ast::MathOp::Or => llvm.builder.build_or(il, ir, ""),
                        ast::MathOp::Xor => llvm.builder.build_xor(il, ir, ""),
                        ast::MathOp::ShiftLeft => llvm.builder.build_left_shift(il, ir, ""),
                        ast::MathOp::ShiftRight => {
                            llvm.builder
                                .build_right_shift(il, ir, Self::is_signed(ty, llvm), "")
                        }
                        ast::MathOp::AndNot => {
                            let not = llvm.builder.build_not(ir, "").unwrap();
                            llvm.builder.build_and(il, not, "")
                        }
                    }
                    .unwrap()
                    .into()
                }))
            }
            Callable::Syscall { .. } => {
                let nr = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                let args = args
                    .map(|arg| arg.build(llvm).basic_value(llvm).unwrap().into_int_value())
                    .collect::<Box<_>>();
                mu_llvm::Value::Data(Some(llvm.build_syscall(nr, args)))
            }
            Callable::LetReference { ty, to } => {
                let val = args.next().unwrap().build(llvm).basic_value(llvm);
                let ptr = val.map(|val| {
                    let alloc = llvm.builder.build_alloca(val.get_type(), "").unwrap();
                    let _ = llvm.builder.build_store(alloc, val).unwrap();
                    alloc.into()
                });

                let fun = mu::FunctionType::new(
                    llvm.table
                        .insert_tuple([llvm.table.base(Base::Pointer(ty))]),
                    to,
                    llvm.table,
                );
                let fval = args.next().unwrap();
                fval.build_call(fun, [mu_llvm::Value::Data(ptr).into()], llvm)
            }
            Callable::LetAlloca { ty, to } => {
                let size = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                let ptr = llvm
                    .get_type(ty)
                    .basic_type(llvm)
                    .map(|ty| llvm.builder.build_array_alloca(ty, size, "").unwrap());

                let ptr_slice = llvm.table.base(Base::PointerSlice(ty));
                let llvm_ptr_slice = llvm
                    .get_type(ptr_slice)
                    .basic_type(llvm)
                    .unwrap()
                    .into_struct_type();
                let count_fields = llvm_ptr_slice.count_fields();

                let mut out = llvm_ptr_slice.get_poison();
                if let Some(ptr) = ptr {
                    out = llvm
                        .builder
                        .build_insert_value(out, ptr, 0, "")
                        .unwrap()
                        .into_struct_value();
                }
                out = llvm
                    .builder
                    .build_insert_value(out, size, count_fields - 1, "")
                    .unwrap()
                    .into_struct_value();

                let fun =
                    mu::FunctionType::new(llvm.table.insert_tuple([ptr_slice]), to, llvm.table);
                let fval = args.next().unwrap();
                fval.build_call(fun, [mu_llvm::Value::Data(Some(out.into())).into()], llvm)
            }
            Callable::Read { ty } => {
                let val = args.next().unwrap().build(llvm).basic_value(llvm);
                mu_llvm::Value::Data(val.map(|val| {
                    let llvm_ty = llvm.get_type(ty).basic_type(llvm).unwrap();
                    llvm.builder
                        .build_load(llvm_ty, val.into_pointer_value(), "")
                        .unwrap()
                }))
            }
            Callable::Write { .. } => {
                let ptr = args.next().unwrap().build(llvm).basic_value(llvm);
                let val = args.next().unwrap().build(llvm).basic_value(llvm);
                if let Some((ptr, val)) = ptr.zip(val) {
                    llvm.builder
                        .build_store(ptr.into_pointer_value(), val)
                        .unwrap();
                }
                mu_llvm::Value::Data(None)
            }
            Callable::PointerMember { tys, member } => {
                let val = args.next().unwrap().build(llvm);
                llvm.build_member_pointer(tys, member, val)
            }
            Callable::MultiPointerIndex { ty }
            | Callable::PointerArrayIndex { ty, .. }
            | Callable::MultiPointerOffset { ty } => {
                // TODO: do a bounds check
                let val = args.next().unwrap().build(llvm).basic_value(llvm);
                let index = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                mu_llvm::Value::Data(val.map(|val| {
                    let llvm_ty = llvm.get_type(ty).basic_type(llvm).unwrap();
                    unsafe {
                        llvm.builder
                            .build_gep(llvm_ty, val.into_pointer_value(), &[index], "")
                    }
                    .unwrap()
                    .into()
                }))
            }
            Callable::PointerSliceIndex { ty } => {
                // TODO: do a bounds check
                let val = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_struct_value();
                let index = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                mu_llvm::Value::Data((val.get_type().count_fields() == 2).then(|| {
                    let llvm_ty = llvm.get_type(ty).basic_type(llvm).unwrap();
                    let ptr = llvm
                        .builder
                        .build_extract_value(val, 0, "")
                        .unwrap()
                        .into_pointer_value();
                    unsafe { llvm.builder.build_gep(llvm_ty, ptr, &[index], "") }
                        .unwrap()
                        .into()
                }))
            }
            Callable::ArrayIndex { ty, size } => {
                // TODO: do a bounds check
                let val = args.next().unwrap().build(llvm).basic_value(llvm);
                let index = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                mu_llvm::Value::Data(val.map(|val| {
                    // there is no dynamic array index in llvm,
                    // so we gotta do an alloca
                    let llvm_ty = llvm.get_type(ty).basic_type(llvm).unwrap();
                    let ptr = llvm
                        .builder
                        .build_alloca(llvm_ty.array_type(size), "")
                        .unwrap();
                    let _ = llvm.builder.build_store(ptr, val).unwrap();
                    let offset =
                        unsafe { llvm.builder.build_gep(llvm_ty, ptr, &[index], "") }.unwrap();
                    llvm.builder.build_load(llvm_ty, offset, "").unwrap()
                }))
            }
            Callable::PointerSliceSlice { ty } => {
                // TODO: do a bounds check
                let val = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_struct_value();
                let from = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                let to = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();

                let count_fields = val.get_type().count_fields();
                let ptr = (count_fields == 2).then(|| {
                    let llvm_ty = llvm.get_type(ty).basic_type(llvm).unwrap();
                    let ptr = llvm
                        .builder
                        .build_extract_value(val, 0, "")
                        .unwrap()
                        .into_pointer_value();
                    unsafe { llvm.builder.build_gep(llvm_ty, ptr, &[from], "") }.unwrap()
                });
                let len = llvm.builder.build_int_sub(to, from, "").unwrap();

                let mut out = val.get_type().get_poison();
                if let Some(ptr) = ptr {
                    out = llvm
                        .builder
                        .build_insert_value(out, ptr, 0, "")
                        .unwrap()
                        .into_struct_value();
                }
                out = llvm
                    .builder
                    .build_insert_value(out, len, count_fields - 1, "")
                    .unwrap()
                    .into_struct_value();
                mu_llvm::Value::Data(Some(out.into()))
            }
            Callable::PointerArraySlice { ty, .. } | Callable::MultiPointerSlice { ty } => {
                // TODO: do a bounds check
                let val = args.next().unwrap().build(llvm).basic_value(llvm);
                let from = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();
                let to = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_int_value();

                let len = llvm.builder.build_int_sub(to, from, "").unwrap();

                let mut out = llvm
                    .get_type(llvm.table.base(Base::PointerSlice(ty)))
                    .basic_type(llvm)
                    .unwrap()
                    .into_struct_type()
                    .get_poison();
                if let Some(ptr) = val {
                    let llvm_ty = llvm.get_type(ty).basic_type(llvm).unwrap();
                    let ptr = unsafe {
                        llvm.builder
                            .build_gep(llvm_ty, ptr.into_pointer_value(), &[from], "")
                    }
                    .unwrap();
                    out = llvm
                        .builder
                        .build_insert_value(out, ptr, 0, "")
                        .unwrap()
                        .into_struct_value();
                }
                out = llvm
                    .builder
                    .build_insert_value(out, len, val.map(|_| 1).unwrap_or(0), "")
                    .unwrap()
                    .into_struct_value();
                mu_llvm::Value::Data(Some(out.into()))
            }
            Callable::Len { .. } => {
                let val = args
                    .next()
                    .unwrap()
                    .build(llvm)
                    .basic_value(llvm)
                    .unwrap()
                    .into_struct_value();
                llvm.builder
                    .build_extract_value(val, val.get_type().count_fields() - 1, "")
                    .unwrap()
                    .into()
            }
        }
    }
}
