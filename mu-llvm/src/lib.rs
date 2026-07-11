use std::collections::HashMap;
use std::hash::Hash;
use std::iter;
use std::ops::Deref;
use std::path::Path;
use std::sync::RwLock;

use inkwell::attributes::AttributeLoc;
use inkwell::basic_block::BasicBlock;
use inkwell::module::Linkage;
use inkwell::passes::PassBuilderOptions;
use inkwell::support::LLVMString;
use inkwell::targets::{FileType, TargetData, TargetMachine};
use inkwell::types::{
    BasicMetadataTypeEnum, BasicType as _, BasicTypeEnum, FunctionType, IntType, StructType,
};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValueEnum, FunctionValue, IntValue, PhiValue, PointerValue,
};
use inkwell::{AddressSpace, IntPredicate};
use mu::{TypeTable as _, Typed as _};

pub trait Builder
where
    <Self::TT as mu::TypeTable>::Name: Deref<Target = str>,
{
    type Base;
    type TT: mu::TypeTable<Base = Self::Base> + ?Sized;
    type ET: mu::ExpressionTable<Base = Self::Base> + ?Sized;
    type Callable: mu::Typed<Base = Self::Base> + Clone + Hash + Eq;

    fn has_zero_niche<'ctx>(
        base: &<Self::TT as mu::TypeTable>::Base,
        llvm: &Context<'ctx, Self>,
    ) -> bool;
    fn get_type<'ctx>(
        base: &<Self::TT as mu::TypeTable>::Base,
        llvm: &Context<'ctx, Self>,
    ) -> Type<'ctx>;
    fn build_operation<'ctx>(
        op: &<Self::ET as mu::ExpressionTable>::Operation,
        llvm: &Context<'ctx, Self>,
    ) -> Value<'ctx, Self>;
    fn build_callable<'ctx>(
        op: &Self::Callable,
        op_ty: mu::Function,
        params: impl IntoIterator<Item = ValueOrExpression<'ctx, Self>>,
        llvm: &Context<'ctx, Self>,
    ) -> Value<'ctx, Self>;
}

pub type BasicValue<'ctx> = Option<BasicValueEnum<'ctx>>;

pub type BasicType<'ctx> = Option<BasicTypeEnum<'ctx>>;

#[derive(Clone, Copy)]
pub enum Type<'ctx> {
    Data(BasicType<'ctx>),
    Function(FunctionType<'ctx>),
}

impl<'ctx, T: inkwell::types::BasicType<'ctx>> From<T> for Type<'ctx> {
    fn from(value: T) -> Self {
        Self::Data(Some(value.as_basic_type_enum()))
    }
}

impl<'ctx> Type<'ctx> {
    pub fn nonzero_sized(self) -> bool {
        match self {
            Type::Data(data_type) => data_type.is_some(),
            Type::Function(_) => true,
        }
    }
    pub fn basic_type<B: Builder + ?Sized>(self, llvm: &Context<'ctx, B>) -> BasicType<'ctx> {
        match self {
            Type::Data(data_type) => data_type,
            Type::Function(_) => Some(
                llvm.context
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .into(),
            ),
        }
    }
}

pub enum Value<'ctx, B: Builder + ?Sized> {
    Data(BasicValue<'ctx>),
    Function(FunctionValue<'ctx>, Option<PointerValue<'ctx>>),
    Callable(B::Callable),
}

impl<B: Builder + ?Sized> Clone for Value<'_, B> {
    fn clone(&self) -> Self {
        match *self {
            Self::Data(arg0) => Self::Data(arg0),
            Self::Function(arg0, arg1) => Self::Function(arg0, arg1),
            Self::Callable(ref arg0) => Self::Callable(arg0.clone()),
        }
    }
}

impl<'ctx, B: Builder + ?Sized, T: inkwell::values::BasicValue<'ctx>> From<T> for Value<'ctx, B> {
    fn from(value: T) -> Self {
        Self::Data(Some(value.as_basic_value_enum()))
    }
}

impl<'ctx, B: Builder + ?Sized> Value<'ctx, B> {
    pub fn basic_value(self, llvm: &Context<'ctx, B>) -> BasicValue<'ctx> {
        match self {
            Value::Data(data) => data,
            Value::Function(function, closure) => llvm.build_closure(function, closure),
            Value::Callable(c) => {
                // we create a small function that is just this operation cuz we need it as a closure
                let function = match llvm.callables.read().unwrap().get(&c).copied() {
                    Some(function) => function,
                    None => {
                        let current_block = llvm.builder.get_insert_block().unwrap();
                        let current_fun = {
                            let guard = llvm.function.read().unwrap();
                            guard.unwrap()
                        };

                        // build function
                        let fun = c.get_type(llvm.tt).into_function(llvm.tt);

                        let function_type = llvm.get_function_type(fun, true);
                        let function =
                            llvm.module
                                .add_function("", function_type, Some(Linkage::Private));
                        llvm.function_attributes(function);
                        llvm.builder
                            .position_at_end(llvm.context.append_basic_block(function, ""));
                        let params = {
                            let mut nth = 0;
                            llvm.tt[fun.from()].iter().copied().enumerate().map(
                                move |(index, t)| {
                                    ValueOrExpression::Value(Value::Data(
                                        llvm.get_type(t).nonzero_sized().then(|| {
                                            let struc = function
                                                .get_first_param()
                                                .unwrap()
                                                .into_struct_value();
                                            let val = llvm
                                                .builder
                                                .build_extract_value(
                                                    struc,
                                                    nth,
                                                    llvm.tt
                                                        .tuple_field_name(fun.from(), index as u32)
                                                        .map(Deref::deref)
                                                        .unwrap_or(""),
                                                )
                                                .unwrap();
                                            nth += 1;
                                            val
                                        }),
                                    ))
                                },
                            )
                        };
                        let out = B::build_callable(&c, fun, params, llvm).basic_value(llvm);
                        if !fun.never_returns(llvm.tt) {
                            llvm.builder
                                .build_return(
                                    out.as_ref().map(|e| e as &dyn inkwell::values::BasicValue),
                                )
                                .unwrap();
                        }

                        // return
                        llvm.builder.position_at_end(current_block);
                        *llvm.function.write().unwrap() = Some(current_fun);
                        llvm.callables.write().unwrap().insert(c.clone(), function);
                        function
                    }
                };
                llvm.build_closure(function, None)
            }
        }
    }
}

pub struct Expression<'ctx, B: Builder + ?Sized> {
    expr: mu::Expression,
    bound: im::Vector<Value<'ctx, B>>,
}

impl<'ctx, B: Builder + ?Sized> Clone for Expression<'ctx, B> {
    fn clone(&self) -> Self {
        Self {
            expr: self.expr,
            bound: self.bound.clone(),
        }
    }
}

impl<'ctx, B: Builder + ?Sized> Expression<'ctx, B> {
    pub fn build(self, llvm: &Context<'ctx, B>) -> Value<'ctx, B> {
        llvm.build_expression(self.expr, &self.bound)
    }
    pub fn build_call(
        self,
        fun: mu::Function,
        vals: impl IntoIterator<Item = ValueOrExpression<'ctx, B>>,
        llvm: &Context<'ctx, B>,
    ) -> Value<'ctx, B> {
        match llvm.et[self.expr] {
            mu::ExpressionEnum::Abstract(_, e) => {
                let value =
                    llvm.build_construct(fun.from(), vals.into_iter().map(|v| v.build(llvm)));
                let mut refs = self.bound;
                refs.push_front(value);
                llvm.build_expression(e, &refs)
            }
            _ => {
                let fval = self.build(llvm);
                llvm.build_call(fun, fval, vals)
            }
        }
    }
}

pub enum ValueOrExpression<'ctx, B: Builder + ?Sized> {
    Value(Value<'ctx, B>),
    Expression(Expression<'ctx, B>),
}

impl<'ctx, B: Builder + ?Sized> Clone for ValueOrExpression<'ctx, B> {
    fn clone(&self) -> Self {
        match self {
            Self::Value(arg0) => Self::Value(arg0.clone()),
            Self::Expression(arg0) => Self::Expression(arg0.clone()),
        }
    }
}

impl<'ctx, B: Builder + ?Sized> ValueOrExpression<'ctx, B> {
    pub fn build(self, llvm: &Context<'ctx, B>) -> Value<'ctx, B> {
        match self {
            ValueOrExpression::Value(value) => value,
            ValueOrExpression::Expression(expression) => expression.build(llvm),
        }
    }
    pub fn build_call(
        self,
        fun: mu::Function,
        vals: impl IntoIterator<Item = ValueOrExpression<'ctx, B>>,
        llvm: &Context<'ctx, B>,
    ) -> Value<'ctx, B> {
        match self {
            ValueOrExpression::Value(value) => llvm.build_call(fun, value, vals),
            ValueOrExpression::Expression(expression) => expression.build_call(fun, vals, llvm),
        }
    }
}

impl<'ctx, B: Builder + ?Sized> From<Value<'ctx, B>> for ValueOrExpression<'ctx, B> {
    fn from(value: Value<'ctx, B>) -> Self {
        Self::Value(value)
    }
}

type CallableCache<'ctx, C> = HashMap<C, FunctionValue<'ctx>>;
type EnumCache<'ctx> = HashMap<mu::Enum, (Box<[Type<'ctx>]>, Enum<'ctx>)>;
type StructCache<'ctx> = HashMap<mu::Tuple, (Box<[Type<'ctx>]>, Option<StructType<'ctx>>)>;

#[derive(Clone, Copy, Debug)]
pub enum Enum<'ctx> {
    Never,
    Units(IntType<'ctx>),
    Single(Option<BasicTypeEnum<'ctx>>),
    ZeroNiche(Option<BasicTypeEnum<'ctx>>, bool),
    TaggedUnion(StructType<'ctx>),
}

impl<'ctx> From<Enum<'ctx>> for Type<'ctx> {
    fn from(value: Enum<'ctx>) -> Self {
        Type::Data(match value {
            Enum::Never => None,
            Enum::Units(repr) => Some(repr.into()),
            Enum::Single(repr) => repr,
            Enum::ZeroNiche(repr, _) => repr,
            Enum::TaggedUnion(repr) => Some(repr.into()),
        })
    }
}

pub struct Context<'ctx, B: Builder + ?Sized> {
    pub context: &'ctx inkwell::context::Context,
    pub tt: &'ctx B::TT,
    pub et: &'ctx B::ET,
    pub base: &'ctx B,
    pub module: inkwell::module::Module<'ctx>,
    pub builder: inkwell::builder::Builder<'ctx>,
    pub target_machine: TargetMachine,
    pub target_data: TargetData,

    function: RwLock<Option<FunctionValue<'ctx>>>,
    structs: RwLock<StructCache<'ctx>>,
    enums: RwLock<EnumCache<'ctx>>,
    callables: RwLock<CallableCache<'ctx, B::Callable>>,
    // TODO: remove this from here
    syscalls: Box<[(FunctionType<'ctx>, PointerValue<'ctx>)]>,
}

impl<'ctx, B: Builder + ?Sized> Context<'ctx, B> {
    // TODO: remove this from here
    pub fn build_syscall<I>(&self, nr: IntValue<'ctx>, args: I) -> BasicValueEnum<'ctx>
    where
        I: IntoIterator<Item = IntValue<'ctx>>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = args.into_iter();
        let (ty, ptr) = self.syscalls[iter.len()];
        self.builder
            .build_indirect_call(
                ty,
                ptr,
                &iter::once(nr)
                    .chain(iter)
                    .map(BasicMetadataValueEnum::from)
                    .collect::<Box<_>>(),
                "",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
    }
    pub fn new(
        context: &'ctx inkwell::context::Context,
        tt: &'ctx B::TT,
        et: &'ctx B::ET,
        base: &'ctx B,
        target_machine: TargetMachine,
        module_name: &str,
    ) -> Self {
        let target_data = target_machine.get_target_data();
        let ptr_int_t = context.ptr_sized_int_type(&target_data, None);
        Self {
            context,
            tt,
            et,
            base,
            module: context.create_module(module_name),
            builder: context.create_builder(),
            target_machine,
            target_data,
            syscalls: (0..=6)
                .map(|n| {
                    const SYS_RET: &str = "rax";
                    const SYS_NR: &str = "rax";
                    const SYS_ARGS: &[&str] = &["rdi", "rsi", "rdx", "r10", "r8", "r9"];
                    const SYS_CLOBBER: &[&str] = &["rcx", "r11", "memory"];

                    let inputs = iter::repeat_n(BasicMetadataTypeEnum::from(ptr_int_t), n + 1)
                        .collect::<Vec<_>>();
                    let ty = ptr_int_t.fn_type(&inputs, false);

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
                .collect(),
            structs: RwLock::new(HashMap::new()),
            enums: RwLock::new(HashMap::new()),
            callables: RwLock::new(HashMap::new()),
            function: RwLock::new(None),
        }
    }
    pub fn eprint(&self) {
        self.module.print_to_stderr();
    }
    pub fn verify(&self) -> Result<(), LLVMString> {
        self.module.verify()
    }
    pub fn optimize(&self) -> Result<(), LLVMString> {
        let opts = PassBuilderOptions::create();
        self.module
            .run_passes("default<O3>", &self.target_machine, opts)
    }
    pub fn write_asm(&self, path: &Path) -> Result<(), LLVMString> {
        self.target_machine
            .write_to_file(&self.module, FileType::Assembly, path)
    }
    pub fn write_object(&self, path: &Path) -> Result<(), LLVMString> {
        self.target_machine
            .write_to_file(&self.module, FileType::Object, path)
    }

    fn build_closure(
        &self,
        function: FunctionValue<'ctx>,
        closure: Option<PointerValue<'ctx>>,
    ) -> BasicValue<'ctx> {
        let mut array = self
            .context
            .ptr_type(AddressSpace::default())
            .array_type(2)
            .get_poison();
        array = self
            .builder
            .build_insert_value(
                array,
                function.as_global_value().as_pointer_value(),
                0,
                "function pointer",
            )
            .unwrap()
            .into_array_value();
        if let Some(closure) = closure {
            array = self
                .builder
                .build_insert_value(array, closure, 1, "function closure")
                .unwrap()
                .into_array_value();
        }
        Some(array.into())
    }
    fn get_closure(&self, data: BasicValue<'ctx>) -> (PointerValue<'ctx>, PointerValue<'ctx>) {
        let closure = data.unwrap().into_array_value();
        let fptr = self
            .builder
            .build_extract_value(closure, 0, "function pointer")
            .unwrap()
            .into_pointer_value();
        let cptr = self
            .builder
            .build_extract_value(closure, 1, "function closure")
            .unwrap()
            .into_pointer_value();
        (fptr, cptr)
    }
    fn function_attributes(&self, function: FunctionValue<'ctx>) {
        // do not probe the stack
        // TODO: link with a library on windows that has a stack prober
        function.add_attribute(
            AttributeLoc::Function,
            self.context
                .create_string_attribute("no-stack-arg-probe", ""),
        );
    }

    pub fn get_struct(&self, tys: mu::Tuple) -> Option<StructType<'ctx>> {
        let read = self.structs.read().unwrap();
        match read.get(&tys) {
            Some(&(_, s)) => s,
            None => {
                drop(read);

                // NOTE: recursive structs will cause a stack overflow here
                let fields = self.tt[tys]
                    .iter()
                    .map(|&field| self.get_type(field))
                    .collect::<Box<_>>();
                let llvm_fields = fields
                    .iter()
                    .filter_map(|f| f.basic_type(self))
                    .collect::<Box<_>>();
                let struc = (!llvm_fields.is_empty()).then(|| match self.tt.tuple_name(tys) {
                    Some(name) => {
                        let s = self.context.opaque_struct_type(name);
                        s.set_body(&llvm_fields, false);
                        s
                    }
                    None => self.context.struct_type(&llvm_fields, false),
                });
                self.structs.write().unwrap().insert(tys, (fields, struc));
                struc
            }
        }
    }
    pub fn has_zero_niche(&self, ty: mu::Type) -> bool {
        match self.tt[ty] {
            mu::TypeEnum::Base(ref base) => B::has_zero_niche(base, self),
            mu::TypeEnum::Sum(tys) => match self.get_enum(tys) {
                Enum::Never => true,
                Enum::Units(_) | Enum::ZeroNiche(_, _) => false,
                Enum::Single(_) | Enum::TaggedUnion(_) => self.has_zero_niche(self.tt[tys][0]),
            },
            mu::TypeEnum::Product(tys) => {
                self.tt[tys].iter().any(|&field| self.has_zero_niche(field))
            }
            mu::TypeEnum::Function(_) => true,
        }
    }
    pub fn get_enum(&self, tys: mu::Enum) -> Enum<'ctx> {
        let read = self.enums.read().unwrap();
        match read.get(&tys) {
            Some(&(_, s)) => s,
            None => {
                drop(read);

                // NOTE: recursive structs will cause a stack overflow here
                let variants = self.tt[tys]
                    .iter()
                    .map(|&field| self.get_type(field))
                    .collect::<Box<_>>();
                let tag_ty = || match (variants.len() - 1).ilog2() {
                    0 => self.context.bool_type(),
                    1..8 => self.context.i8_type(),
                    8..16 => self.context.i16_type(),
                    16..32 => self.context.i32_type(),
                    _ => panic!("that's just way too many variants"),
                };
                let e = match self.tt[tys] {
                    // no variants
                    [] => Enum::Never,
                    // single variant
                    [_] => Enum::Single(variants[0].basic_type(self)),
                    // only unit variant
                    _ if variants.iter().all(|v| !v.nonzero_sized()) => Enum::Units(tag_ty()),
                    // unit variant and variant with zero niche
                    [value, _] if self.has_zero_niche(value) && !variants[1].nonzero_sized() => {
                        Enum::ZeroNiche(variants[0].basic_type(self), true)
                    }
                    [_, value] if self.has_zero_niche(value) && !variants[0].nonzero_sized() => {
                        Enum::ZeroNiche(variants[1].basic_type(self), false)
                    }
                    // other
                    _ => todo!("tagged union"),
                };
                self.enums.write().unwrap().insert(tys, (variants, e));
                e
            }
        }
    }
    pub fn get_type(&self, ty: mu::Type) -> Type<'ctx> {
        match self.tt[ty] {
            mu::TypeEnum::Base(ref base) => B::get_type(base, self),
            mu::TypeEnum::Product(tys) => Type::Data(self.get_struct(tys).map(Into::into)),
            mu::TypeEnum::Sum(tys) => self.get_enum(tys).into(),
            mu::TypeEnum::Function(function) => {
                Type::Function(self.get_function_type(function, true))
            }
        }
    }
    pub fn get_function_type(
        &self,
        function: mu::Function,
        closure_param: bool,
    ) -> FunctionType<'ctx> {
        let from = self
            .get_type(self.tt.insert_type(mu::TypeEnum::Product(function.from())))
            .basic_type(self);
        let to = self.get_type(function.to()).basic_type(self);

        if closure_param {
            let closure = self.context.ptr_type(AddressSpace::default());
            let param_types = match from {
                Some(f) => [f.into(), closure.into()],
                None => [closure.into(), closure.into()],
            };
            let param_types = match from {
                Some(_) => &param_types,
                None => &param_types[0..1],
            };
            match to {
                Some(t) => t.fn_type(param_types, false),
                None => self.context.void_type().fn_type(param_types, false),
            }
        } else {
            let meta = from.map(BasicMetadataTypeEnum::from);
            let param_types = meta.as_slice();
            match to {
                Some(t) => t.fn_type(param_types, false),
                None => self.context.void_type().fn_type(param_types, false),
            }
        }
    }
    pub fn build_function(
        &self,
        abstraction: mu::Expression,
        name: &str,
        linkage: Option<Linkage>,
    ) -> FunctionValue<'ctx> {
        let mu::ExpressionEnum::Abstract(from, e) = self.et[abstraction] else {
            panic!();
        };
        let fun = mu::Function::new(from, e.get_type(self.tt, self.et), self.tt);
        let function_type = self.get_function_type(fun, false);
        let function = self.module.add_function(name, function_type, linkage);
        self.function_attributes(function);
        self.builder
            .position_at_end(self.context.append_basic_block(function, ""));
        *self.function.write().unwrap() = Some(function);
        let out = self
            .build_expression(
                e,
                &im::Vector::unit(Value::Data(
                    (function.count_params() == 2).then(|| function.get_first_param().unwrap()),
                )),
            )
            .basic_value(self);
        if !fun.never_returns(self.tt) {
            self.builder
                .build_return(
                    out.as_ref()
                        .map(|e| e as &dyn inkwell::values::BasicValue)
                        .filter(|_| function_type.get_return_type().is_some()),
                )
                .unwrap();
        }
        self.builder.clear_insertion_position();
        *self.function.write().unwrap() = None;
        function
    }
    fn build_expression(
        &self,
        e: mu::Expression,
        refs: &im::Vector<Value<'ctx, B>>,
    ) -> Value<'ctx, B> {
        match self.et[e] {
            mu::ExpressionEnum::Operation(ref o) => B::build_operation(o, self),
            mu::ExpressionEnum::Reference(_, n) => refs[n as usize].clone(),
            mu::ExpressionEnum::Let(e1, e2) => {
                let mut refs_new = refs.clone();
                refs_new.push_front(self.build_expression(e1, refs));
                self.build_expression(e2, &refs_new)
            }
            mu::ExpressionEnum::Sequence(es, en) => {
                for &e in self.et[es].iter() {
                    let _ = self.build_expression(e, refs);
                }
                self.build_expression(en, refs)
            }
            mu::ExpressionEnum::Construct(types, expressions) => self.build_construct(
                types,
                self.et[expressions]
                    .iter()
                    .map(|&e| self.build_expression(e, refs)),
            ),
            mu::ExpressionEnum::Apply(f, e) => {
                let fun = f.get_type(self.tt, self.et).into_function(self.tt);
                let fval = self.build_expression(f, refs);
                let vals = self.et[e].iter().map(|&e| {
                    ValueOrExpression::Expression(Expression {
                        expr: e,
                        bound: refs.clone(),
                    })
                });
                self.build_call(fun, fval, vals)
            }
            mu::ExpressionEnum::Member(e, index) => {
                let types = e.get_type(self.tt, self.et).into_product(self.tt);
                let val = self.build_expression(e, refs);
                self.build_member(types, index, val)
            }
            mu::ExpressionEnum::Variant(variants, i, e) => {
                let variant = self.build_expression(e, refs);

                match self.get_enum(variants) {
                    Enum::Never => panic!(),
                    Enum::Units(int) => int.const_int(i as u64, false).into(),
                    Enum::Single(_) => variant,
                    Enum::ZeroNiche(ty, zero_index) => {
                        if i == zero_index as u32 {
                            Value::Data(ty.map(BasicTypeEnum::const_zero))
                        } else {
                            variant
                        }
                    }
                    Enum::TaggedUnion(_) => todo!(),
                }
            }
            mu::ExpressionEnum::Match(e, es) => {
                let sum = e.get_type(self.tt, self.et).into_sum(self.tt);
                let variant = self.build_expression(e, refs);

                let out = self
                    .get_type(self.et[es][0].get_type(self.tt, self.et))
                    .basic_type(self);
                match self.get_enum(sum) {
                    Enum::Never => Value::Data(None),
                    Enum::Units(int) => {
                        // TODO: simplify in the case of exactly 2 units

                        let else_block = self.build_block("");
                        let cases = (0..self.et[es].len() as u32)
                            .map(|n| {
                                (
                                    int.const_int(n.into(), false),
                                    self.build_block(
                                        self.tt
                                            .enum_variant_name(sum, n)
                                            .map(Deref::deref)
                                            .unwrap_or(""),
                                    ),
                                )
                            })
                            .collect::<Box<_>>();
                        let end_block = self.build_block("");

                        self.builder
                            .build_switch(
                                variant.basic_value(self).unwrap().into_int_value(),
                                else_block,
                                &cases,
                            )
                            .unwrap();

                        let phi = out.map(|ty| {
                            self.builder.position_at_end(end_block);
                            self.builder.build_phi(ty, "").unwrap()
                        });

                        let mut refs_new = refs.clone();
                        refs_new.push_front(Value::Data(None));
                        for ((_, case), &e) in cases.into_iter().zip(&self.et[es]) {
                            self.builder.position_at_end(case);
                            let val = self.build_expression(e, &refs_new);
                            self.builder.build_unconditional_branch(end_block).unwrap();

                            if let Some(phi) = phi {
                                phi.add_incoming(&[(
                                    &val.basic_value(self).unwrap(),
                                    self.builder.get_insert_block().unwrap(),
                                )]);
                            }
                        }

                        self.builder.position_at_end(else_block);
                        self.builder.build_unreachable().unwrap();

                        self.builder.position_at_end(end_block);
                        Value::Data(phi.map(PhiValue::as_basic_value))
                    }
                    Enum::Single(_) => {
                        let mut refs_new = refs.clone();
                        refs_new.push_front(variant);
                        self.build_expression(self.et[es][0], &refs_new)
                    }
                    Enum::ZeroNiche(_, zero_index) => match variant.basic_value(self) {
                        Some(v) => {
                            let is_zero = self.build_is_zero(v);

                            let then_block = self.build_block("");
                            let else_block = self.build_block("");
                            let next_block = self.build_block("");
                            self.builder
                                .build_conditional_branch(is_zero, then_block, else_block)
                                .unwrap();

                            self.builder.position_at_end(then_block);
                            let mut refs_new = refs.clone();
                            refs_new.push_front(Value::Data(None));
                            let then_val =
                                self.build_expression(self.et[es][zero_index as usize], &refs_new);
                            let then_end = self.builder.get_insert_block().unwrap();
                            self.builder.build_unconditional_branch(next_block).unwrap();

                            self.builder.position_at_end(else_block);
                            let mut refs_new = refs.clone();
                            refs_new.push_front(Value::Data(Some(v)));
                            let else_val = self
                                .build_expression(self.et[es][(!zero_index) as usize], &refs_new);
                            let else_end = self.builder.get_insert_block().unwrap();
                            self.builder.build_unconditional_branch(next_block).unwrap();

                            self.builder.position_at_end(next_block);
                            Value::Data(out.map(|ty| {
                                let then_val = then_val.basic_value(self).unwrap();
                                let else_val = else_val.basic_value(self).unwrap();
                                let phi = self.builder.build_phi(ty, "").unwrap();
                                phi.add_incoming(&[(&then_val, then_end), (&else_val, else_end)]);
                                phi.as_basic_value()
                            }))
                        }
                        None => {
                            let mut refs_new = refs.clone();
                            refs_new.push_front(Value::Data(None));
                            self.build_expression(self.et[es][zero_index as usize], &refs_new)
                        }
                    },
                    Enum::TaggedUnion(_) => todo!(),
                }
            }
            mu::ExpressionEnum::Abstract(from, body) => {
                let current_fun = {
                    let guard = self.function.read().unwrap();
                    guard.unwrap()
                };
                let current_block = self.builder.get_insert_block().unwrap();

                // create function
                let fun = mu::Function::new(from, body.get_type(self.tt, self.et), self.tt);
                let function_type = self.get_function_type(fun, true);
                let function = self
                    .module
                    .add_function("", function_type, Some(Linkage::Private));
                self.function_attributes(function);
                self.builder
                    .position_at_end(self.context.append_basic_block(function, ""));
                *self.function.write().unwrap() = Some(function);

                // build closure
                let mut captures = iter::repeat_n(false, refs.len()).collect::<Box<_>>();
                e.get_captures(self.et, &mut captures);
                let mut closure_members = Vec::new();
                let mut closure_refs = Vec::new();
                for (i, val) in refs.iter().enumerate().filter(|&(i, _)| captures[i]) {
                    match *val {
                        Value::Data(Some(val)) => {
                            closure_members.push(val);
                            closure_refs.push(i);
                        }
                        Value::Function(_, Some(val)) => {
                            closure_members.push(val.into());
                            closure_refs.push(i);
                        }
                        _ => {}
                    }
                }

                let mut refs_new = refs.clone();
                let closure_type = (!closure_members.is_empty()).then(|| {
                    let closure_pointer = function.get_last_param().unwrap().into_pointer_value();
                    let closure_types = closure_members
                        .iter()
                        .map(|v| v.get_type())
                        .collect::<Box<_>>();
                    let closure_type = self.context.struct_type(&closure_types, false);
                    let closure = self
                        .builder
                        .build_load(closure_type, closure_pointer, "")
                        .unwrap()
                        .into_struct_value();
                    for (nth, i) in closure_refs.into_iter().enumerate() {
                        match &mut refs_new[i] {
                            Value::Data(Some(val)) => {
                                *val = self
                                    .builder
                                    .build_extract_value(closure, nth as u32, "")
                                    .unwrap();
                            }
                            Value::Function(_, Some(val)) => {
                                *val = self
                                    .builder
                                    .build_extract_value(closure, nth as u32, "")
                                    .unwrap()
                                    .into_pointer_value();
                            }
                            _ => {}
                        }
                    }
                    closure_type
                });

                // build function
                refs_new.push_front(Value::Data(
                    (function.count_params() == 2).then(|| function.get_first_param().unwrap()),
                ));
                let out = self.build_expression(body, &refs_new).basic_value(self);
                self.builder
                    .build_return(
                        out.as_ref()
                            .map(|e| e as &dyn inkwell::values::BasicValue)
                            .filter(|_| function_type.get_return_type().is_some()),
                    )
                    .unwrap();

                // return
                self.builder.position_at_end(current_block);
                *self.function.write().unwrap() = Some(current_fun);
                let closure_pointer = closure_type.map(|closure_type| {
                    let closure_pointer = self.builder.build_alloca(closure_type, "").unwrap();
                    let mut closure = closure_type.get_poison();
                    for (nth, member) in closure_members.into_iter().enumerate() {
                        closure = self
                            .builder
                            .build_insert_value(closure, member, nth as u32, "")
                            .unwrap()
                            .into_struct_value();
                    }
                    let _ = self.builder.build_store(closure_pointer, closure).unwrap();
                    closure_pointer
                });
                Value::Function(function, closure_pointer)
            }
            mu::ExpressionEnum::Try(ty, e) => todo!(),
        }
    }
    fn build_is_zero(&self, v: BasicValueEnum<'ctx>) -> IntValue<'ctx> {
        match v {
            BasicValueEnum::IntValue(int) if int.get_type().get_bit_width() == 1 => int,
            BasicValueEnum::IntValue(int) => self
                .builder
                .build_int_compare(IntPredicate::EQ, int, int.get_type().const_zero(), "")
                .unwrap(),
            BasicValueEnum::PointerValue(ptr) => self
                .builder
                .build_int_compare(IntPredicate::EQ, ptr, ptr.get_type().const_zero(), "")
                .unwrap(),
            BasicValueEnum::StructValue(struc) => {
                // TODO: do bitwise compare with 0 if struct is simply comparable
                let mut is_zero = self.context.bool_type().const_all_ones();
                for n in 0..struc.get_type().count_fields() {
                    let field = self.builder.build_extract_value(struc, n, "").unwrap();
                    let is_field_zero = self.build_is_zero(field);
                    is_zero = self.builder.build_and(is_zero, is_field_zero, "").unwrap()
                }
                is_zero
            }
            _ => todo!(),
        }
    }
    pub fn build_member(
        &self,
        types: mu::Tuple,
        index: u32,
        val: Value<'ctx, B>,
    ) -> Value<'ctx, B> {
        let member_types = &self.tt[types];
        let member = member_types[index as usize];
        Value::Data(val.basic_value(self).and_then(|data| {
            self.get_type(member).nonzero_sized().then(|| {
                let nth = member_types[..index as usize]
                    .iter()
                    .filter(|&&member| self.get_type(member).nonzero_sized())
                    .count() as u32;
                self.builder
                    .build_extract_value(
                        data.into_struct_value(),
                        nth,
                        self.tt
                            .tuple_field_name(types, index)
                            .map(Deref::deref)
                            .unwrap_or(""),
                    )
                    .unwrap()
            })
        }))
    }
    pub fn build_member_pointer(
        &self,
        types: mu::Tuple,
        index: u32,
        val: Value<'ctx, B>,
    ) -> Value<'ctx, B> {
        let member_types = &self.tt[types];
        let member = member_types[index as usize];
        Value::Data(val.basic_value(self).and_then(|data| {
            self.get_type(member).nonzero_sized().then(|| {
                let pointee_ty = self
                    .get_type(self.tt.insert_type(mu::TypeEnum::Product(types)))
                    .basic_type(self)
                    .unwrap();
                let nth = member_types[..index as usize]
                    .iter()
                    .filter(|&&member| self.get_type(member).nonzero_sized())
                    .count() as u32;
                self.builder
                    .build_struct_gep(
                        pointee_ty,
                        data.into_pointer_value(),
                        nth,
                        self.tt
                            .tuple_field_name(types, index)
                            .map(Deref::deref)
                            .unwrap_or(""),
                    )
                    .unwrap()
                    .into()
            })
        }))
    }
    fn build_construct(
        &self,
        types: mu::Tuple,
        members: impl IntoIterator<Item = Value<'ctx, B>>,
    ) -> Value<'ctx, B> {
        let members = members.into_iter().enumerate().filter_map(|(index, val)| {
            // any 'callable' will get turned into a small function
            val.basic_value(self).map(|v| {
                (
                    self.tt
                        .tuple_field_name(types, index as u32)
                        .map(Deref::deref)
                        .unwrap_or(""),
                    v,
                )
            })
        });
        match self.get_struct(types) {
            Some(struc) => {
                let mut value = struc.get_poison();
                for (nth, (name, member)) in members.enumerate() {
                    value = self
                        .builder
                        .build_insert_value(value, member, nth as u32, name)
                        .unwrap()
                        .into_struct_value();
                }
                Value::Data(Some(value.into()))
            }
            None => {
                // fully consume fields iterator
                members.for_each(drop);
                Value::Data(None)
            }
        }
    }
    pub fn build_call(
        &self,
        fun: mu::Function,
        fval: Value<'ctx, B>,
        vals: impl IntoIterator<Item = ValueOrExpression<'ctx, B>>,
    ) -> Value<'ctx, B> {
        match fval {
            Value::Data(data) => {
                self.build_indirect_call(fun, data, vals.into_iter().map(|v| v.build(self)))
            }
            Value::Function(function, closure) => {
                let val = self
                    .build_construct(fun.from(), vals.into_iter().map(|v| v.build(self)))
                    .basic_value(self);
                let closure = closure
                    .unwrap_or_else(|| self.context.ptr_type(AddressSpace::default()).get_poison());
                let args = match val {
                    Some(v) => [v.into(), closure.into()],
                    None => [closure.into(), closure.into()],
                };
                let args = match val {
                    Some(_) => &args,
                    None => &args[0..1],
                };
                let out = self
                    .builder
                    .build_call(function, args, "")
                    .unwrap()
                    .try_as_basic_value()
                    .basic();
                Value::Data(out)
            }
            Value::Callable(c) => B::build_callable(&c, fun, vals, self),
        }
    }
    pub fn build_indirect_call(
        &self,
        fun: mu::Function,
        fval: BasicValue<'ctx>,
        vals: impl IntoIterator<Item = Value<'ctx, B>>,
    ) -> Value<'ctx, B> {
        let val = self.build_construct(fun.from(), vals).basic_value(self);

        let function_type = self.get_function_type(fun, true);
        let (fptr, closure) = self.get_closure(fval);

        let args = match val {
            Some(v) => [v.into(), closure.into()],
            None => [closure.into(), closure.into()],
        };
        let args = match val {
            Some(_) => &args,
            None => &args[0..1],
        };
        let out = self
            .builder
            .build_indirect_call(function_type, fptr, args, "")
            .unwrap()
            .try_as_basic_value()
            .basic();
        Value::Data(out)
    }
    pub fn build_block(&self, name: &str) -> BasicBlock<'ctx> {
        self.context
            .append_basic_block(self.function.read().unwrap().unwrap(), name)
    }
}
