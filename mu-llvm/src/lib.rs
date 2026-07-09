use std::collections::HashMap;
use std::hash::Hash;
use std::iter;
use std::ops::Deref;
use std::path::Path;
use std::sync::RwLock;

use inkwell::AddressSpace;
use inkwell::attributes::AttributeLoc;
use inkwell::basic_block::BasicBlock;
use inkwell::module::Linkage;
use inkwell::passes::PassBuilderOptions;
use inkwell::support::LLVMString;
use inkwell::targets::{FileType, TargetData, TargetMachine};
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, StructType};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
};
use mu::TypeTable as _;

pub trait Builder
where
    <Self::TT as mu::TypeTable>::Name: Deref<Target = str>,
{
    type Base;
    type TT: mu::TypeTable<Base = Self::Base> + ?Sized;
    type ET: mu::ExpressionTable<Base = Self::Base> + ?Sized;
    type Callable: mu::Typed<Base = Self::Base> + Clone + Hash + Eq;

    fn get_base_type<'ctx>(
        base: &<Self::TT as mu::TypeTable>::Base,
        llvm: &Context<'ctx, Self>,
    ) -> Type<'ctx>;
    fn build_operation<'ctx>(
        op: &<Self::ET as mu::ExpressionTable>::Operation,
        llvm: &Context<'ctx, Self>,
    ) -> Value<'ctx, Self::Callable>;
    fn build_callable<'ctx>(
        op: &Self::Callable,
        op_ty: mu::Function,
        params: impl IntoIterator<Item = Value<'ctx, Self::Callable>>,
        llvm: &Context<'ctx, Self>,
    ) -> DataValue<'ctx>;
    // TODO: build callable with param as expression
    // this will prevent every if statement to be a seperate function
}

#[derive(Clone, Copy)]
pub struct DataValue<'ctx>(pub Option<BasicValueEnum<'ctx>>);

impl<'ctx> DataValue<'ctx> {
    pub fn llvm_members<B: Builder + ?Sized>(
        self,
        llvm: &Context<'ctx, B>,
    ) -> impl ExactSizeIterator<Item = BasicValueEnum<'ctx>> {
        let fields = self
            .0
            .map(|v| v.into_struct_value().get_type().count_fields())
            .unwrap_or(0);
        (0..fields).map(move |nth| {
            let struc = self.0.unwrap().into_struct_value();
            llvm.builder.build_extract_value(struc, nth, "").unwrap()
        })
    }
    pub fn members<B: Builder + ?Sized>(
        self,
        types: mu::Types,
        llvm: &Context<'ctx, B>,
    ) -> impl ExactSizeIterator<Item = DataValue<'ctx>> {
        let mut nth = 0;
        llvm.tt[types]
            .iter()
            .copied()
            .enumerate()
            .map(move |(index, t)| {
                if llvm.get_type(t).nonzero_sized() {
                    let struc = self.0.unwrap().into_struct_value();
                    let val = llvm
                        .builder
                        .build_extract_value(
                            struc,
                            nth,
                            llvm.tt
                                .tuple_field_name(types, index as u32)
                                .map(Deref::deref)
                                .unwrap_or(""),
                        )
                        .unwrap();
                    nth += 1;
                    DataValue(Some(val))
                } else {
                    DataValue(None)
                }
            })
    }
    pub fn members_exact<const N: usize, B: Builder + ?Sized>(
        self,
        types: mu::Types,
        llvm: &Context<'ctx, B>,
    ) -> [DataValue<'ctx>; N] {
        match self.members(types, llvm).collect::<Vec<_>>().try_into() {
            Ok(v) => v,
            Err(_) => panic!(),
        }
    }
}

#[derive(Clone, Copy)]
pub struct DataType<'ctx>(pub Option<BasicTypeEnum<'ctx>>);

#[derive(Clone, Copy)]
pub enum Type<'ctx> {
    Data(DataType<'ctx>),
    Function(FunctionType<'ctx>),
}

impl<'ctx> Type<'ctx> {
    fn nonzero_sized(self) -> bool {
        match self {
            Type::Data(data_type) => data_type.0.is_some(),
            Type::Function(_) => true,
        }
    }
    pub fn get_data_type<B: Builder + ?Sized>(self, llvm: &Context<'ctx, B>) -> DataType<'ctx> {
        match self {
            Type::Data(data_type) => data_type,
            Type::Function(_) => DataType(Some(
                llvm.context
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .into(),
            )),
        }
    }
}

#[derive(Clone, Copy)]
pub enum Value<'ctx, C> {
    Data(DataValue<'ctx>),
    Function(FunctionValue<'ctx>, Option<PointerValue<'ctx>>),
    Callable(C),
}

impl<'ctx, C> Value<'ctx, C>
where
    C: Hash + Eq + Clone,
{
    pub fn build<B: Builder<Callable = C> + ?Sized>(
        self,
        llvm: &Context<'ctx, B>,
    ) -> DataValue<'ctx>
    where
        C: mu::Typed<Base = B::Base>,
    {
        match self {
            Value::Data(data) => data,
            Value::Function(function, closure) => llvm.build_closure(function, closure),
            Value::Callable(c) => {
                // we create a small function that is just this operation cuz we need it as a closure
                let function = match llvm.callables.read().unwrap().get(&c).copied() {
                    Some(function) => function,
                    None => {
                        // build function
                        let current_block = llvm.builder.get_insert_block().unwrap();
                        let fun = c.get_type(llvm.tt).into_function(llvm.tt);

                        let function_type = llvm.get_function_type(fun, true);
                        let function =
                            llvm.module
                                .add_function("", function_type, Some(Linkage::Private));
                        llvm.function_attributes(function);
                        llvm.builder
                            .position_at_end(llvm.context.append_basic_block(function, ""));
                        let params = DataValue(
                            (function.count_params() == 2)
                                .then(|| function.get_first_param().unwrap()),
                        );
                        let out = B::build_callable(
                            &c,
                            fun,
                            params.members(fun.from(), llvm).map(|v| Value::Data(v)),
                            llvm,
                        );
                        if fun.never_returns(llvm.tt) {
                            llvm.builder.build_unreachable().unwrap();
                        } else {
                            llvm.builder
                                .build_return(out.0.as_ref().map(|e| e as &dyn BasicValue))
                                .unwrap();
                        }

                        // return
                        llvm.builder.position_at_end(current_block);
                        llvm.callables.write().unwrap().insert(c.clone(), function);
                        function
                    }
                };
                llvm.build_closure(function, None)
            }
        }
    }
}

type CallableCache<'ctx, C> = HashMap<C, FunctionValue<'ctx>>;
type StructCache<'ctx> = HashMap<mu::Types, (Box<[Type<'ctx>]>, Option<StructType<'ctx>>)>;

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
    ) -> DataValue<'ctx> {
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
        DataValue(Some(array.into()))
    }
    fn get_closure(&self, data: DataValue<'ctx>) -> (PointerValue<'ctx>, PointerValue<'ctx>) {
        let closure = data.0.unwrap().into_array_value();
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

    pub fn get_struct(&self, tys: mu::Types) -> Option<StructType<'ctx>> {
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
                    .filter_map(|f| f.get_data_type(self).0)
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
    pub fn get_type(&self, ty: mu::Type) -> Type<'ctx> {
        match self.tt[ty] {
            mu::TypeEnum::Base(ref base) => B::get_base_type(base, self),
            mu::TypeEnum::Never => Type::Data(DataType(None)),
            mu::TypeEnum::Product(tys) => {
                Type::Data(DataType(self.get_struct(tys).map(Into::into)))
            }
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
            .get_data_type(self);
        let to = self.get_type(function.to()).get_data_type(self);

        if closure_param {
            let closure = self.context.ptr_type(AddressSpace::default());
            let param_types = match from.0 {
                Some(f) => [f.into(), closure.into()],
                None => [closure.into(), closure.into()],
            };
            let param_types = match from.0 {
                Some(_) => &param_types,
                None => &param_types[0..1],
            };
            match to.0 {
                Some(t) => t.fn_type(param_types, false),
                None => self.context.void_type().fn_type(param_types, false),
            }
        } else {
            let meta = from.0.map(BasicMetadataTypeEnum::from);
            let param_types = meta.as_slice();
            match to.0 {
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
                &im::Vector::unit(Value::Data(DataValue(
                    (function.count_params() == 2).then(|| function.get_first_param().unwrap()),
                ))),
            )
            .build(self);
        if fun.never_returns(self.tt) {
            self.builder.build_unreachable().unwrap();
        } else {
            self.builder
                .build_return(
                    out.0
                        .as_ref()
                        .map(|e| e as &dyn BasicValue)
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
        refs: &im::Vector<Value<'ctx, B::Callable>>,
    ) -> Value<'ctx, B::Callable> {
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
                let vals = self.et[e].iter().map(|&e| self.build_expression(e, refs));
                self.build_call(fun, fval, vals)
            }
            mu::ExpressionEnum::Member(e, index) => {
                let types = e.get_type(self.tt, self.et).into_product(self.tt);
                let member_types = &self.tt[types];
                let member = member_types[index as usize];

                let val = self.build_expression(e, refs).build(self);

                Value::Data(DataValue(val.0.and_then(|data| {
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
                })))
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
                        Value::Data(DataValue(Some(val))) => {
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
                            Value::Data(DataValue(Some(val))) => {
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
                refs_new.push_front(Value::Data(DataValue(
                    (function.count_params() == 2).then(|| function.get_first_param().unwrap()),
                )));
                let out = self.build_expression(body, &refs_new).build(self);
                self.builder
                    .build_return(
                        out.0
                            .as_ref()
                            .map(|e| e as &dyn BasicValue)
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
    fn build_construct(
        &self,
        types: mu::Types,
        members: impl IntoIterator<Item = Value<'ctx, B::Callable>>,
    ) -> Value<'ctx, B::Callable> {
        let members = members.into_iter().enumerate().filter_map(|(index, val)| {
            // any 'callable' will get turned into a small function
            val.build(self).0.map(|v| {
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
                Value::Data(DataValue(Some(value.into())))
            }
            None => {
                // fully consume fields iterator
                members.for_each(drop);
                Value::Data(DataValue(None))
            }
        }
    }
    pub fn build_call(
        &self,
        fun: mu::Function,
        fval: Value<'ctx, B::Callable>,
        vals: impl IntoIterator<Item = Value<'ctx, B::Callable>>,
    ) -> Value<'ctx, B::Callable> {
        match fval {
            Value::Data(data) => self.build_indirect_call(fun, data, vals),
            Value::Function(function, closure) => {
                let val = self.build_construct(fun.from(), vals).build(self);

                let closure = closure
                    .unwrap_or_else(|| self.context.ptr_type(AddressSpace::default()).get_poison());
                let args = match val.0 {
                    Some(v) => [v.into(), closure.into()],
                    None => [closure.into(), closure.into()],
                };
                let args = match val.0 {
                    Some(_) => &args,
                    None => &args[0..1],
                };
                let out = self
                    .builder
                    .build_call(function, args, "")
                    .unwrap()
                    .try_as_basic_value()
                    .basic();
                Value::Data(DataValue(out))
            }
            Value::Callable(c) => {
                let out = B::build_callable(&c, fun, vals, self);
                Value::Data(out)
            }
        }
    }
    pub fn build_indirect_call(
        &self,
        fun: mu::Function,
        fval: DataValue<'ctx>,
        vals: impl IntoIterator<Item = Value<'ctx, B::Callable>>,
    ) -> Value<'ctx, B::Callable> {
        let val = self.build_construct(fun.from(), vals).build(self);

        let function_type = self.get_function_type(fun, true);
        let (fptr, closure) = self.get_closure(fval);

        let args = match val.0 {
            Some(v) => [v.into(), closure.into()],
            None => [closure.into(), closure.into()],
        };
        let args = match val.0 {
            Some(_) => &args,
            None => &args[0..1],
        };
        let out = self
            .builder
            .build_indirect_call(function_type, fptr, args, "")
            .unwrap()
            .try_as_basic_value()
            .basic();
        Value::Data(DataValue(out))
    }
    pub fn build_block(&self, name: &str) -> BasicBlock<'ctx> {
        self.context
            .append_basic_block(self.function.read().unwrap().unwrap(), name)
    }
}
