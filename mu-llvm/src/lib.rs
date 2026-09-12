use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter;
use std::ops::Deref;
use std::path::Path;
use std::sync::{Arc, RwLock};

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
    BasicMetadataValueEnum, BasicValue as _, BasicValueEnum, FunctionValue, GlobalValue, IntValue,
    PhiValue, PointerValue, StructValue,
};
use inkwell::{AddressSpace, IntPredicate};
use mu::{Table as _, Typed as _};

pub trait Builder<'ctx>: Sized
where
    <Self::Table as mu::Table>::Name: Deref<Target = str>,
{
    type Base;
    type Table: mu::Table<Base = Self::Base> + ?Sized;
    type Callable: mu::Typed<Base = Self::Base> + Clone + Hash + Eq + Debug;

    fn has_zero_niche(base: &Self::Base, llvm: &Context<'ctx, Self>) -> bool;
    fn get_type(base: &Self::Base, llvm: &Context<'ctx, Self>) -> Type<'ctx>;
    fn build_operation(
        op: &<Self::Table as mu::Table>::Operation,
        llvm: &Context<'ctx, Self>,
    ) -> Value<'ctx, Self>;
    fn build_callable(
        op: &Self::Callable,
        params: impl IntoIterator<Item = ValueOrExpression<'ctx, Self>>,
        llvm: &Context<'ctx, Self>,
    ) -> Value<'ctx, Self>;
}

pub type BasicValue<'ctx> = Option<BasicValueEnum<'ctx>>;

pub type BasicType<'ctx> = Option<BasicTypeEnum<'ctx>>;

#[derive(Clone)]
pub enum Type<'ctx> {
    Data(BasicType<'ctx>),
    Function(FunctionType<'ctx>),
    VTable(Arc<[FunctionType<'ctx>]>),
}

impl<'ctx, T: inkwell::types::BasicType<'ctx>> From<T> for Type<'ctx> {
    fn from(value: T) -> Self {
        Self::Data(Some(value.as_basic_type_enum()))
    }
}

impl<'ctx> Type<'ctx> {
    pub fn nonzero_sized(&self) -> bool {
        match self {
            Type::Data(data_type) => data_type.is_some(),
            Type::Function(_) => true,
            Type::VTable(fs) => !fs.is_empty(),
        }
    }
    pub fn basic_type<B: Builder<'ctx>>(&self, llvm: &Context<'ctx, B>) -> BasicType<'ctx> {
        match self {
            Type::Data(data_type) => *data_type,
            Type::Function(_) => Some(
                llvm.context
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .into(),
            ),
            Type::VTable(fs) => (!fs.is_empty()).then(|| {
                llvm.context
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .into()
            }),
        }
    }
}

pub enum Captures<'ctx, B: Builder<'ctx>> {
    Local(BTreeMap<u32, Value<'ctx, B>>),
    Closure(Closure<'ctx>),
}

#[derive(Clone, Debug, Default)]
pub struct Closure<'ctx> {
    value: Option<StructValue<'ctx>>,
    refs: Arc<[u32]>,
}

impl<'ctx, B: Builder<'ctx>> Clone for Captures<'ctx, B> {
    fn clone(&self) -> Self {
        match self {
            Self::Local(arg0) => Self::Local(arg0.clone()),
            Self::Closure(arg0) => Self::Closure(arg0.clone()),
        }
    }
}

impl<'ctx, B: Builder<'ctx>> Debug for Captures<'ctx, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local(arg0) => f.debug_tuple("Local").field(arg0).finish(),
            Self::Closure(arg0) => f.debug_tuple("Closure").field(arg0).finish(),
        }
    }
}

impl<'ctx, B: Builder<'ctx>> Captures<'ctx, B> {
    fn get(
        es: impl IntoIterator<Item = mu::Expression>,
        llvm: &Context<'ctx, B>,
        refs: &im::Vector<Value<'ctx, B>>,
    ) -> Self {
        let mut captures = iter::repeat_n(false, refs.len()).collect::<Box<_>>();
        for e in es {
            e.get_captures(llvm.table, &mut captures);
        }

        let mut map = BTreeMap::new();
        for (i, _) in captures.iter().enumerate().filter(|&(_, &b)| b) {
            map.insert(i as u32, refs[i].clone());
        }

        Self::Local(map)
    }
    fn refs(&self, llvm: &Context<'ctx, B>) -> im::Vector<Value<'ctx, B>> {
        match self {
            Self::Local(btree_map) => {
                let len = btree_map.keys().copied().last().unwrap_or(0);
                let mut iter = btree_map.iter().peekable();
                (0..=len)
                    .map(|i| {
                        if let Some((_, val)) = iter.next_if(|&(&pos, _)| pos == i) {
                            val.clone()
                        } else {
                            Value::Data(None)
                        }
                    })
                    .collect()
            }
            Self::Closure(closure) => closure.refs(llvm),
        }
    }
    pub fn build(self, llvm: &Context<'ctx, B>) -> Closure<'ctx> {
        let btree_map = match self {
            Captures::Local(btree_map) => btree_map,
            Captures::Closure(closure) => return closure,
        };

        let (indices, values): (Vec<u32>, Vec<BasicValueEnum<'ctx>>) = btree_map
            .into_iter()
            .filter_map(|(k, v)| v.basic_value(llvm).map(|v| (k, v)))
            .unzip();
        if values.is_empty() {
            Closure::default()
        } else {
            let types = values.iter().map(|v| v.get_type()).collect::<Box<_>>();
            let struct_type = llvm.context.struct_type(&types, false);
            let mut struct_val = struct_type.get_poison();
            for (i, value) in values.into_iter().enumerate() {
                struct_val = llvm
                    .builder
                    .build_insert_value(struct_val, value, i as u32, "")
                    .unwrap()
                    .into_struct_value();
            }
            Closure {
                value: Some(struct_val),
                refs: indices.into(),
            }
        }
    }
}
impl<'ctx> Closure<'ctx> {
    fn refs<B: Builder<'ctx>>(&self, llvm: &Context<'ctx, B>) -> im::Vector<Value<'ctx, B>> {
        match self.value {
            Some(value) => {
                let len = self.refs.iter().copied().last().unwrap_or(0);
                let mut iter = self.refs.iter().enumerate().peekable();
                (0..=len)
                    .map(|i| {
                        if let Some((idx, _)) = iter.next_if(|&(_, &pos)| pos == i) {
                            let field = llvm
                                .builder
                                .build_extract_value(value, idx as u32, "")
                                .unwrap();
                            Value::Data(Some(field))
                        } else {
                            Value::Data(None)
                        }
                    })
                    .collect()
            }
            None => im::Vector::new(),
        }
    }
    fn alloca<B: Builder<'ctx>>(&self, llvm: &Context<'ctx, B>) -> Option<PointerValue<'ctx>> {
        self.value.map(|value| {
            let ptr = llvm
                .builder
                .build_alloca(value.get_type(), "closure")
                .unwrap();
            llvm.builder.build_store(ptr, value).unwrap();
            ptr
        })
    }
    pub fn for_function<B: Builder<'ctx>>(
        self,
        f: FunctionValue<'ctx>,
        llvm: &Context<'ctx, B>,
    ) -> Self {
        match self.value {
            Some(value) => {
                let ptr = f.get_last_param().unwrap().into_pointer_value();
                let struct_val = llvm
                    .builder
                    .build_load(value.get_type(), ptr, "closure")
                    .unwrap()
                    .into_struct_value();
                Self {
                    value: Some(struct_val),
                    refs: self.refs,
                }
            }
            None => self,
        }
    }
}

pub enum Value<'ctx, B: Builder<'ctx>> {
    Data(BasicValue<'ctx>),
    Abstract(mu::Expression, Captures<'ctx, B>),
    VTable(mu::Expressions, Captures<'ctx, B>),
    Function(PointerValue<'ctx>, Option<PointerValue<'ctx>>),
    Callable(B::Callable),
    Raise(
        FunctionValue<'ctx>,
        BasicBlock<'ctx>,
        Option<PhiValue<'ctx>>,
    ),
}

impl<'ctx, B: Builder<'ctx>> Clone for Value<'ctx, B> {
    fn clone(&self) -> Self {
        match *self {
            Self::Data(arg0) => Self::Data(arg0),
            Self::Abstract(arg0, ref arg1) => Self::Abstract(arg0, arg1.clone()),
            Self::Function(arg0, arg1) => Self::Function(arg0, arg1),
            Self::VTable(arg0, ref arg1) => Self::VTable(arg0, arg1.clone()),
            Self::Callable(ref arg0) => Self::Callable(arg0.clone()),
            Self::Raise(arg0, arg1, arg2) => Self::Raise(arg0, arg1, arg2),
        }
    }
}

impl<'ctx, B: Builder<'ctx>> Debug for Value<'ctx, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Data(arg0) => f.debug_tuple("Data").field(arg0).finish(),
            Self::Abstract(arg0, arg1) => {
                f.debug_tuple("Abstract").field(arg0).field(arg1).finish()
            }
            Self::VTable(arg0, arg1) => f.debug_tuple("VTable").field(arg0).field(arg1).finish(),
            Self::Function(arg0, arg1) => {
                f.debug_tuple("Function").field(arg0).field(arg1).finish()
            }
            Self::Callable(arg0) => f.debug_tuple("Callable").field(arg0).finish(),
            Self::Raise(arg0, arg1, arg2) => f
                .debug_tuple("Raise")
                .field(arg0)
                .field(arg1)
                .field(arg2)
                .finish(),
        }
    }
}

impl<'ctx, B: Builder<'ctx>, T: inkwell::values::BasicValue<'ctx>> From<T> for Value<'ctx, B> {
    fn from(value: T) -> Self {
        Self::Data(Some(value.as_basic_value_enum()))
    }
}

impl<'ctx, B: Builder<'ctx>> Value<'ctx, B> {
    pub fn basic_value(self, llvm: &Context<'ctx, B>) -> BasicValue<'ctx> {
        match self {
            Value::Data(data) => data,
            Value::Abstract(e, captures) => {
                let closure = captures.build(llvm);
                let closure_ptr = closure.alloca(llvm);
                let function = llvm.build_abstract(e, closure);
                llvm.build_closure(function, closure_ptr)
            }
            Value::Function(function, closure) => {
                let mut array = llvm
                    .context
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .get_poison();
                array = llvm
                    .builder
                    .build_insert_value(array, function, 0, "function pointer")
                    .unwrap()
                    .into_array_value();
                if let Some(closure) = closure {
                    array = llvm
                        .builder
                        .build_insert_value(array, closure, 1, "function closure")
                        .unwrap()
                        .into_array_value();
                }
                Some(array.into())
            }
            Value::VTable(es, captures) => {
                if llvm.table[es].is_empty() {
                    return None;
                }

                let closure = captures.build(llvm);
                let closure_ptr = closure.alloca(llvm);

                let functions = llvm.table[es]
                    .iter()
                    .map(|&e| {
                        llvm.build_abstract(e, closure.clone())
                            .as_global_value()
                            .as_pointer_value()
                            .as_basic_value_enum()
                    })
                    .collect::<Box<_>>();
                let function_types = functions.iter().map(|e| e.get_type()).collect::<Box<_>>();
                // TODO: named vtable type?
                let vtable_type = llvm.context.struct_type(&function_types, false);

                let const_vtable = vtable_type.const_named_struct(&functions);
                let global_vtable = llvm.module.add_global(vtable_type, None, "");
                global_vtable.set_linkage(Linkage::Internal);
                global_vtable.set_constant(true);
                global_vtable.set_initializer(&const_vtable);

                let mut array = llvm
                    .context
                    .ptr_type(AddressSpace::default())
                    .array_type(2)
                    .get_poison();
                array = llvm
                    .builder
                    .build_insert_value(
                        array,
                        global_vtable.as_pointer_value(),
                        0,
                        "vtable pointer",
                    )
                    .unwrap()
                    .into_array_value();
                if let Some(closure_ptr) = closure_ptr {
                    array = llvm
                        .builder
                        .build_insert_value(array, closure_ptr, 1, "vtable closure")
                        .unwrap()
                        .into_array_value();
                }
                Some(array.into())
            }
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
                        let fun = c.get_type(llvm.table).into_function(llvm.table).unwrap();

                        let function = llvm.add_function(fun, true, None, Some(Linkage::Private));
                        llvm.builder
                            .position_at_end(llvm.context.append_basic_block(function, ""));
                        *llvm.function.write().unwrap() = Some(function);

                        let params = llvm
                            .function_arguments(fun, function)
                            .map(ValueOrExpression::Value);
                        let out = B::build_callable(&c, params, llvm).basic_value(llvm);
                        if !fun.never_returns(llvm.table) {
                            llvm.builder
                                .build_return(
                                    out.as_ref().map(|e| e as &dyn inkwell::values::BasicValue),
                                )
                                .unwrap();
                        } else {
                            llvm.builder.build_unreachable().unwrap();
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
            Value::Raise(_, _, _) => todo!(),
        }
    }
}

pub struct Expression<'ctx, B: Builder<'ctx>> {
    expr: mu::Expression,
    bound: im::Vector<Value<'ctx, B>>,
}

impl<'ctx, B: Builder<'ctx>> Clone for Expression<'ctx, B> {
    fn clone(&self) -> Self {
        Self {
            expr: self.expr,
            bound: self.bound.clone(),
        }
    }
}

impl<'ctx, B: Builder<'ctx>> Expression<'ctx, B> {
    pub fn build(self, llvm: &Context<'ctx, B>) -> Value<'ctx, B> {
        llvm.build_expression(self.expr, &self.bound)
    }
    pub fn build_call(
        self,
        fun: mu::FunctionType,
        vals: impl IntoIterator<Item = ValueOrExpression<'ctx, B>>,
        llvm: &Context<'ctx, B>,
    ) -> Value<'ctx, B> {
        match llvm.table[self.expr] {
            mu::ExpressionEnum::Abstract(_, e) => {
                let mut refs = self.bound;
                for val in vals {
                    refs.push_front(val.build(llvm));
                }
                llvm.build_expression(e, &refs)
            }
            _ => {
                let fval = self.build(llvm);
                llvm.build_call(fun, fval, vals)
            }
        }
    }
}

pub enum ValueOrExpression<'ctx, B: Builder<'ctx>> {
    Value(Value<'ctx, B>),
    Expression(Expression<'ctx, B>),
}

impl<'ctx, B: Builder<'ctx>> Clone for ValueOrExpression<'ctx, B> {
    fn clone(&self) -> Self {
        match self {
            Self::Value(arg0) => Self::Value(arg0.clone()),
            Self::Expression(arg0) => Self::Expression(arg0.clone()),
        }
    }
}

impl<'ctx, B: Builder<'ctx>> ValueOrExpression<'ctx, B> {
    pub fn build(self, llvm: &Context<'ctx, B>) -> Value<'ctx, B> {
        match self {
            ValueOrExpression::Value(value) => value,
            ValueOrExpression::Expression(expression) => expression.build(llvm),
        }
    }
    pub fn build_call(
        self,
        fun: mu::FunctionType,
        vals: impl IntoIterator<Item = ValueOrExpression<'ctx, B>>,
        llvm: &Context<'ctx, B>,
    ) -> Value<'ctx, B> {
        match self {
            ValueOrExpression::Value(value) => llvm.build_call(fun, value, vals),
            ValueOrExpression::Expression(expression) => expression.build_call(fun, vals, llvm),
        }
    }
}

impl<'ctx, B: Builder<'ctx>> From<Value<'ctx, B>> for ValueOrExpression<'ctx, B> {
    fn from(value: Value<'ctx, B>) -> Self {
        Self::Value(value)
    }
}

type ForeignFunctionCache<'ctx> = HashMap<String, FunctionValue<'ctx>>;
type ForeignGlobalCache<'ctx> = HashMap<String, GlobalValue<'ctx>>;
type CallableCache<'ctx, C> = HashMap<C, FunctionValue<'ctx>>;
type EnumCache<'ctx> = HashMap<mu::Enum, (Box<[Type<'ctx>]>, Enum<'ctx>)>;
type StructCache<'ctx> = HashMap<mu::Tuple, (Box<[Type<'ctx>]>, Option<StructType<'ctx>>)>;

#[derive(Clone, Copy, Debug)]
pub enum Enum<'ctx> {
    Empty,
    Units(IntType<'ctx>),
    Single(Option<BasicTypeEnum<'ctx>>),
    ZeroNiche(Option<BasicTypeEnum<'ctx>>, bool),
    TaggedUnion(StructType<'ctx>),
}

impl<'ctx> From<Enum<'ctx>> for Type<'ctx> {
    fn from(value: Enum<'ctx>) -> Self {
        Type::Data(match value {
            Enum::Empty => None,
            Enum::Units(repr) => Some(repr.into()),
            Enum::Single(repr) => repr,
            Enum::ZeroNiche(repr, _) => repr,
            Enum::TaggedUnion(repr) => Some(repr.into()),
        })
    }
}

pub struct Context<'ctx, B: Builder<'ctx>> {
    pub context: &'ctx inkwell::context::Context,
    pub table: &'ctx B::Table,
    pub base: B,
    pub module: inkwell::module::Module<'ctx>,
    pub builder: inkwell::builder::Builder<'ctx>,
    pub target_machine: TargetMachine,
    pub target_data: TargetData,

    linked: RwLock<HashSet<String>>,
    function: RwLock<Option<FunctionValue<'ctx>>>,
    structs: RwLock<StructCache<'ctx>>,
    enums: RwLock<EnumCache<'ctx>>,
    callables: RwLock<CallableCache<'ctx, B::Callable>>,
    foreign_functions: RwLock<ForeignFunctionCache<'ctx>>,
    foreign_globals: RwLock<ForeignGlobalCache<'ctx>>,
    // TODO: remove this from here
    syscalls: Box<[(FunctionType<'ctx>, PointerValue<'ctx>)]>,
}

impl<'ctx, B: Builder<'ctx>> Context<'ctx, B> {
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
        table: &'ctx B::Table,
        base: B,
        target_machine: TargetMachine,
        module_name: &str,
    ) -> Self {
        let target_data = target_machine.get_target_data();
        let ptr_int_t = context.ptr_sized_int_type(&target_data, None);
        Self {
            context,
            table,
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
            linked: RwLock::new(HashSet::new()),
            structs: RwLock::new(HashMap::new()),
            enums: RwLock::new(HashMap::new()),
            callables: RwLock::new(HashMap::new()),
            function: RwLock::new(None),
            foreign_functions: RwLock::new(HashMap::new()),
            foreign_globals: RwLock::new(HashMap::new()),
        }
    }
    pub fn take_linked(&mut self) -> HashSet<String> {
        std::mem::take(&mut self.linked).into_inner().unwrap()
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
    pub fn get_foreign_function(
        &self,
        lib: &str,
        name: &str,
        fun: mu::FunctionType,
    ) -> FunctionValue<'ctx> {
        let hash_map = self.foreign_functions.read().unwrap();
        if let Some(function) = hash_map.get(name).copied() {
            return function;
        }
        drop(hash_map);

        let ty = self.get_function_type(fun, false);
        let function = self.module.add_function(name, ty, Some(Linkage::External));

        // FIXME: add wasm-import-module attribute when on wasm

        self.linked.write().unwrap().insert(lib.to_string());
        self.foreign_functions
            .write()
            .unwrap()
            .insert(name.to_string(), function);
        function
    }
    pub fn get_foreign_global(&self, lib: &str, name: &str, ty: mu::Type) -> GlobalValue<'ctx> {
        let hash_map = self.foreign_globals.read().unwrap();
        if let Some(global) = hash_map.get(name).copied() {
            return global;
        }
        drop(hash_map);

        let ty = self.get_type(ty).basic_type(self).unwrap();
        let global = self.module.add_global(ty, None, name);
        global.set_linkage(Linkage::External);

        // FIXME: add wasm-import-module attribute when on wasm

        self.linked.write().unwrap().insert(lib.to_string());
        self.foreign_globals
            .write()
            .unwrap()
            .insert(name.to_string(), global);
        global
    }
    pub fn add_function(
        &self,
        fun: mu::FunctionType,
        closure_param: bool,
        name: Option<&str>,
        linkage: Option<Linkage>,
    ) -> FunctionValue<'ctx> {
        let function_type = self.get_function_type(fun, closure_param);
        let function = self.module.add_function(
            name.or_else(|| self.table.tuple_name(fun.from()).map(Deref::deref))
                .unwrap_or(""),
            function_type,
            linkage,
        );

        // set parameter names
        let params = Iterator::zip(
            self.function_arguments(fun, function)
                .map(|v| v.basic_value(self)),
            (0..self.table[fun.from()].len() as u32)
                .map(|index| self.table.tuple_field_name(fun.from(), index)),
        );
        for (param, name) in params.filter_map(|(a, b)| a.zip(b)) {
            param.set_name(name);
        }
        if closure_param {
            function.get_last_param().unwrap().set_name("closure");
        }

        // do not probe the stack
        // TODO: link with a library on windows that has a stack prober
        function.add_attribute(
            AttributeLoc::Function,
            self.context
                .create_string_attribute("no-stack-arg-probe", ""),
        );

        function
    }
    pub fn get_struct(&self, tys: mu::Tuple) -> Option<StructType<'ctx>> {
        let read = self.structs.read().unwrap();
        match read.get(&tys) {
            Some(&(_, s)) => s,
            None => {
                drop(read);

                // NOTE: recursive structs will cause a stack overflow here
                let fields = self.table[tys]
                    .iter()
                    .map(|&field| self.get_type(field))
                    .collect::<Box<_>>();
                let llvm_fields = fields
                    .iter()
                    .filter_map(|f| f.basic_type(self))
                    .collect::<Box<_>>();
                let struc = (!llvm_fields.is_empty()).then(|| match self.table.tuple_name(tys) {
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
        match self.table[ty] {
            mu::TypeEnum::Base(ref base) => B::has_zero_niche(base, self),
            mu::TypeEnum::Sum(tys) => match self.get_enum(tys) {
                Enum::Empty => true,
                Enum::Units(_) | Enum::ZeroNiche(_, _) => false,
                Enum::Single(_) | Enum::TaggedUnion(_) => self.has_zero_niche(self.table[tys][0]),
            },
            mu::TypeEnum::Product(tys) => self.table[tys]
                .iter()
                .any(|&field| self.has_zero_niche(field)),
            mu::TypeEnum::VTable(fs) => !self.table[fs].is_empty(),
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
                let variants = self.table[tys]
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
                let e = match self.table[tys] {
                    // no variants
                    [] => Enum::Empty,
                    // single variant
                    [_] => Enum::Single(variants[0].basic_type(self)),
                    // only unit variants
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
        match self.table[ty] {
            mu::TypeEnum::Base(ref base) => B::get_type(base, self),
            mu::TypeEnum::Product(tys) => Type::Data(self.get_struct(tys).map(Into::into)),
            mu::TypeEnum::Sum(tys) => self.get_enum(tys).into(),
            mu::TypeEnum::Function(function) => {
                Type::Function(self.get_function_type(function, true))
            }
            mu::TypeEnum::VTable(tys) => Type::VTable(
                self.table[tys]
                    .iter()
                    .map(|&t| {
                        let mu::TypeEnum::Function(function) = self.table[t] else {
                            panic!("ICE")
                        };
                        self.get_function_type(function, true)
                    })
                    .collect(),
            ),
        }
    }
    pub fn get_function_type(
        &self,
        function: mu::FunctionType,
        closure_param: bool,
    ) -> FunctionType<'ctx> {
        let mut param_types = self.table[function.from()]
            .iter()
            .filter_map(|&ty| self.get_type(ty).basic_type(self))
            .map(BasicMetadataTypeEnum::from)
            .collect::<Vec<_>>();
        let to = self.get_type(function.to()).basic_type(self);

        if closure_param {
            param_types.push(self.context.ptr_type(AddressSpace::default()).into());
        }

        match to {
            Some(t) => t.fn_type(&param_types, false),
            None => self.context.void_type().fn_type(&param_types, false),
        }
    }
    pub fn build_function(
        &self,
        fun: mu::FunctionType,
        val: FunctionValue<'ctx>,
        expression: mu::Expression,
    ) {
        self.builder
            .position_at_end(self.context.append_basic_block(val, ""));
        *self.function.write().unwrap() = Some(val);
        let mut refs = im::Vector::new();
        for arg in self.function_arguments(fun, val) {
            refs.push_front(arg);
        }
        let out = self.build_expression(expression, &refs).basic_value(self);
        if !fun.never_returns(self.table) {
            self.builder
                .build_return(
                    out.as_ref()
                        .map(|e| e as &dyn inkwell::values::BasicValue)
                        .filter(|_| val.get_type().get_return_type().is_some()),
                )
                .unwrap();
        } else {
            self.builder.build_unreachable().unwrap();
        }
        self.builder.clear_insertion_position();
        *self.function.write().unwrap() = None;
    }
    pub fn function_arguments(
        &self,
        fun: mu::FunctionType,
        val: FunctionValue<'ctx>,
    ) -> impl Iterator<Item = Value<'ctx, B>> {
        let mut nth = 0;
        self.table[fun.from()].iter().map(move |&t| {
            Value::Data(self.get_type(t).nonzero_sized().then(|| {
                let param = val.get_nth_param(nth).unwrap();
                nth += 1;
                param
            }))
        })
    }
    pub fn build_expression_bound(
        &self,
        e: mu::Expression,
        args: impl IntoIterator<Item = ValueOrExpression<'ctx, B>>,
    ) -> Value<'ctx, B> {
        let mut refs = im::Vector::new();
        for val in args {
            refs.push_front(val.build(self));
        }
        self.build_expression(e, &refs)
    }
    fn build_expression(
        &self,
        e: mu::Expression,
        refs: &im::Vector<Value<'ctx, B>>,
    ) -> Value<'ctx, B> {
        match self.table[e] {
            mu::ExpressionEnum::Operation(ref o) => B::build_operation(o, self),
            mu::ExpressionEnum::Reference(_, n) => refs[n as usize].clone(),
            mu::ExpressionEnum::Let(e1, e2) => {
                let mut refs_new = refs.clone();
                refs_new.push_front(self.build_expression(e1, refs));
                self.build_expression(e2, &refs_new)
            }
            mu::ExpressionEnum::Sequence(es, en) => {
                for &e in self.table[es].iter() {
                    let _ = self.build_expression(e, refs);
                }
                self.build_expression(en, refs)
            }
            mu::ExpressionEnum::Construct(types, expressions) => self.build_construct(
                types,
                self.table[expressions]
                    .iter()
                    .map(|&e| self.build_expression(e, refs)),
            ),
            mu::ExpressionEnum::ConstructVTable(_, es) => {
                let captures = Captures::get(self.table[es].iter().copied(), self, refs);
                Value::VTable(es, captures)
            }
            mu::ExpressionEnum::Apply(f, es) => {
                let fun = f
                    .get_type(self.table)
                    .unwrap()
                    .into_function(self.table)
                    .unwrap();
                let vals = self.table[es].iter().map(|&e| {
                    ValueOrExpression::Expression(Expression {
                        expr: e,
                        bound: refs.clone(),
                    })
                });
                Expression {
                    expr: f,
                    bound: refs.clone(),
                }
                .build_call(fun, vals, self)
            }
            mu::ExpressionEnum::Member(e, index) => {
                let val = self.build_expression(e, refs);
                match val {
                    Value::VTable(es, captures) => {
                        Value::Abstract(self.table[es][index as usize], captures)
                    }
                    _ => {
                        let types = e
                            .get_type(self.table)
                            .unwrap()
                            .into_product(self.table)
                            .unwrap();
                        self.build_member(types, index, val)
                    }
                }
            }
            mu::ExpressionEnum::Variant(variants, i, e) => {
                let variant = self.build_expression(e, refs);

                match self.get_enum(variants) {
                    Enum::Empty => panic!(),
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
                let sum = e
                    .get_type(self.table)
                    .unwrap()
                    .into_sum(self.table)
                    .unwrap();
                let variant = self.build_expression(e, refs);

                let out = self
                    .get_type(self.table[es][0].get_type(self.table).unwrap())
                    .basic_type(self);
                match self.get_enum(sum) {
                    Enum::Empty => Value::Data(None),
                    Enum::Units(int) => {
                        // TODO: simplify in the case of exactly 2 units

                        let else_block = self.build_block("");
                        let cases = (0..self.table[es].len() as u32)
                            .map(|n| {
                                (
                                    int.const_int(n.into(), false),
                                    self.build_block(
                                        self.table
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
                        for ((_, case), &e) in cases.into_iter().zip(&self.table[es]) {
                            self.builder.position_at_end(case);
                            let val = self.build_expression(e, &refs_new);
                            self.builder.build_unconditional_branch(end_block).unwrap();

                            if let Some(phi) = phi {
                                phi.add_incoming(&[(
                                    &val.basic_value(self).unwrap_or_else(|| {
                                        phi.as_basic_value().get_type().const_zero()
                                    }),
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
                        self.build_expression(self.table[es][0], &refs_new)
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
                            let then_val = self
                                .build_expression(self.table[es][zero_index as usize], &refs_new);
                            let then_end = self.builder.get_insert_block().unwrap();
                            self.builder.build_unconditional_branch(next_block).unwrap();

                            self.builder.position_at_end(else_block);
                            let mut refs_new = refs.clone();
                            refs_new.push_front(Value::Data(Some(v)));
                            let else_val = self.build_expression(
                                self.table[es][(!zero_index) as usize],
                                &refs_new,
                            );
                            let else_end = self.builder.get_insert_block().unwrap();
                            self.builder.build_unconditional_branch(next_block).unwrap();

                            self.builder.position_at_end(next_block);
                            Value::Data(out.map(|ty| {
                                let phi = self.builder.build_phi(ty, "").unwrap();
                                self.builder.position_at_end(then_block);
                                let then_val = then_val.basic_value(self).unwrap_or_else(|| {
                                    phi.as_basic_value().get_type().const_zero()
                                });
                                self.builder.position_at_end(else_block);
                                let else_val = else_val.basic_value(self).unwrap_or_else(|| {
                                    phi.as_basic_value().get_type().const_zero()
                                });
                                self.builder.position_at_end(next_block);
                                phi.add_incoming(&[(&then_val, then_end), (&else_val, else_end)]);
                                phi.as_basic_value()
                            }))
                        }
                        None => {
                            let mut refs_new = refs.clone();
                            refs_new.push_front(Value::Data(None));
                            self.build_expression(self.table[es][zero_index as usize], &refs_new)
                        }
                    },
                    Enum::TaggedUnion(_) => todo!(),
                }
            }
            mu::ExpressionEnum::Abstract(_, _) => {
                let captures = Captures::get(iter::once(e), self, refs);
                Value::Abstract(e, captures)
            }
            mu::ExpressionEnum::Try(ty, e) => {
                let next = self.build_block("");
                let phi = self.get_type(ty).basic_type(self).map(|ty| {
                    let current_block = self.builder.get_insert_block().unwrap();
                    self.builder.position_at_end(next);
                    let phi = self.builder.build_phi(ty, "").unwrap();
                    self.builder.position_at_end(current_block);
                    phi
                });

                let mut refs_new = refs.clone();
                refs_new.push_front(Value::Raise(
                    self.function.read().unwrap().unwrap(),
                    next,
                    phi,
                ));
                let val = self.build_expression(e, &refs_new);
                let old_block = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(next).unwrap();

                self.builder.position_at_end(next);
                if let Some(phi) = phi {
                    phi.add_incoming(&[(
                        &val.basic_value(self)
                            .unwrap_or_else(|| phi.as_basic_value().get_type().const_zero()),
                        old_block,
                    )]);
                }
                Value::Data(phi.map(PhiValue::as_basic_value))
            }
        }
    }
    fn build_abstract(&self, e: mu::Expression, closure: Closure<'ctx>) -> FunctionValue<'ctx> {
        let mu::ExpressionEnum::Abstract(from, body) = self.table[e] else {
            panic!("ICE");
        };

        let current_fun = {
            let guard = self.function.read().unwrap();
            guard.unwrap()
        };
        let current_block = self.builder.get_insert_block().unwrap();

        // create function
        let fun = mu::FunctionType::new(from, body.get_type(self.table).unwrap(), self.table);
        let function = self.add_function(fun, true, None, Some(Linkage::Private));
        self.builder
            .position_at_end(self.context.append_basic_block(function, ""));
        *self.function.write().unwrap() = Some(function);

        // build function
        let mut refs = closure.for_function(function, self).refs(self);
        for arg in self.function_arguments(fun, function) {
            refs.push_front(arg);
        }
        let out = self.build_expression(body, &refs).basic_value(self);
        if !fun.never_returns(self.table) {
            self.builder
                .build_return(
                    out.as_ref()
                        .map(|e| e as &dyn inkwell::values::BasicValue)
                        .filter(|_| function.get_type().get_return_type().is_some()),
                )
                .unwrap();
        } else {
            self.builder.build_unreachable().unwrap();
        }

        // return
        self.builder.position_at_end(current_block);
        *self.function.write().unwrap() = Some(current_fun);
        function
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
        let member_types = &self.table[types];
        let member = member_types[index as usize];
        val.basic_value(self).map_or(Value::Data(None), |data| {
            if data.is_array_value() {
                // vtable
                let table = self
                    .builder
                    .build_extract_value(data.into_array_value(), 0, "vtable pointer")
                    .unwrap()
                    .into_pointer_value();
                let closure = self
                    .builder
                    .build_extract_value(data.into_array_value(), 1, "vtable closure")
                    .unwrap()
                    .into_pointer_value();

                let ptr_type = self.context.ptr_type(AddressSpace::default());
                let ptr_types = iter::repeat_n(ptr_type.as_basic_type_enum(), member_types.len())
                    .collect::<Box<_>>();
                // TODO: named vtable type?
                let vtable_type = self.context.struct_type(&ptr_types, false);
                let function_ptr = self
                    .builder
                    .build_struct_gep(
                        vtable_type,
                        table,
                        index,
                        self.table
                            .tuple_field_name(types, index)
                            .map(Deref::deref)
                            .unwrap_or(""),
                    )
                    .unwrap();
                let function = self
                    .builder
                    .build_load(ptr_type, function_ptr, "")
                    .unwrap()
                    .into_pointer_value();

                Value::Function(function, Some(closure))
            } else {
                // product
                Value::Data(self.get_type(member).nonzero_sized().then(|| {
                    let nth = member_types[..index as usize]
                        .iter()
                        .filter(|&&member| self.get_type(member).nonzero_sized())
                        .count() as u32;
                    self.builder
                        .build_extract_value(
                            data.into_struct_value(),
                            nth,
                            self.table
                                .tuple_field_name(types, index)
                                .map(Deref::deref)
                                .unwrap_or(""),
                        )
                        .unwrap()
                }))
            }
        })
    }
    pub fn build_member_pointer(
        &self,
        types: mu::Tuple,
        index: u32,
        val: Value<'ctx, B>,
    ) -> Value<'ctx, B> {
        let member_types = &self.table[types];
        let member = member_types[index as usize];
        Value::Data(val.basic_value(self).and_then(|data| {
            self.get_type(member).nonzero_sized().then(|| {
                let pointee_ty = self
                    .get_type(self.table.insert_type(mu::TypeEnum::Product(types)))
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
                        self.table
                            .tuple_field_name(types, index)
                            .map(Deref::deref)
                            .unwrap_or(""),
                    )
                    .unwrap()
                    .into()
            })
        }))
    }
    pub fn build_construct(
        &self,
        types: mu::Tuple,
        members: impl IntoIterator<Item = Value<'ctx, B>>,
    ) -> Value<'ctx, B> {
        let members = members.into_iter().enumerate().filter_map(|(index, val)| {
            // any 'callable' will get turned into a small function
            val.basic_value(self).map(|v| {
                (
                    self.table
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
        fun: mu::FunctionType,
        fval: Value<'ctx, B>,
        vals: impl IntoIterator<Item = ValueOrExpression<'ctx, B>>,
    ) -> Value<'ctx, B> {
        match fval {
            Value::Data(data) => {
                self.build_indirect_call(fun, data, vals.into_iter().map(|v| v.build(self)))
            }
            Value::Abstract(e, captures) => {
                let mu::ExpressionEnum::Abstract(_, body) = self.table[e] else {
                    panic!("ICE");
                };
                let mut refs = captures.refs(self);
                for val in vals {
                    refs.push_front(val.build(self));
                }
                self.build_expression(body, &refs)
            }
            Value::Function(function, closure) => {
                let function_type = self.get_function_type(fun, true);
                let args = vals
                    .into_iter()
                    .filter_map(|v| v.build(self).basic_value(self))
                    .map(BasicMetadataValueEnum::from)
                    .chain(iter::once(
                        closure
                            .unwrap_or_else(|| {
                                self.context.ptr_type(AddressSpace::default()).get_poison()
                            })
                            .into(),
                    ))
                    .collect::<Box<_>>();
                let out = self
                    .builder
                    .build_indirect_call(function_type, function, &args, "")
                    .unwrap()
                    .try_as_basic_value()
                    .basic();
                Value::Data(out)
            }
            Value::VTable(_, _) => panic!("ICE"),
            Value::Callable(c) => B::build_callable(&c, vals, self),
            Value::Raise(f, block, phi) => {
                if self.current_function() == Some(f) {
                    let val = vals.into_iter().next().unwrap().build(self);
                    let current_block = self.builder.get_insert_block().unwrap();
                    self.builder.build_unconditional_branch(block).unwrap();
                    if let Some(phi) = phi {
                        phi.add_incoming(&[(
                            &val.basic_value(self)
                                .unwrap_or_else(|| phi.as_basic_value().get_type().const_zero()),
                            current_block,
                        )]);
                    }

                    let next = self.build_block("");
                    self.builder.position_at_end(next);
                    Value::Data(None)
                } else {
                    todo!()
                }
            }
        }
    }
    fn current_function(&self) -> Option<FunctionValue<'ctx>> {
        *self.function.read().unwrap()
    }
    pub fn build_direct_call(
        &self,
        fval: FunctionValue<'ctx>,
        vals: impl IntoIterator<Item = Value<'ctx, B>>,
    ) -> Value<'ctx, B> {
        let args = vals
            .into_iter()
            .filter_map(|v| v.basic_value(self))
            .map(BasicMetadataValueEnum::from)
            .collect::<Box<_>>();
        let out = self
            .builder
            .build_call(fval, &args, "")
            .unwrap()
            .try_as_basic_value()
            .basic();
        Value::Data(out)
    }
    pub fn build_indirect_call(
        &self,
        fun: mu::FunctionType,
        fval: BasicValue<'ctx>,
        vals: impl IntoIterator<Item = Value<'ctx, B>>,
    ) -> Value<'ctx, B> {
        let function_type = self.get_function_type(fun, true);
        let (fptr, closure) = self.get_closure(fval);
        let args = vals
            .into_iter()
            .filter_map(|v| v.basic_value(self))
            .map(BasicMetadataValueEnum::from)
            .chain(iter::once(closure.into()))
            .collect::<Box<_>>();
        let out = self
            .builder
            .build_indirect_call(function_type, fptr, &args, "")
            .unwrap()
            .try_as_basic_value()
            .basic();
        Value::Data(out)
    }
    pub fn build_block(&self, name: &str) -> BasicBlock<'ctx> {
        self.context
            .append_basic_block(self.function.read().unwrap().unwrap(), name)
    }
    pub fn build_functions_that_llvm_tries_to_call_for_some_reason(&self) {
        // memset
        let u8_ptr = self.context.ptr_type(AddressSpace::default());
        let uptr = self.context.ptr_sized_int_type(&self.target_data, None);

        let memset = self.module.add_function(
            "memset",
            u8_ptr.fn_type(
                &[
                    u8_ptr.into(),
                    self.context.i64_type().into(), // TODO: C int
                    uptr.into(),
                ],
                false,
            ),
            Some(Linkage::Internal),
        );

        let start = memset.get_nth_param(0).unwrap().into_pointer_value();
        let char = memset.get_nth_param(1).unwrap().into_int_value();
        let size = memset.get_nth_param(2).unwrap().into_int_value();

        let memset_entry = self.context.append_basic_block(memset, "");
        let memset_init = self.context.append_basic_block(memset, "init");
        let memset_loop = self.context.append_basic_block(memset, "loop");
        let memset_ret = self.context.append_basic_block(memset, "end");

        self.builder.position_at_end(memset_entry);
        let char = self
            .builder
            .build_int_truncate(char, self.context.i8_type(), "")
            .unwrap();
        let end = unsafe {
            self.builder
                .build_gep(self.context.i8_type(), start, &[size], "end")
                .unwrap()
        };
        self.builder
            .build_unconditional_branch(memset_init)
            .unwrap();

        self.builder.position_at_end(memset_init);
        let phi = self.builder.build_phi(u8_ptr, "current").unwrap();
        let current = phi.as_basic_value().into_pointer_value();
        let lhs = self.builder.build_ptr_to_int(current, uptr, "lhs").unwrap();
        let rhs = self.builder.build_ptr_to_int(end, uptr, "rhs").unwrap();
        let cmp = self
            .builder
            .build_int_compare(IntPredicate::EQ, lhs, rhs, "cmp")
            .unwrap();
        self.builder
            .build_conditional_branch(cmp, memset_ret, memset_loop)
            .unwrap();

        self.builder.position_at_end(memset_loop);
        self.builder.build_store(current, char).unwrap();
        let next = unsafe {
            self.builder
                .build_gep(
                    self.context.i8_type(),
                    current,
                    &[uptr.const_int(1, false)],
                    "next",
                )
                .unwrap()
        };
        phi.add_incoming(&[(&start, memset_entry), (&next, memset_loop)]);
        self.builder
            .build_unconditional_branch(memset_init)
            .unwrap();

        self.builder.position_at_end(memset_ret);
        self.builder.build_return(Some(&start)).unwrap();

        // tell the linker these are used
        let used_const = u8_ptr.const_array(&[
            // guard.as_pointer_value().const_cast(u8_ptr),
            // fail.as_global_value().as_pointer_value().const_cast(u8_ptr),
            memset
                .as_global_value()
                .as_pointer_value()
                .const_cast(u8_ptr),
        ]);

        let used = self
            .module
            .add_global(used_const.get_type(), None, "llvm.compiler.used");
        used.set_linkage(Linkage::Appending);
        used.set_section(Some("llvm.metadata"));
        used.set_initializer(&used_const);
    }
}
