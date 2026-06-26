#![cfg(feature = "llvm")]

use std::borrow::Cow;
use std::collections::HashMap;
use std::iter;
use std::path::Path;
use std::sync::{Arc, RwLock};

use compact_str::{CompactString, format_compact};
use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassBuilderOptions;
use inkwell::support::LLVMString;
use inkwell::targets::{
    FileType, InitializationConfig, Target, TargetData, TargetMachine, TargetMachineOptions,
};
use inkwell::types::{
    BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, IntType, PointerType, StructType,
};
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue, StructValue};
use inkwell::{AddressSpace, OptimizationLevel};

use crate::header::{ItemDecl, StructDecl};
use crate::ir::{ClosureParameter, Function, Handler, IR, Instruction, Next};
use crate::module;
use crate::pass::ModuleGraph;
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Constant, ConstantEnum, FunctionParameter, GenericArgument, IntSize, Integer, Type, TypeEnum,
    TypeTable,
};

struct Llvm<'ctx> {
    context: &'ctx Context,
    tt: &'ctx TypeTable,
    graph: &'ctx ModuleGraph,
    ir: &'ctx IR,

    module: Module<'ctx>,
    builder: Builder<'ctx>,
    target_machine: TargetMachine,
    target_data: TargetData,

    syscalls: Box<[(FunctionType<'ctx>, PointerValue<'ctx>)]>,
    structs: RwLock<HashMap<SpecializedStruct<'ctx>, Option<StructType<'ctx>>>>,
    functions: RwLock<HashMap<SpecializedCallable, FunctionValue<'ctx>>>,
}

#[derive(Hash, PartialEq, Eq)]
struct SpecializedStruct<'ctx> {
    module: &'ctx module::Module,
    name: &'ctx str,
    type_args: Arc<[GenericArgument]>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct SpecializedHandler {
    ir: Handler,
    type_args: Arc<[GenericArgument]>,
    closure_args: Arc<[Specialized]>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct SpecializedFunction {
    ir: Function,
    type_args: Arc<[GenericArgument]>,
    closure_args: Arc<[Specialized]>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct SpecializedCallable {
    function: SpecializedFunction,
    type_args: Arc<[GenericArgument]>,
    args: Arc<[Specialized]>,
    handlers: Arc<[Arc<[Value<SpecializedHandler>]>]>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum Specialized {
    Data(Value<Constant>),
    Lambda(Value<SpecializedFunction>),
    Effect(Arc<[Value<SpecializedHandler>]>),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
enum Value<T> {
    Specialized(T),
    Any,
    Unit,
}

impl SpecializedCallable {
    fn param_index(&self, idx: u32) -> Option<u32> {
        self.args[idx as usize].nonzero_sized().then(|| {
            let params = self
                .args
                .iter()
                .take(idx as usize)
                .filter(|s| s.nonzero_sized())
                .count();
            params as u32
        })
    }
    fn handler_index(&self, idx: u32) -> Option<u32> {
        self.handlers[idx as usize]
            .iter()
            .any(|h| h.nonzero_sized())
            .then(|| {
                let params = self.args.iter().filter(|s| s.nonzero_sized()).count();
                let handlers = self
                    .handlers
                    .iter()
                    .take(idx as usize)
                    .filter(|s| s.iter().any(|s| s.nonzero_sized()))
                    .count();
                (params + handlers) as u32
            })
    }
    fn closure_index(&self) -> u32 {
        let params = self.args.iter().filter(|s| s.nonzero_sized()).count();
        let handlers = self
            .handlers
            .iter()
            .filter(|s| s.iter().any(|s| s.nonzero_sized()))
            .count();
        (params + handlers) as u32
    }
    fn closure_param_index(&self, idx: u32) -> Option<u32> {
        self.function.closure_args[idx as usize]
            .nonzero_sized()
            .then(|| {
                let params = self
                    .function
                    .closure_args
                    .iter()
                    .take(idx as usize)
                    .filter(|s| s.nonzero_sized())
                    .count();
                params as u32
            })
    }
}

impl SpecializedFunction {
    fn has_closure(&self) -> bool {
        self.closure_args.iter().any(Specialized::nonzero_sized)
    }
}

impl SpecializedHandler {
    fn has_closure(&self) -> bool {
        self.closure_args.iter().any(Specialized::nonzero_sized)
    }
}

impl Value<SpecializedFunction> {
    fn nonzero_sized(&self) -> bool {
        match self {
            Value::Specialized(f) => f.has_closure(),
            Value::Any => true,
            Value::Unit => false,
        }
    }
}

impl Value<SpecializedHandler> {
    fn nonzero_sized(&self) -> bool {
        match self {
            Value::Specialized(h) => h.has_closure(),
            Value::Any => true,
            Value::Unit => false,
        }
    }
}

impl Value<Constant> {
    fn nonzero_sized(&self) -> bool {
        match self {
            Value::Specialized(_) => false,
            Value::Any => true,
            Value::Unit => false,
        }
    }
}

impl Specialized {
    fn nonzero_sized(&self) -> bool {
        match self {
            Specialized::Data(value) => value.nonzero_sized(),
            Specialized::Lambda(value) => value.nonzero_sized(),
            Specialized::Effect(value) => value.iter().any(|h| h.nonzero_sized()),
        }
    }
    fn as_data(&self) -> Value<Constant> {
        match self {
            Specialized::Data(value) => *value,
            _ => panic!(),
        }
    }
    fn as_lambda(&self) -> &Value<SpecializedFunction> {
        match self {
            Specialized::Lambda(mono_function) => mono_function,
            _ => panic!(),
        }
    }
    fn as_effect(&self) -> &[Value<SpecializedHandler>] {
        match self {
            Specialized::Effect(mono_handler) => mono_handler,
            _ => panic!(),
        }
    }
    fn reg<'ctx>(&self, value: Option<BasicValueEnum<'ctx>>) -> Reg<'ctx> {
        match self {
            Specialized::Data(_) => Reg::Data(value),
            Specialized::Lambda(Value::Any) => todo!(),
            Specialized::Lambda(Value::Unit) => todo!(),
            Specialized::Lambda(Value::Specialized(fun)) => {
                Reg::Lambda(fun.clone(), value.map(|v| v.into_pointer_value()))
            }
            Specialized::Effect(handlers) => Reg::Handlers(
                handlers
                    .iter()
                    .map(|v| match v {
                        Value::Specialized(handler) => handler.clone(),
                        Value::Any => todo!(),
                        Value::Unit => todo!(),
                    })
                    .collect(),
                value.map(|v| v.into_struct_value()),
            ),
        }
    }
}

#[derive(Clone)]
enum Reg<'ctx> {
    Data(Option<BasicValueEnum<'ctx>>),
    Lambda(SpecializedFunction, Option<PointerValue<'ctx>>),
    Handlers(Arc<[SpecializedHandler]>, Option<StructValue<'ctx>>),
}

impl<'ctx> Reg<'ctx> {
    fn as_data(&self) -> Option<BasicValueEnum<'ctx>> {
        match self {
            Reg::Data(basic_value_enum) => *basic_value_enum,
            _ => panic!(),
        }
    }
    fn as_lambda(&self) -> (&SpecializedFunction, Option<PointerValue<'ctx>>) {
        match self {
            Reg::Lambda(function_reg, pointer_value) => (function_reg, *pointer_value),
            _ => panic!(),
        }
    }
    fn as_handlers(&self) -> (&[SpecializedHandler], Option<StructValue<'ctx>>) {
        match self {
            Reg::Handlers(items, closures) => (items, *closures),
            _ => panic!(),
        }
    }
    fn value(&self) -> Option<BasicValueEnum<'ctx>> {
        match *self {
            Reg::Data(basic_value_enum) => basic_value_enum,
            Reg::Lambda(_, pointer_value) => pointer_value.map(Into::into),
            Reg::Handlers(_, closures) => closures.map(Into::into),
        }
    }
    fn specialization(&self) -> Specialized {
        match self {
            Reg::Data(None) => Specialized::Data(Value::Unit),
            Reg::Data(Some(_)) => Specialized::Data(Value::Any),
            Reg::Lambda(fun, _) => Specialized::Lambda(Value::Specialized(fun.clone())),
            Reg::Handlers(items, _) => Specialized::Effect(
                items
                    .iter()
                    .map(|h| Value::Specialized(h.clone()))
                    .collect(),
            ),
        }
    }
}

impl<'ctx> Llvm<'ctx> {
    fn new(
        context: &'ctx Context,
        tt: &'ctx TypeTable,
        graph: &'ctx ModuleGraph,
        ir: &'ctx IR,
        target_machine: TargetMachine,
    ) -> Self {
        let target_data = target_machine.get_target_data();
        let ptr_int_t = context.ptr_sized_int_type(&target_data, None);
        Self {
            context,
            tt,
            graph,
            ir,
            module: context.create_module("main"),
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
            functions: RwLock::new(HashMap::new()),
        }
    }
    fn get_closure_type(&self, f: &SpecializedFunction) -> Option<StructType<'ctx>> {
        let fields = Iterator::zip(self.ir[f.ir].closure.iter(), f.closure_args.iter())
            .filter_map(|(param, spec)| match param {
                ClosureParameter::Data(ty) if spec.as_data().nonzero_sized() => {
                    Some(self.get_type(*ty).unwrap())
                }
                ClosureParameter::Data(_) => None,
                ClosureParameter::Lambda(_) => match spec.as_lambda() {
                    Value::Specialized(f) => f.has_closure().then(|| self.ptr_t().into()),
                    Value::Any => todo!(),
                    Value::Unit => todo!(),
                },
                ClosureParameter::Effect(_) => {
                    let fields = spec
                        .as_effect()
                        .iter()
                        .filter_map(|handler| match handler {
                            Value::Specialized(h) => {
                                h.has_closure().then(|| self.ptr_t().as_basic_type_enum())
                            }
                            Value::Any => todo!(),
                            Value::Unit => todo!(),
                        })
                        .collect::<Box<_>>();
                    (!fields.is_empty()).then(|| self.context.struct_type(&fields, false).into())
                }
            })
            .collect::<Box<_>>();
        (!fields.is_empty()).then(|| self.context.struct_type(&fields, false))
    }
    fn build_closure(
        &self,
        values: impl IntoIterator<Item = Option<BasicValueEnum<'ctx>>>,
    ) -> Option<StructValue<'ctx>> {
        let values = values.into_iter().flatten().collect::<Box<_>>();
        (!values.is_empty()).then(|| {
            let types = values.iter().map(|v| v.get_type()).collect::<Box<_>>();
            let struct_t = self.context.struct_type(&types, false);
            let mut closure = struct_t.get_undef();
            for (i, val) in values.into_iter().enumerate() {
                closure = self
                    .builder
                    .build_insert_value(closure, val, i as u32, "")
                    .unwrap()
                    .into_struct_value();
            }
            closure
        })
    }
    fn get_global_str(
        &self,
        str: &'ctx str,
        sentinel: Option<char>,
        elem_ty: Type,
        name: &str,
    ) -> Option<(PointerValue<'ctx>, IntValue<'ctx>)> {
        // TODO: do some interning

        // TODO: support for u32 elements
        assert!(elem_ty.is_u8(self.tt));

        if str.is_empty() && sentinel.is_none() {
            return None;
        }

        let str_with_sentinel = match sentinel {
            Some('\0') | None => Cow::from(str),
            Some(sentinel) => Cow::from(format!("{}{}", str, sentinel)),
        };

        let const_str = self
            .context
            .const_string(str_with_sentinel.as_bytes(), sentinel == Some('\0'));
        let global_str = self.module.add_global(const_str.get_type(), None, name);
        global_str.set_linkage(Linkage::Internal);
        global_str.set_constant(true);
        global_str.set_initializer(&const_str);

        let size = self.int_index_t().const_int(str.len() as u64, false);
        Some((global_str.as_pointer_value(), size))
    }
    fn build_function(&self, callable: SpecializedCallable, queue: &mut Vec<SpecializedCallable>) {
        let Some(fun) = self.functions.read().unwrap().get(&callable).copied() else {
            return;
        };
        let ir = &self.ir[callable.function.ir];

        // do not probe the stack
        // TODO: link with a library on windows that has a stack prober
        fun.add_attribute(
            AttributeLoc::Function,
            self.context
                .create_string_attribute("no-stack-arg-probe", ""),
        );

        let blocks = (0..ir.blocks.len())
            .map(|idx| {
                self.context
                    .append_basic_block(fun, &format_compact!("L{}", idx))
            })
            .collect::<Box<_>>();
        let mut regs = Vec::<Reg<'ctx>>::new();

        let closure_ty = self.get_closure_type(&callable.function);
        let closure_idx = callable.closure_index();

        for (basic_block, block) in Iterator::zip(blocks.iter().copied(), ir.blocks.iter()) {
            self.builder.position_at_end(basic_block);

            for &(ty, ref instr) in &block.instructions {
                let reg = match instr {
                    Instruction::Parameter(n) => {
                        let value = callable
                            .param_index(*n)
                            .map(|n| fun.get_nth_param(n).unwrap());
                        callable.args[*n as usize].reg(value)
                    }
                    Instruction::ClosureParameter(n) => {
                        let value = Option::zip(closure_ty, callable.closure_param_index(*n)).map(
                            |(closure_ty, elem)| {
                                let closure_ptr =
                                    fun.get_nth_param(closure_idx).unwrap().into_pointer_value();
                                let elem_ptr = self
                                    .builder
                                    .build_struct_gep::<BasicTypeEnum>(
                                        closure_ty.into(),
                                        closure_ptr,
                                        elem,
                                        "",
                                    )
                                    .unwrap();
                                self.builder
                                    .build_load(self.get_type(ty).unwrap(), elem_ptr, "")
                                    .unwrap()
                            },
                        );
                        callable.function.closure_args[*n as usize].reg(value)
                    }
                    Instruction::FunctionTop { module, name } => {
                        let function =
                            self.ir.function_map.read().unwrap()[&(module.clone(), name.clone())];
                        Reg::Lambda(
                            SpecializedFunction {
                                ir: function,
                                type_args: Arc::new([]),
                                closure_args: Arc::new([]),
                            },
                            None,
                        )
                    }
                    Instruction::FunctionNew {
                        function,
                        type_args,
                        closure_args,
                    } => {
                        let closure = self
                            .build_closure(closure_args.iter().map(|n| regs[*n as usize].value()));
                        let closure_ptr = closure.map(|closure| {
                            let ptr = self.builder.build_alloca(closure.get_type(), "").unwrap();
                            self.builder.build_store(ptr, closure).unwrap();
                            ptr
                        });
                        Reg::Lambda(
                            SpecializedFunction {
                                ir: *function,
                                type_args: type_args.clone(),
                                closure_args: closure_args
                                    .iter()
                                    .map(|n| regs[*n as usize].specialization())
                                    .collect(),
                            },
                            closure_ptr,
                        )
                    }
                    Instruction::FunctionHandler {
                        effect,
                        handler,
                        function,
                    } => {
                        let (handlers, closures) = regs[*effect as usize].as_handlers();
                        let closure_ptr = handlers[*handler as usize].has_closure().then(|| {
                            let index = handlers
                                .iter()
                                .take(*handler as usize)
                                .filter(|h| h.has_closure())
                                .count() as u32;
                            self.builder
                                .build_extract_value(closures.unwrap(), index, "")
                                .unwrap()
                                .into_pointer_value()
                        });
                        let handler = &handlers[*handler as usize];
                        Reg::Lambda(
                            SpecializedFunction {
                                ir: self.ir[handler.ir].functions[*function as usize],
                                type_args: handler.type_args.clone(),
                                closure_args: handler.closure_args.clone(),
                            },
                            closure_ptr,
                        )
                    }
                    Instruction::EffectParameter(n) => {
                        let value = callable
                            .handler_index(*n)
                            .map(|n| fun.get_nth_param(n).unwrap().into_struct_value());
                        let handlers = &callable.handlers[*n as usize];
                        Reg::Handlers(
                            handlers
                                .iter()
                                .map(|h| match h {
                                    Value::Specialized(h) => h.clone(),
                                    Value::Any => todo!(),
                                    Value::Unit => todo!(),
                                })
                                .collect(),
                            value,
                        )
                    }
                    Instruction::HandlerTop {
                        module,
                        handler,
                        type_args,
                    } => {
                        let handler =
                            self.ir.handler_map.read().unwrap()[&(module.clone(), *handler)];
                        Reg::Handlers(
                            Arc::new([SpecializedHandler {
                                ir: handler,
                                type_args: type_args.clone(),
                                closure_args: Arc::new([]),
                            }]),
                            None,
                        )
                    }
                    Instruction::HandlerNew {
                        handler,
                        type_args,
                        closure_args,
                    } => {
                        let closure = self
                            .build_closure(closure_args.iter().map(|s| regs[*s as usize].value()));
                        let closures = closure.map(|closure| {
                            let ptr = self.builder.build_alloca(closure.get_type(), "").unwrap();
                            self.builder.build_store(ptr, closure).unwrap();
                            let closures = self
                                .context
                                .struct_type(&[self.ptr_t().into()], false)
                                .get_undef();
                            self.builder
                                .build_insert_value(closures, ptr, 0, "")
                                .unwrap()
                                .into_struct_value()
                        });
                        Reg::Handlers(
                            Arc::new([SpecializedHandler {
                                ir: *handler,
                                type_args: type_args.clone(),
                                closure_args: closure_args
                                    .iter()
                                    .map(|n| regs[*n as usize].specialization())
                                    .collect(),
                            }]),
                            closures,
                        )
                    }
                    Instruction::Local(value) => {
                        Reg::Data(regs[*value as usize].as_data().map(|val| {
                            let local = self
                                .builder
                                .build_alloca(self.get_type(ty).unwrap(), "")
                                .unwrap();
                            self.builder.build_store(local, val).unwrap();
                            local.into()
                        }))
                    }
                    Instruction::Syscall { nr, args } => {
                        let (ty, ptr) = self.syscalls[args.len()];
                        Reg::Data(Some(
                            self.builder
                                .build_indirect_call(
                                    ty,
                                    ptr,
                                    &iter::once(nr)
                                        .chain(args.iter())
                                        .map(|n| {
                                            let v = regs[*n as usize].as_data().unwrap();
                                            if v.is_pointer_value() {
                                                self.builder
                                                    .build_ptr_to_int(
                                                        v.into_pointer_value(),
                                                        self.int_addr_t(),
                                                        "",
                                                    )
                                                    .unwrap()
                                                    .into()
                                            } else {
                                                v.into()
                                            }
                                        })
                                        .collect::<Box<_>>(),
                                    "",
                                )
                                .unwrap()
                                .try_as_basic_value()
                                .unwrap_basic(),
                        ))
                    }
                    Instruction::BinOp { lhs, op, rhs } => todo!(),
                    Instruction::UnOp { op, rhs } => todo!(),
                    Instruction::Index { array, index } => {
                        let index = regs[*index as usize].as_data().unwrap().into_int_value();
                        Reg::Data(regs[*array as usize].as_data().and_then(|array_value| {
                            match self.tt[ir.type_of(*array)] {
                                TypeEnum::PointerSlice(inner, _, None) => {
                                    self.get_type(inner).map(|inner_ty| {
                                        let ptr = self
                                            .builder
                                            .build_extract_value(
                                                array_value.into_struct_value(),
                                                0,
                                                "",
                                            )
                                            .unwrap()
                                            .into_pointer_value();
                                        unsafe {
                                            self.builder
                                                .build_in_bounds_gep(inner_ty, ptr, &[index], "")
                                                .unwrap()
                                                .into()
                                        }
                                    })
                                }
                                TypeEnum::PointerSlice(inner, _, Some(_)) => todo!(),
                                TypeEnum::Array(inner, _, _) => todo!(),
                                _ => unreachable!(),
                            }
                        }))
                    }
                    Instruction::IndexRange { array, from, to } => todo!(),
                    Instruction::Constant(constant) => Reg::Data(match self.tt[*constant] {
                        ConstantEnum::Generic(_) => todo!(),
                        ConstantEnum::True => {
                            Some(self.context.bool_type().const_int(1, false).into())
                        }
                        ConstantEnum::False => Some(self.context.bool_type().const_zero().into()),
                        ConstantEnum::Integer(i) => match self.tt[ty] {
                            TypeEnum::Integer(integer) => self
                                .get_int_type(integer)
                                .map(|n| n.const_int(i, false).into()),
                            _ => unreachable!(),
                        },
                        ConstantEnum::String(ref str) => match self.tt[ty] {
                            TypeEnum::PointerSlice(inner, _, sentinel) => Some(
                                self.get_global_str(str, sentinel.map(|_| '\0'), inner, "")
                                    .map(|(global, size)| match sentinel {
                                        Some(_) => global.into(),
                                        None => {
                                            let mut slice = self.slice_t().get_undef();
                                            slice = self
                                                .builder
                                                .build_insert_value(slice, global, 0, "")
                                                .unwrap()
                                                .into_struct_value();
                                            slice = self
                                                .builder
                                                .build_insert_value(slice, size, 1, "")
                                                .unwrap()
                                                .into_struct_value();
                                            slice.into()
                                        }
                                    })
                                    .unwrap_or_else(|| self.empty_slice().into()),
                            ),
                            TypeEnum::Array(inner, _, sentinel) => self
                                .get_global_str(str, sentinel.map(|_| '\0'), inner, "")
                                .map(|(global, _)| {
                                    self.builder
                                        .build_load(self.get_type(ty).unwrap(), global, "")
                                        .unwrap()
                                }),
                            _ => unreachable!(),
                        },
                        ConstantEnum::Character(ref str) => {
                            let char = str.chars().next().unwrap();
                            match self.tt[ty] {
                                TypeEnum::Integer(int) => self
                                    .get_int_type(int)
                                    .map(|ty| ty.const_int(char as u64, false).into()),
                                _ => unreachable!(),
                            }
                        }
                        ConstantEnum::Zero => self.get_type(ty).map(|ty| ty.const_zero()),
                    }),
                    Instruction::Uninit => Reg::Data(self.get_type(ty).map(|ty| match ty {
                        BasicTypeEnum::ArrayType(array_type) => array_type.get_undef().into(),
                        BasicTypeEnum::FloatType(float_type) => float_type.get_undef().into(),
                        BasicTypeEnum::IntType(int_type) => int_type.get_undef().into(),
                        BasicTypeEnum::PointerType(pointer_type) => pointer_type.get_undef().into(),
                        BasicTypeEnum::StructType(struct_type) => struct_type.get_undef().into(),
                        BasicTypeEnum::VectorType(vector_type) => vector_type.get_undef().into(),
                        BasicTypeEnum::ScalableVectorType(scalable_vector_type) => {
                            scalable_vector_type.get_undef().into()
                        }
                    })),
                    Instruction::Truncate(_) => todo!(),
                    Instruction::Extend(_) => todo!(),
                    Instruction::Transmute(_) => todo!(),
                    Instruction::If { condition, block } => todo!(),
                    Instruction::Load { address } => {
                        Reg::Data(regs[*address as usize].as_data().map(|ptr| {
                            self.builder
                                .build_load(
                                    self.get_type(ty).unwrap(),
                                    ptr.into_pointer_value(),
                                    "",
                                )
                                .unwrap()
                        }))
                    }
                    Instruction::Store { address, value } => {
                        if let (Some(addr), Some(value)) = (
                            regs[*address as usize].as_data(),
                            regs[*value as usize].as_data(),
                        ) {
                            self.builder
                                .build_store(addr.into_pointer_value(), value)
                                .unwrap();
                        }
                        Reg::Data(None)
                    }
                    Instruction::Array(items) => {
                        let (inner, sentinel) = match self.tt[ty] {
                            TypeEnum::Array(ty, _, sentinel) => (ty, sentinel),
                            _ => unreachable!(),
                        };
                        Reg::Data(self.get_type(inner).map(|ty| {
                            let items = items
                                .iter()
                                .map(|elem| regs[*elem as usize].as_data().unwrap())
                                .chain(sentinel.map(|_| ty.const_zero()))
                                .collect::<Box<_>>();
                            let mut array = ty.array_type(items.len() as u32).get_undef();
                            for (i, item) in items.into_iter().enumerate() {
                                array = self
                                    .builder
                                    .build_insert_value(array, item, i as u32, "")
                                    .unwrap()
                                    .into_array_value();
                            }
                            array.into()
                        }))
                    }
                    Instruction::Call {
                        function,
                        type_args,
                        args,
                        effects,
                    } => todo!(),
                    Instruction::Alloca => todo!(),
                    Instruction::ArrayAlloca(_) => todo!(),
                };
                regs.push(reg);
            }
            match block.next {
                Next::Block(block) => self
                    .builder
                    .build_unconditional_branch(blocks[block as usize])
                    .unwrap(),
                Next::Return(_) => todo!(),
                Next::Unreachable => self.builder.build_unreachable().unwrap(),
            };
        }
    }
    fn get_function(
        &self,
        callable: SpecializedCallable,
        queue: &mut Vec<SpecializedCallable>,
        linkage: Linkage,
    ) -> FunctionValue<'ctx> {
        if let Some(fn_value) = self.functions.read().unwrap().get(&callable).copied() {
            return fn_value;
        }

        let ir = &self.ir[callable.function.ir];
        let sig = ir
            .sig
            .subst(self.tt, 0, &callable.function.type_args)
            .apply(self.tt, &callable.type_args);

        let params = Iterator::zip(
            self.tt[sig].params.iter().flat_map(|p| p.iter()).copied(),
            callable.args.iter(),
        )
        .filter_map(|(param, mono)| match param {
            FunctionParameter::Data(ty) => mono.nonzero_sized().then(|| self.get_type(ty).unwrap()),
            FunctionParameter::Lambda(_) => match mono.as_lambda() {
                Value::Specialized(fun_mono) => fun_mono.has_closure().then(|| self.ptr_t().into()),
                Value::Any => todo!("function pointer"),
                Value::Unit => todo!("canonical function for signature"),
            },
        });

        let effects = callable.handlers.iter().filter_map(|handlers| {
            let fields = handlers
                .iter()
                .filter_map(|handler| match handler {
                    Value::Specialized(h) => {
                        h.has_closure().then(|| self.ptr_t().as_basic_type_enum())
                    }
                    Value::Any => todo!("handler pointer"),
                    Value::Unit => todo!("canonical handler for effect"),
                })
                .collect::<Box<_>>();
            (!fields.is_empty()).then(|| self.context.struct_type(&fields, false).into())
        });

        let closure = callable.function.has_closure().then(|| self.ptr_t().into());

        let inputs = params
            .chain(effects)
            .chain(closure)
            .map(Into::into)
            .collect::<Box<_>>();
        let fn_type = match self.get_type(self.tt[sig].thunk.returns) {
            Some(ty) => ty.fn_type(&inputs, false),
            None => self.context.void_type().fn_type(&inputs, false),
        };

        let fn_value = self.module.add_function(&ir.name, fn_type, Some(linkage));
        self.functions
            .write()
            .unwrap()
            .insert(callable.clone(), fn_value);
        queue.push(callable);
        fn_value
    }
    fn new_struct(&self, name: &str) -> StructType<'ctx> {
        self.context.opaque_struct_type(name)
    }
    fn fill_struct(&self, ty: StructType<'ctx>, decl: &StructDecl) {
        let fields = decl
            .members
            .iter()
            .filter_map(|mem| self.get_type(mem.ty))
            .collect::<Box<_>>();
        ty.set_body(&fields, false);
    }
    fn int_addr_t(&self) -> IntType<'ctx> {
        self.context.ptr_sized_int_type(&self.target_data, None)
    }
    fn int_index_t(&self) -> IntType<'ctx> {
        // TODO
        self.int_addr_t()
    }
    fn int_reg_t(&self) -> IntType<'ctx> {
        // TODO
        self.context.i64_type()
    }
    fn ptr_t(&self) -> PointerType<'ctx> {
        self.context.ptr_type(AddressSpace::default())
    }
    fn slice_t(&self) -> StructType<'ctx> {
        self.context
            .struct_type(&[self.ptr_t().into(), self.int_index_t().into()], false)
    }
    fn empty_slice(&self) -> StructValue<'ctx> {
        self.slice_t().const_zero()
    }
    fn get_int_type(&self, i: Integer) -> Option<IntType<'ctx>> {
        match i {
            Integer::Integer(_, int_size) => match int_size {
                IntSize::Exact(0) => None,
                IntSize::Exact(n) => Some(self.context.custom_width_int_type(n)),
                IntSize::Index => Some(self.int_index_t()),
                IntSize::Address => Some(self.int_addr_t()),
                IntSize::Register => Some(self.int_reg_t()),
                IntSize::CChar => todo!(),
                IntSize::CShort => todo!(),
                IntSize::CInt => todo!(),
                IntSize::CLong => todo!(),
                IntSize::CLongLong => todo!(),
            },
            Integer::CChar => todo!(),
        }
    }
    fn get_type(&self, ty: Type) -> Option<BasicTypeEnum<'ctx>> {
        match &self.tt[ty] {
            TypeEnum::Generic(_) => todo!(),
            TypeEnum::Item(item) => {
                // TODO: translate apply
                let key = SpecializedStruct {
                    module: &item.module,
                    name: &item.name,
                    type_args: item.apply.clone().unwrap_or_default(),
                };
                match self.structs.read().unwrap().get(&key).copied() {
                    Some(Some(s)) => Some(s.into()),
                    Some(None) => None,
                    None => {
                        // TODO: do not make a new struct if zero-sized

                        let s = self.new_struct(&format_compact!("{}.{}", item.module, item.name));
                        self.structs.write().unwrap().insert(key, Some(s));

                        // TODO: perform apply
                        let decl = match self
                            .graph
                            .stages(&item.module)
                            .expect("ICE: no stage")
                            .header(self.graph, self.tt)
                            .expect("ICE: no header")
                            .get(&item.name)
                        {
                            Some(ItemDecl::Struct(_, decl)) => {
                                decl.get().expect("ICE: no struct def")
                            }
                            _ => panic!("ICE: no struct"),
                        };
                        self.fill_struct(s, decl);

                        Some(s.into())
                    }
                }
            }
            TypeEnum::Integer(n) => self.get_int_type(*n).map(Into::into),
            TypeEnum::Boolean => Some(self.context.bool_type().into()),
            TypeEnum::Unit | TypeEnum::Never => None,
            TypeEnum::Pointer(_, _) | TypeEnum::PointerSlice(_, _, Some(_)) => {
                Some(self.ptr_t().into())
            }
            TypeEnum::PointerSlice(_, _, None) => Some(self.slice_t().into()),
            TypeEnum::Array(inner, size, sentinel) => match self.get_type(*inner) {
                None => None,
                Some(inner) => match &self.tt[*size] {
                    ConstantEnum::Generic(_) => todo!(),
                    ConstantEnum::Zero | ConstantEnum::Integer(0) if sentinel.is_none() => None,
                    ConstantEnum::Integer(n) => {
                        match u32::try_from(*n + sentinel.map(|_| 1).unwrap_or(0)) {
                            Ok(n) => Some(inner.array_type(n).into()),
                            Err(_) => panic!("ICE: array size too big"),
                        }
                    }
                    _ => panic!("ICE: array size is not an integer constant"),
                },
            },
        }
    }
    fn eprint(&self) {
        self.module.print_to_stderr();
        eprintln!();
    }
    fn verify(&self) -> Result<(), LLVMString> {
        self.module.verify()
    }
    fn optimize(&self) -> Result<(), LLVMString> {
        let opts = PassBuilderOptions::create();
        self.module
            .run_passes("default<O3>", &self.target_machine, opts)
    }
    fn write_asm(&self, path: &Path) {
        self.target_machine
            .write_to_file(&self.module, FileType::Assembly, path)
            .unwrap();
    }
    fn write_object(&self, path: &Path) {
        self.target_machine
            .write_to_file(&self.module, FileType::Object, path)
            .unwrap();
    }
}

pub fn export(
    tt: &TypeTable,
    graph: &ModuleGraph,
    ir: &IR,
    path: &Path,
    debug: bool,
    entry_module: &module::Module,
) {
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
    let llvm = Llvm::new(&context, tt, graph, ir, machine);

    let mut queue = Vec::new();
    let fun = llvm.get_function(
        SpecializedCallable {
            function: SpecializedFunction {
                ir: *ir
                    .function_map
                    .read()
                    .unwrap()
                    .get(&(entry_module.clone(), CompactString::const_new("_start")))
                    .unwrap(),
                type_args: Arc::new([]),
                closure_args: Arc::new([]),
            },
            type_args: Arc::new([]),
            args: Arc::new([]),
            handlers: Arc::new([]),
        },
        &mut queue,
        Linkage::External,
    );
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

    while let Some(next) = queue.pop() {
        llvm.build_function(next, &mut queue);
    }

    if debug {
        llvm.eprint();
    }

    llvm.verify().unwrap();
    llvm.optimize().unwrap();

    if debug {
        llvm.eprint();
    }

    llvm.write_asm(&path.with_extension("asm"));
    llvm.write_object(path);
}
