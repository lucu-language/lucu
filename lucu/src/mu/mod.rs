use std::iter;

use compact_str::CompactString;

use crate::ast;
use crate::type_table::Integer;

pub mod table;
pub use mu::*;

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Base {
    Integer(Integer),
    /// ^a
    Pointer(mu::Type),
    /// *a
    MultiPointer(mu::Type),
    /// ^[]a
    PointerSlice(mu::Type),
    /// [N]a
    Array(mu::Type, u32),
}

impl Base {
    pub const I8: Self = Self::Integer(Integer::I8);
    pub const INT: Self = Self::Integer(Integer::INT);
    pub const SIZE: Self = Self::Integer(Integer::SIZE);
    pub const ADDR: Self = Self::Integer(Integer::ADDR);
}

pub enum Constant {
    Integer(u64),
    Zero,
    Uninit,
    String(CompactString),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Item {
    pub module: crate::module::Module,
    pub item: CompactString,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Linkage {
    Internal,
    External,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Function {
    pub item: Item,
    pub ty: mu::FunctionType,
    pub body: mu::Expression,
    pub linkage: Option<Linkage>,
}

#[derive(Debug)]
pub struct Module {
    pub functions: Box<[Function]>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Callable {
    /// ? -> ?
    ModuleFunction { item: Item, ty: mu::FunctionType },
    /// (a x a x a x ...) -> [N]a
    ArrayConstruct { ty: mu::Type, size: u32 },
    /// a -> b
    Asm {
        assembly: CompactString,
        constraints: CompactString,
        side_effects: bool,
        from: mu::Type,
        to: mu::Type,
    },
    /// (() -> ()) -> !
    Loop,

    /// a -> b
    Cast {
        from: mu::Type,
        to: mu::Type,
        op: ast::Cast,
    },
    /// a -> a
    UnOp { ty: mu::Type, op: ast::UnOp },
    /// (a x a) -> bool
    PredicateOp { ty: mu::Type, op: ast::PredicateOp },
    /// (a x a) -> a
    MathOp { ty: mu::Type, op: ast::MathOp },
    // TODO: inline assembly
    /// (UPtr x UPtr x UPtr x ...) -> UPtr
    Syscall { args: u8 },

    /// (a x (^a -> b)) -> b
    LetReference { ty: mu::Type, to: mu::Type },
    /// (USize x (^[]a -> b)) -> b
    LetAlloca { ty: mu::Type, to: mu::Type },
    /// ^a -> a
    Read { ty: mu::Type },
    /// (^a x a) -> ()
    Write { ty: mu::Type },
    /// ^a -> ^b
    PointerMember { tys: mu::Tuple, member: u32 },

    /// ([N]a x USize) -> a
    ArrayIndex { ty: mu::Type, size: u32 },
    /// (^[N]a x USize) -> ^a
    PointerArrayIndex { ty: mu::Type, size: u32 },
    /// (^[]a x USize) -> ^a
    PointerSliceIndex { ty: mu::Type },
    /// Unsafe operation:
    /// (*a x USize) -> ^a
    MultiPointerIndex { ty: mu::Type },

    /// (^[N]a x USize x USize) -> ^[]a
    PointerArraySlice { ty: mu::Type, size: u32 },
    /// (^[]a x USize x USize) -> ^[]a
    PointerSliceSlice { ty: mu::Type },
    /// Unsafe operation:
    /// (*a x USize x USize) -> ^[]a
    MultiPointerSlice { ty: mu::Type },

    /// ^[]a -> USize
    Len { ty: mu::Type },
}

pub enum Operation {
    Unreachable,
    Constant(mu::Type, Constant),
    Callable(Callable),
}

impl mu::Typed for Callable {
    type Base = Base;
    fn get_type(&self, mt: &(impl mu::Table<Base = Self::Base> + ?Sized)) -> mu::Type {
        match *self {
            Callable::ModuleFunction { ty, .. } => mt.insert_type(mu::TypeEnum::Function(ty)),
            Callable::ArrayConstruct { ty, size } => {
                let arr = mt.base(Base::Array(ty, size));
                mt.function(mt.insert_tuple(iter::repeat_n(ty, size as usize)), arr)
            }
            Callable::Asm { from, to, .. } => mt.function(mt.insert_tuple([from]), to),
            Callable::Loop => mt.function(
                mt.insert_tuple([mt.function(mt.insert_tuple([]), mt.unit())]),
                mt.never(),
            ),
            Callable::Cast { from, to, .. } => mt.function(mt.insert_tuple([from]), to),
            Callable::UnOp { ty, .. } => mt.function(mt.insert_tuple([ty]), ty),
            Callable::PredicateOp { ty, .. } => mt.function(mt.insert_tuple([ty, ty]), mt.bool()),
            Callable::MathOp { ty, .. } => mt.function(mt.insert_tuple([ty, ty]), ty),
            Callable::Syscall { args } => {
                let uptr = mt.base(Base::ADDR);
                mt.function(
                    mt.insert_tuple(iter::repeat_n(uptr, args as usize + 1)),
                    uptr,
                )
            }
            Callable::LetReference { ty, to } => {
                let ptr = mt.base(Base::Pointer(ty));
                let fun = mt.function(mt.insert_tuple([ptr]), to);
                mt.function(mt.insert_tuple([ty, fun]), to)
            }
            Callable::LetAlloca { ty, to } => {
                let usize = mt.base(Base::SIZE);
                let ptr_slice = mt.base(Base::PointerSlice(ty));
                let fun = mt.function(mt.insert_tuple([ptr_slice]), to);
                mt.function(mt.insert_tuple([usize, fun]), to)
            }
            Callable::Read { ty } => {
                let ptr = mt.base(Base::Pointer(ty));
                mt.function(mt.insert_tuple([ptr]), ty)
            }
            Callable::Write { ty } => {
                let ptr = mt.base(Base::Pointer(ty));
                let unit = mt.unit();
                mt.function(mt.insert_tuple([ptr, ty]), unit)
            }
            Callable::PointerMember { tys, member } => {
                let product = mt.insert_type(mu::TypeEnum::Product(tys));
                let field = mt[tys][member as usize];
                mt.function(mt.insert_tuple([product]), field)
            }
            Callable::MultiPointerIndex { ty } => {
                let multi_ptr = mt.base(Base::MultiPointer(ty));
                let usize = mt.base(Base::SIZE);
                let ptr = mt.base(Base::Pointer(ty));
                mt.function(mt.insert_tuple([multi_ptr, usize]), ptr)
            }
            Callable::PointerSliceIndex { ty } => {
                let ptr_slice = mt.base(Base::PointerSlice(ty));
                let usize = mt.base(Base::SIZE);
                let ptr = mt.base(Base::Pointer(ty));
                mt.function(mt.insert_tuple([ptr_slice, usize]), ptr)
            }
            Callable::ArrayIndex { ty, size } => {
                let arr = mt.base(Base::Array(ty, size));
                let usize = mt.base(Base::SIZE);
                mt.function(mt.insert_tuple([arr, usize]), ty)
            }
            Callable::PointerArrayIndex { ty, size } => {
                let ptr_array = mt.base(Base::Pointer(mt.base(Base::Array(ty, size))));
                let usize = mt.base(Base::SIZE);
                let ptr = mt.base(Base::Pointer(ty));
                mt.function(mt.insert_tuple([ptr_array, usize]), ptr)
            }
            Callable::MultiPointerSlice { ty } => {
                let multi_ptr = mt.base(Base::MultiPointer(ty));
                let usize = mt.base(Base::SIZE);
                let ptr_slice = mt.base(Base::PointerSlice(ty));
                mt.function(mt.insert_tuple([multi_ptr, usize, usize]), ptr_slice)
            }
            Callable::PointerSliceSlice { ty } => {
                let ptr_slice = mt.base(Base::PointerSlice(ty));
                let usize = mt.base(Base::SIZE);
                mt.function(mt.insert_tuple([ptr_slice, usize, usize]), ptr_slice)
            }
            Callable::PointerArraySlice { ty, size } => {
                let ptr_array = mt.base(Base::Pointer(mt.base(Base::Array(ty, size))));
                let usize = mt.base(Base::SIZE);
                let ptr_slice = mt.base(Base::PointerSlice(ty));
                mt.function(mt.insert_tuple([ptr_array, usize, usize]), ptr_slice)
            }
            Callable::Len { ty } => {
                let ptr_slice = mt.base(Base::PointerSlice(ty));
                let usize = mt.base(Base::SIZE);
                mt.function(mt.insert_tuple([ptr_slice]), usize)
            }
        }
    }
}

impl mu::Typed for Operation {
    type Base = Base;
    fn get_type(&self, mt: &(impl mu::Table<Base = Self::Base> + ?Sized)) -> mu::Type {
        match *self {
            Operation::Unreachable => mt.never(),
            Operation::Constant(ty, _) => ty,
            Operation::Callable(ref callable) => callable.get_type(mt),
        }
    }
}
