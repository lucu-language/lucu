use std::iter;

use compact_str::CompactString;

use crate::ast;
use crate::type_table::Integer;

pub mod table;

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum Base {
    // Unit is represented by the empty tuple
    // Never is part of Mu
    Boolean,
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
    pub const U8: Self = Self::Integer(Integer::U8);
    pub const U32: Self = Self::Integer(Integer::U32);
    pub const INT: Self = Self::Integer(Integer::INT);
    pub const USIZE: Self = Self::Integer(Integer::USIZE);
    pub const UPTR: Self = Self::Integer(Integer::UPTR);
}

pub enum Constant {
    Integer(u64),
    Zero,
    Uninit,
    String(CompactString),
    // TODO: string / char
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Callable {
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
    /// (Bool x (() -> ())) -> ()
    If,
    /// (Bool x (() -> a) x (() -> a)) -> a
    IfElse { to: mu::Type },
    // TODO: inline assembly
    /// (UPtr x UPtr x UPtr x ...) -> UPtr
    Syscall { args: u8 },

    /// (a x (^a -> b)) -> b
    LetReference { ty: mu::Type, to: mu::Type },
    /// ^a -> a
    Read { ty: mu::Type },
    /// (^a x a) -> ()
    Write { ty: mu::Type },
    /// ^a -> ^b
    PointerMember { tys: mu::Types, member: u32 },

    /// ([N]a x USize) -> a
    ArrayIndex { ty: mu::Type, size: u32 },
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
    fn get_type(&self, tt: &(impl mu::TypeTable<Base = Self::Base> + ?Sized)) -> mu::Type {
        match *self {
            Callable::Cast { from, to, .. } => tt.function([from], to),
            Callable::UnOp { ty, .. } => tt.function([ty], ty),
            Callable::PredicateOp { ty, .. } => tt.function([ty, ty], tt.base(Base::Boolean)),
            Callable::MathOp { ty, .. } => tt.function([ty, ty], ty),
            Callable::If => {
                let bool = tt.base(Base::Boolean);
                let unit = tt.unit();
                let branch = tt.function([unit], unit);
                tt.function([bool, branch], unit)
            }
            Callable::IfElse { to } => {
                let bool = tt.base(Base::Boolean);
                let unit = tt.unit();
                let branch = tt.function([unit], to);
                tt.function([bool, branch, branch], to)
            }
            Callable::Syscall { args } => {
                let uptr = tt.base(Base::UPTR);
                tt.function(iter::repeat_n(uptr, args as usize + 1), uptr)
            }
            Callable::LetReference { ty, to } => {
                let ptr = tt.base(Base::Pointer(ty));
                let fun = tt.function([ptr], to);
                tt.function([ty, fun], to)
            }
            Callable::Read { ty } => {
                let ptr = tt.base(Base::Pointer(ty));
                tt.function([ptr], ty)
            }
            Callable::Write { ty } => {
                let ptr = tt.base(Base::Pointer(ty));
                let unit = tt.unit();
                tt.function([ptr, ty], unit)
            }
            Callable::PointerMember { tys, member } => {
                let product = tt.insert_type(mu::TypeEnum::Product(tys));
                let field = tt[tys][member as usize];
                tt.function([product], field)
            }
            Callable::MultiPointerIndex { ty } => {
                let multi_ptr = tt.base(Base::MultiPointer(ty));
                let usize = tt.base(Base::USIZE);
                let ptr = tt.base(Base::Pointer(ty));
                tt.function([multi_ptr, usize], ptr)
            }
            Callable::PointerSliceIndex { ty } => {
                let ptr_slice = tt.base(Base::PointerSlice(ty));
                let usize = tt.base(Base::USIZE);
                let ptr = tt.base(Base::Pointer(ty));
                tt.function([ptr_slice, usize], ptr)
            }
            Callable::ArrayIndex { ty, size } => {
                let arr = tt.base(Base::Array(ty, size));
                let usize = tt.base(Base::USIZE);
                tt.function([arr, usize], ty)
            }
            Callable::MultiPointerSlice { ty } => {
                let multi_ptr = tt.base(Base::MultiPointer(ty));
                let usize = tt.base(Base::USIZE);
                let ptr_slice = tt.base(Base::PointerSlice(ty));
                tt.function([multi_ptr, usize, usize], ptr_slice)
            }
            Callable::PointerSliceSlice { ty } => {
                let ptr_slice = tt.base(Base::PointerSlice(ty));
                let usize = tt.base(Base::USIZE);
                tt.function([ptr_slice, usize, usize], ptr_slice)
            }
            Callable::PointerArraySlice { ty, size } => {
                let ptr_array = tt.base(Base::Pointer(tt.base(Base::Array(ty, size))));
                let usize = tt.base(Base::USIZE);
                let ptr_slice = tt.base(Base::PointerSlice(ty));
                tt.function([ptr_array, usize, usize], ptr_slice)
            }
            Callable::Len { ty } => {
                let ptr_slice = tt.base(Base::PointerSlice(ty));
                let usize = tt.base(Base::USIZE);
                tt.function([ptr_slice], usize)
            }
        }
    }
}

impl mu::Typed for Operation {
    type Base = Base;
    fn get_type(&self, tt: &(impl mu::TypeTable<Base = Self::Base> + ?Sized)) -> mu::Type {
        match *self {
            Operation::Unreachable => tt.never(),
            Operation::Constant(ty, _) => ty,
            Operation::Callable(ref callable) => callable.get_type(tt),
        }
    }
}
