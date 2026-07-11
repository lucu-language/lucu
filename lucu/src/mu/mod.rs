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
    // TODO: this should be `^[:0]char`
    CString,
    // TODO: pointers, arrays
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
    // TODO: deref, index, array
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
