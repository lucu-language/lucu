use std::iter;

use compact_str::CompactString;
use mu::TypeTable as _;

use crate::ast;
use crate::mu::table::TypeTable;
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
    /// (a x a) -> a OR (a x a) -> bool
    BinOp { ty: mu::Type, op: ast::BinOp },
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

impl Operation {
    pub fn get_type(&self, tt: &TypeTable) -> mu::Type {
        match *self {
            Operation::Unreachable => tt.never(),
            Operation::Constant(ty, _) => ty,
            Operation::Callable(ref callable) => match *callable {
                Callable::Cast { from, to, .. } => {
                    tt.insert_type(mu::TypeEnum::Function(mu::Function::new(from, to, tt)))
                }
                Callable::UnOp { ty, .. } => {
                    tt.insert_type(mu::TypeEnum::Function(mu::Function::new(ty, ty, tt)))
                }
                Callable::BinOp { ty, op } => {
                    let input = tt.insert_type(mu::TypeEnum::Product(tt.tuple([ty, ty])));
                    match op {
                        ast::BinOp::Equality(_) | ast::BinOp::Inequality(_) => {
                            let bool = tt.insert_type(mu::TypeEnum::Base(Base::Boolean));
                            tt.insert_type(mu::TypeEnum::Function(mu::Function::new(
                                input, bool, tt,
                            )))
                        }
                        ast::BinOp::Math(_) => {
                            tt.insert_type(mu::TypeEnum::Function(mu::Function::new(input, ty, tt)))
                        }
                    }
                }
                Callable::If => {
                    let bool = tt.base(Base::Boolean);
                    let unit = tt.unit();
                    let branch =
                        tt.insert_type(mu::TypeEnum::Function(mu::Function::new(unit, unit, tt)));
                    let input = tt.insert_type(mu::TypeEnum::Product(tt.tuple([bool, branch])));
                    tt.insert_type(mu::TypeEnum::Function(mu::Function::new(input, unit, tt)))
                }
                Callable::IfElse { to } => {
                    let bool = tt.base(Base::Boolean);
                    let unit = tt.unit();
                    let branch =
                        tt.insert_type(mu::TypeEnum::Function(mu::Function::new(unit, to, tt)));
                    let input =
                        tt.insert_type(mu::TypeEnum::Product(tt.tuple([bool, branch, branch])));
                    tt.insert_type(mu::TypeEnum::Function(mu::Function::new(input, to, tt)))
                }
                Callable::Syscall { args } => {
                    let uptr = tt.insert_type(mu::TypeEnum::Base(Base::UPTR));
                    let input = tt.insert_type(mu::TypeEnum::Product(
                        tt.tuple(iter::repeat_n(uptr, args as usize + 1)),
                    ));
                    tt.insert_type(mu::TypeEnum::Function(mu::Function::new(input, uptr, tt)))
                }
            },
        }
    }
}
