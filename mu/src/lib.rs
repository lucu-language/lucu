#![no_std]
use core::fmt::Debug;
use core::hash::Hash;
use core::ops::Index;

pub trait TypeTable:
    Index<Type, Output = TypeEnum<Self::Base>> + Index<Types, Output = [Type]>
{
    type Base;
    type Name: Debug;

    fn insert_type(&self, ty: TypeEnum<Self::Base>) -> Type;
    fn push_aggregate(
        &self,
        tys: impl IntoIterator<Item = (Self::Name, Type)>,
        name: Self::Name,
    ) -> Types;

    fn aggregate_name(&self, tys: Types) -> &Self::Name;
    fn aggregate_field_name(&self, tys: Types, index: u32) -> &Self::Name;
}

pub trait ExpressionTable:
    Index<Expression, Output = ExpressionEnum<Self::Operation>>
    + Index<Expressions, Output = [Expression]>
{
    type Operation;
    fn push_expression(&self, expr: ExpressionEnum<Self::Operation>) -> Expression;
    fn push_expressions(&self, exprs: impl IntoIterator<Item = Expression>) -> Expressions;
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Type(pub u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Types(pub u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Expression(pub u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Expressions(pub u32);

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Function(Type, Type);

impl Function {
    pub fn new(from: Type, to: Type, tt: &impl TypeTable) -> Self {
        assert!(to.first_order(tt));
        Function(from, to)
    }
    pub fn from(self) -> Type {
        self.0
    }
    pub fn to(self) -> Type {
        self.1
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub enum TypeEnum<B> {
    Base(B),
    Product(Types),
    Function(Function),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub enum ExpressionEnum<O> {
    // o / c
    Operation(O),
    // x
    /// Using De Bruijn-indices
    Reference(u32),
    // let x = e1 in e2
    Let(Expression, Expression),
    // e1; e2; e3; ...; en
    Sequence(Expressions, Expression),
    // (e1, e2, e3, ...)
    Construct(Types, Expressions),
    // (e1 e2)
    Apply(Expression, Expression),
    // (pi e)
    Member(Expression, u32),
    // (lambda x : tau. e)
    /// Type must be TypeEnum::Function
    Abstract(Type, Expression),
    // (mu x <- tau. e)
    Try(Type, Expression),
}

impl Type {
    pub fn first_order(self, tt: &impl TypeTable) -> bool {
        match tt[self] {
            TypeEnum::Base(_) => true,
            TypeEnum::Product(product) => tt[product].iter().copied().all(|ty| ty.first_order(tt)),
            TypeEnum::Function(_) => false,
        }
    }
}

impl Expression {
    pub fn get_captures(self, tt: &impl ExpressionTable, captures: &mut [bool]) {
        self.get_captures_inner(tt, 0, captures);
    }
    fn get_captures_inner(self, tt: &impl ExpressionTable, offset: u32, captures: &mut [bool]) {
        match tt[self] {
            ExpressionEnum::Operation(_) => {}
            ExpressionEnum::Reference(n) => {
                if n >= offset && ((n - offset) as usize) < captures.len() {
                    captures[(n - offset) as usize] = true;
                }
            }
            ExpressionEnum::Let(e1, e2) => {
                e1.get_captures_inner(tt, offset, captures);
                e2.get_captures_inner(tt, offset + 1, captures);
            }
            ExpressionEnum::Sequence(es, en) => {
                for e in tt[es].iter() {
                    e.get_captures_inner(tt, offset, captures);
                }
                en.get_captures_inner(tt, offset, captures);
            }
            ExpressionEnum::Construct(_, es) => {
                for e in tt[es].iter() {
                    e.get_captures_inner(tt, offset, captures);
                }
            }
            ExpressionEnum::Apply(e1, e2) => {
                e1.get_captures_inner(tt, offset, captures);
                e2.get_captures_inner(tt, offset, captures);
            }
            ExpressionEnum::Member(e, _) => {
                e.get_captures_inner(tt, offset, captures);
            }
            ExpressionEnum::Abstract(_, e) | ExpressionEnum::Try(_, e) => {
                e.get_captures_inner(tt, offset + 1, captures);
            }
        }
    }
}
