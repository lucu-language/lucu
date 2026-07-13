#![no_std]
use core::fmt::Debug;
use core::hash::Hash;
use core::ops::Index;

mod kind;
pub use kind::*;

pub trait TypeTable:
    Index<Type, Output = TypeEnum<Self::Base>>
    + Index<Tuple, Output = [Type]>
    + Index<Enum, Output = [Type]>
{
    type Base;
    type Name: Debug;

    fn insert_type(&self, ty: TypeEnum<Self::Base>) -> Type;

    fn insert_tuple(&self, tys: impl IntoIterator<Item = Type>) -> Tuple;
    fn push_named_tuple(
        &self,
        tys: impl IntoIterator<Item = (Self::Name, Type)>,
        name: Self::Name,
    ) -> Tuple;
    fn tuple_name(&self, tys: Tuple) -> Option<&Self::Name>;
    fn tuple_field_name(&self, tys: Tuple, index: u32) -> Option<&Self::Name>;

    fn insert_enum(&self, tys: impl IntoIterator<Item = Type>) -> Enum;
    fn push_named_enum(
        &self,
        tys: impl IntoIterator<Item = (Self::Name, Type)>,
        name: Self::Name,
    ) -> Enum;
    fn enum_name(&self, tys: Enum) -> Option<&Self::Name>;
    fn enum_variant_name(&self, tys: Enum, index: u32) -> Option<&Self::Name>;

    // convenience functions
    fn unit(&self) -> Type {
        self.insert_type(TypeEnum::Product(self.insert_tuple([])))
    }
    fn bool(&self) -> Type {
        let unit = self.unit();
        self.insert_type(TypeEnum::Sum(self.insert_enum([unit, unit])))
    }
    fn optional(&self, ty: Type) -> Type {
        let unit = self.unit();
        self.insert_type(TypeEnum::Sum(self.insert_enum([ty, unit])))
    }
    fn never(&self) -> Type {
        self.insert_type(TypeEnum::Sum(self.insert_enum([])))
    }
    fn function(&self, from: Tuple, to: Type) -> Type {
        self.insert_type(TypeEnum::Function(Function::new(from, to, self)))
    }
    fn base(&self, base: Self::Base) -> Type {
        self.insert_type(TypeEnum::Base(base))
    }
}

pub trait Typed {
    type Base;
    fn get_type(&self, tt: &(impl TypeTable<Base = Self::Base> + ?Sized)) -> Type;
}

pub trait ExpressionTable:
    Index<Expression, Output = ExpressionEnum<Self::Operation>>
    + Index<Expressions, Output = [Expression]>
{
    type Base;
    type Operation: Typed<Base = Self::Base>;
    fn push_expression(&self, expr: ExpressionEnum<Self::Operation>) -> Expression;
    fn push_expressions(&self, exprs: impl IntoIterator<Item = Expression>) -> Expressions;

    // convenience functions
    fn construct(&self, types: Tuple, exprs: impl IntoIterator<Item = Expression>) -> Expression {
        self.push_expression(ExpressionEnum::Construct(
            types,
            self.push_expressions(exprs),
        ))
    }
    fn construct_unit(&self, tt: &(impl TypeTable<Base = Self::Base> + ?Sized)) -> Expression {
        self.construct(tt.insert_tuple([]), [])
    }
    fn sequence(
        &self,
        exprs: impl IntoIterator<Item = Expression>,
        expr: Expression,
    ) -> Expression {
        self.push_expression(ExpressionEnum::Sequence(self.push_expressions(exprs), expr))
    }
    fn apply(&self, f: Expression, vals: impl IntoIterator<Item = Expression>) -> Expression {
        self.push_expression(ExpressionEnum::Apply(f, self.push_expressions(vals)))
    }
    fn operation(&self, o: Self::Operation) -> Expression {
        self.push_expression(ExpressionEnum::Operation(o))
    }
    fn apply_operation(
        &self,
        o: Self::Operation,
        vals: impl IntoIterator<Item = Expression>,
    ) -> Expression {
        self.apply(self.operation(o), vals)
    }
    /// Using De Bruijn-indices
    fn reference(&self, ty: Type, i: u32) -> Expression {
        self.push_expression(ExpressionEnum::Reference(ty, i))
    }
    fn let_chain(
        &self,
        values: impl IntoIterator<IntoIter = impl DoubleEndedIterator<Item = Expression>>,
        inner: Expression,
    ) -> Expression {
        let mut e = inner;
        for v in values.into_iter().rev() {
            e = self.push_expression(ExpressionEnum::Let(v, e));
        }
        e
    }
    fn member(&self, val: Expression, i: u32) -> Expression {
        self.push_expression(ExpressionEnum::Member(val, i))
    }
    fn lambda(&self, from: Tuple, body: Expression) -> Expression {
        self.push_expression(ExpressionEnum::Abstract(from, body))
    }
    fn try_break(&self, ty: Type, body: Expression) -> Expression {
        self.push_expression(ExpressionEnum::Try(ty, body))
    }
    fn match_(
        &self,
        value: Expression,
        variants: impl IntoIterator<Item = Expression>,
    ) -> Expression {
        self.push_expression(ExpressionEnum::Match(
            value,
            self.push_expressions(variants),
        ))
    }
    fn if_stmt(
        &self,
        tt: &(impl TypeTable<Base = Self::Base> + ?Sized),
        condition: Expression,
        body: Expression,
    ) -> Expression {
        self.if_else(
            condition,
            self.sequence([body], self.construct_unit(tt)),
            self.construct_unit(tt),
        )
    }
    fn if_else(
        &self,
        condition: Expression,
        then_branch: Expression,
        else_branch: Expression,
    ) -> Expression {
        self.match_(condition, [else_branch, then_branch])
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Type(u32);

impl Type {
    pub unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Tuple(u32);

impl Tuple {
    pub unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Enum(u32);

impl Enum {
    pub unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Expression(u32);

impl Expression {
    pub unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Expressions(u32);

impl Expressions {
    pub unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Function(Tuple, Type);

impl Function {
    pub fn new(from: Tuple, to: Type, tt: &(impl TypeTable + ?Sized)) -> Self {
        assert!(to.is_first_order(tt));
        Function(from, to)
    }
    pub fn from(self) -> Tuple {
        self.0
    }
    pub fn to(self) -> Type {
        self.1
    }
    pub fn never_returns(self, tt: &(impl TypeTable + ?Sized)) -> bool {
        matches!(tt[self.to()], TypeEnum::Sum(tys) if tt[tys].is_empty())
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub enum TypeEnum<B> {
    Base(B),
    Sum(Enum),
    Product(Tuple),
    Function(Function),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub enum ExpressionEnum<O> {
    // o / c
    Operation(O),
    // x
    /// Using De Bruijn-indices
    Reference(Type, u32),
    // let x = e1 in e2
    Let(Expression, Expression),
    // e1; e2; e3; ...; en
    Sequence(Expressions, Expression),
    // (e1, e2, e3, ...)
    Construct(Tuple, Expressions),
    // (e1 e2)
    Apply(Expression, Expressions),
    // (pi e)
    Member(Expression, u32),
    Match(Expression, Expressions),
    Variant(Enum, u32, Expression),
    // (lambda x : tau. e)
    Abstract(Tuple, Expression),
    // (mu x <- tau. e)
    Try(Type, Expression),
}

impl Type {
    pub fn is_first_order(self, tt: &(impl TypeTable + ?Sized)) -> bool {
        match tt[self] {
            TypeEnum::Base(_) => true,
            TypeEnum::Sum(sum) => tt[sum].iter().all(|ty| ty.is_first_order(tt)),
            TypeEnum::Product(product) => tt[product].iter().all(|ty| ty.is_first_order(tt)),
            TypeEnum::Function(_) => false,
        }
    }
    pub fn into_product(self, tt: &(impl TypeTable + ?Sized)) -> Tuple {
        match tt[self] {
            TypeEnum::Product(types) => types,
            _ => panic!(),
        }
    }
    pub fn into_sum(self, tt: &(impl TypeTable + ?Sized)) -> Enum {
        match tt[self] {
            TypeEnum::Sum(types) => types,
            _ => panic!(),
        }
    }
    pub fn into_function(self, tt: &(impl TypeTable + ?Sized)) -> Function {
        match tt[self] {
            TypeEnum::Function(function) => function,
            _ => panic!(),
        }
    }
}

impl Expression {
    pub fn get_type<B>(
        self,
        tt: &(impl TypeTable<Base = B> + ?Sized),
        et: &(impl ExpressionTable<Base = B> + ?Sized),
    ) -> Type {
        match et[self] {
            ExpressionEnum::Operation(ref o) => o.get_type(tt),
            ExpressionEnum::Reference(ty, _) | ExpressionEnum::Try(ty, _) => ty,
            ExpressionEnum::Let(_, e) | ExpressionEnum::Sequence(_, e) => e.get_type(tt, et),
            ExpressionEnum::Construct(types, _) => tt.insert_type(TypeEnum::Product(types)),
            ExpressionEnum::Apply(f, _) => {
                let fun = f.get_type(tt, et).into_function(tt);
                fun.to()
            }
            ExpressionEnum::Member(e, n) => {
                let types = e.get_type(tt, et).into_product(tt);
                tt[types][n as usize]
            }
            ExpressionEnum::Abstract(from, e) => {
                let to = e.get_type(tt, et);
                tt.insert_type(TypeEnum::Function(Function::new(from, to, tt)))
            }
            ExpressionEnum::Match(_, es) => et[es][0].get_type(tt, et),
            ExpressionEnum::Variant(types, _, _) => tt.insert_type(TypeEnum::Sum(types)),
        }
    }
    pub fn get_captures<B>(
        self,
        tt: &(impl TypeTable<Base = B> + ?Sized),
        et: &(impl ExpressionTable<Base = B> + ?Sized),
        captures: &mut [bool],
    ) {
        self.get_captures_inner(tt, et, 0, captures);
    }
    fn get_captures_inner<B>(
        self,
        tt: &(impl TypeTable<Base = B> + ?Sized),
        et: &(impl ExpressionTable<Base = B> + ?Sized),
        offset: u32,
        captures: &mut [bool],
    ) {
        match et[self] {
            ExpressionEnum::Operation(_) => {}
            ExpressionEnum::Reference(_, n) => {
                if n >= offset && ((n - offset) as usize) < captures.len() {
                    captures[(n - offset) as usize] = true;
                }
            }
            ExpressionEnum::Let(e1, e2) => {
                e1.get_captures_inner(tt, et, offset, captures);
                e2.get_captures_inner(tt, et, offset + 1, captures);
            }
            ExpressionEnum::Sequence(es, en) => {
                for e in et[es].iter() {
                    e.get_captures_inner(tt, et, offset, captures);
                }
                en.get_captures_inner(tt, et, offset, captures);
            }
            ExpressionEnum::Construct(_, es) => {
                for e in et[es].iter() {
                    e.get_captures_inner(tt, et, offset, captures);
                }
            }
            ExpressionEnum::Apply(e1, es) => {
                e1.get_captures_inner(tt, et, offset, captures);
                for &e2 in et[es].iter() {
                    e2.get_captures_inner(tt, et, offset, captures);
                }
            }
            ExpressionEnum::Member(e, _) | ExpressionEnum::Variant(_, _, e) => {
                e.get_captures_inner(tt, et, offset, captures);
            }
            ExpressionEnum::Match(e, es) => {
                e.get_captures_inner(tt, et, offset, captures);
                for e in et[es].iter() {
                    e.get_captures_inner(tt, et, offset + 1, captures);
                }
            }
            ExpressionEnum::Abstract(t, e) => {
                e.get_captures_inner(tt, et, offset + tt[t].len() as u32, captures);
            }
            ExpressionEnum::Try(_, e) => {
                e.get_captures_inner(tt, et, offset + 1, captures);
            }
        }
    }
}
