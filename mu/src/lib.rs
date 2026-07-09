#![no_std]
use core::fmt::Debug;
use core::hash::Hash;
use core::ops::Index;

mod kind;
pub use kind::*;

pub trait TypeTable:
    Index<Type, Output = TypeEnum<Self::Base>> + Index<Types, Output = [Type]>
{
    type Base;
    type Name: Debug;

    fn insert_type(&self, ty: TypeEnum<Self::Base>) -> Type;
    fn insert_tuple(&self, tys: impl IntoIterator<Item = Type>) -> Types;
    fn push_named_tuple(
        &self,
        tys: impl IntoIterator<Item = (Self::Name, Type)>,
        name: Self::Name,
    ) -> Types;

    fn tuple_name(&self, tys: Types) -> Option<&Self::Name>;
    fn tuple_field_name(&self, tys: Types, index: u32) -> Option<&Self::Name>;

    // convenience functions
    fn unit(&self) -> Type {
        self.insert_type(TypeEnum::Product(self.insert_tuple([])))
    }
    fn never(&self) -> Type {
        self.insert_type(TypeEnum::Never)
    }
    fn function(&self, from: impl IntoIterator<Item = Type>, to: Type) -> Type {
        self.insert_type(TypeEnum::Function(Function::new(
            self.insert_tuple(from),
            to,
            self,
        )))
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
    fn construct(&self, types: Types, exprs: impl IntoIterator<Item = Expression>) -> Expression {
        self.push_expression(ExpressionEnum::Construct(
            types,
            self.push_expressions(exprs),
        ))
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
    fn lambda(&self, from: Types, body: Expression) -> Expression {
        self.push_expression(ExpressionEnum::Abstract(from, body))
    }
    fn try_break(&self, ty: Type, body: Expression) -> Expression {
        self.push_expression(ExpressionEnum::Try(ty, body))
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
pub struct Types(u32);

impl Types {
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
pub struct Function(Types, Type);

impl Function {
    pub fn new(from: Types, to: Type, tt: &(impl TypeTable + ?Sized)) -> Self {
        assert!(to.is_first_order(tt));
        Function(from, to)
    }
    pub fn from(self) -> Types {
        self.0
    }
    pub fn to(self) -> Type {
        self.1
    }
    pub fn never_returns(self, tt: &(impl TypeTable + ?Sized)) -> bool {
        matches!(tt[self.to()], TypeEnum::Never)
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub enum TypeEnum<B> {
    Base(B),
    Never,
    Product(Types),
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
    Construct(Types, Expressions),
    // (e1 e2)
    Apply(Expression, Expressions),
    // (pi e)
    Member(Expression, u32),
    // (lambda x : tau. e)
    Abstract(Types, Expression),
    // (mu x <- tau. e)
    Try(Type, Expression),
}

impl Type {
    pub fn is_first_order(self, tt: &(impl TypeTable + ?Sized)) -> bool {
        match tt[self] {
            TypeEnum::Base(_) | TypeEnum::Never => true,
            TypeEnum::Product(product) => {
                tt[product].iter().copied().all(|ty| ty.is_first_order(tt))
            }
            TypeEnum::Function(_) => false,
        }
    }
    pub fn into_product(self, tt: &(impl TypeTable + ?Sized)) -> Types {
        match tt[self] {
            TypeEnum::Product(types) => types,
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
        }
    }
    pub fn get_captures(self, et: &(impl ExpressionTable + ?Sized), captures: &mut [bool]) {
        self.get_captures_inner(et, 0, captures);
    }
    fn get_captures_inner(
        self,
        et: &(impl ExpressionTable + ?Sized),
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
                e1.get_captures_inner(et, offset, captures);
                e2.get_captures_inner(et, offset + 1, captures);
            }
            ExpressionEnum::Sequence(es, en) => {
                for e in et[es].iter() {
                    e.get_captures_inner(et, offset, captures);
                }
                en.get_captures_inner(et, offset, captures);
            }
            ExpressionEnum::Construct(_, es) => {
                for e in et[es].iter() {
                    e.get_captures_inner(et, offset, captures);
                }
            }
            ExpressionEnum::Apply(e1, es) => {
                e1.get_captures_inner(et, offset, captures);
                for &e2 in et[es].iter() {
                    e2.get_captures_inner(et, offset, captures);
                }
            }
            ExpressionEnum::Member(e, _) => {
                e.get_captures_inner(et, offset, captures);
            }
            ExpressionEnum::Abstract(_, e) | ExpressionEnum::Try(_, e) => {
                e.get_captures_inner(et, offset + 1, captures);
            }
        }
    }
}
