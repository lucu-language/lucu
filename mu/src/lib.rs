#![no_std]
use core::fmt::Debug;
use core::hash::Hash;
use core::ops::Index;

pub trait Table:
    Index<Type, Output = TypeEnum<Self::Base>>
    + Index<Tuple, Output = [Type]>
    + Index<Enum, Output = [Type]>
    + Index<Expression, Output = ExpressionEnum<Self::Operation>>
    + Index<Expressions, Output = [Expression]>
{
    type Base;
    type Name: Debug;
    type Operation: Typed<Base = Self::Base>;

    fn insert_type(&self, ty: TypeEnum<Self::Base>) -> Type;

    // types
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

    // expressions
    fn push_expression(&self, expr: ExpressionEnum<Self::Operation>) -> Expression;
    fn push_expressions(&self, exprs: impl IntoIterator<Item = Expression>) -> Expressions;

    // convenience functions: types
    fn unit(&self) -> Type {
        self.insert_type(TypeEnum::Product(self.insert_tuple([])))
    }
    fn bool(&self) -> Type {
        let unit = self.unit();
        self.insert_type(TypeEnum::Sum(self.insert_enum([unit, unit])))
    }
    fn optional(&self, ty: Type) -> Type {
        let unit = self.unit();
        self.insert_type(TypeEnum::Sum(self.insert_enum([unit, ty])))
    }
    fn never(&self) -> Type {
        self.insert_type(TypeEnum::Sum(self.insert_enum([])))
    }
    fn function(&self, from: Tuple, to: Type) -> Type {
        self.insert_type(TypeEnum::Function(FunctionType::new(from, to, self)))
    }
    fn base(&self, base: Self::Base) -> Type {
        self.insert_type(TypeEnum::Base(base))
    }

    // convenience functions: expressions
    fn construct(&self, types: Tuple, exprs: impl IntoIterator<Item = Expression>) -> Expression {
        self.push_expression(ExpressionEnum::Construct(
            types,
            self.push_expressions(exprs),
        ))
    }
    fn construct_unit(&self) -> Expression {
        self.construct(self.insert_tuple([]), [])
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
    fn r#match(
        &self,
        value: Expression,
        variants: impl IntoIterator<Item = Expression>,
    ) -> Expression {
        self.push_expression(ExpressionEnum::Match(
            value,
            self.push_expressions(variants),
        ))
    }
    fn if_stmt(&self, condition: Expression, body: Expression) -> Expression {
        self.if_else(condition, body, self.construct_unit())
    }
    fn if_else(
        &self,
        condition: Expression,
        then_branch: Expression,
        else_branch: Expression,
    ) -> Expression {
        self.r#match(condition, [else_branch, then_branch])
    }
}

pub trait Typed {
    type Base;
    fn get_type(&self, mt: &(impl Table<Base = Self::Base> + ?Sized)) -> Type;
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Type(u32);

impl Type {
    #[must_use]
    pub const unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Tuple(u32);

impl Tuple {
    #[must_use]
    pub const unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Enum(u32);

impl Enum {
    #[must_use]
    pub const unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Expression(u32);

impl Expression {
    #[must_use]
    pub const unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct Expressions(u32);

impl Expressions {
    #[must_use]
    pub const unsafe fn new(i: u32) -> Self {
        Self(i)
    }
    #[must_use]
    pub const fn index(self) -> u32 {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub struct FunctionType(Tuple, Type);

impl FunctionType {
    /// Creates a new [`FunctionType`].
    ///
    /// # Panics
    ///
    /// Panics if type `to` is not first-order.
    #[must_use]
    pub fn new(from: Tuple, to: Type, mt: &(impl Table + ?Sized)) -> Self {
        // TODO: add a new FirstOrderType or something
        // that is then convertible to Type
        // same with FirstOrderTuple and FirstOrderEnum
        assert!(to.is_first_order(mt));
        Self(from, to)
    }
    #[must_use]
    pub const fn from(self) -> Tuple {
        self.0
    }
    #[must_use]
    pub const fn to(self) -> Type {
        self.1
    }
    #[must_use]
    pub fn never_returns(self, mt: &(impl Table + ?Sized)) -> bool {
        matches!(mt[self.to()], TypeEnum::Sum(tys) if mt[tys].is_empty())
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord, Debug)]
pub enum TypeEnum<B> {
    Base(B),
    Sum(Enum),
    Product(Tuple),
    Function(FunctionType),
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
    #[must_use]
    pub fn is_first_order(self, mt: &(impl Table + ?Sized)) -> bool {
        match mt[self] {
            TypeEnum::Base(_) => true,
            TypeEnum::Sum(sum) => mt[sum].iter().all(|ty| ty.is_first_order(mt)),
            TypeEnum::Product(product) => mt[product].iter().all(|ty| ty.is_first_order(mt)),
            TypeEnum::Function(_) => false,
        }
    }
    #[must_use]
    pub fn into_product(self, mt: &(impl Table + ?Sized)) -> Option<Tuple> {
        match mt[self] {
            TypeEnum::Product(types) => Some(types),
            _ => None,
        }
    }
    #[must_use]
    pub fn into_sum(self, mt: &(impl Table + ?Sized)) -> Option<Enum> {
        match mt[self] {
            TypeEnum::Sum(types) => Some(types),
            _ => None,
        }
    }
    #[must_use]
    pub fn into_function(self, mt: &(impl Table + ?Sized)) -> Option<FunctionType> {
        match mt[self] {
            TypeEnum::Function(function) => Some(function),
            _ => None,
        }
    }
}

impl Expression {
    pub fn get_type<B>(self, mt: &(impl Table<Base = B> + ?Sized)) -> Option<Type> {
        match mt[self] {
            ExpressionEnum::Operation(ref o) => Some(o.get_type(mt)),
            ExpressionEnum::Reference(ty, _) | ExpressionEnum::Try(ty, _) => Some(ty),
            ExpressionEnum::Let(_, e) | ExpressionEnum::Sequence(_, e) => e.get_type(mt),
            ExpressionEnum::Construct(types, _) => Some(mt.insert_type(TypeEnum::Product(types))),
            ExpressionEnum::Apply(f, _) => f
                .get_type(mt)
                .and_then(|t| t.into_function(mt))
                .map(FunctionType::to),
            ExpressionEnum::Member(e, n) => e
                .get_type(mt)
                .and_then(|t| t.into_product(mt))
                .and_then(|types| mt[types].get(n as usize).copied()),
            ExpressionEnum::Abstract(from, e) => e
                .get_type(mt)
                .map(|to| mt.insert_type(TypeEnum::Function(FunctionType::new(from, to, mt)))),
            ExpressionEnum::Match(_, es) => mt[es]
                .first()
                .map_or_else(|| Some(mt.never()), |e| e.get_type(mt)),
            ExpressionEnum::Variant(types, _, _) => Some(mt.insert_type(TypeEnum::Sum(types))),
        }
    }
    pub fn get_captures<B>(self, mt: &(impl Table<Base = B> + ?Sized), captures: &mut [bool]) {
        self.get_captures_inner(mt, 0, captures);
    }
    fn get_captures_inner<B>(
        self,
        mt: &(impl Table<Base = B> + ?Sized),
        offset: u32,
        captures: &mut [bool],
    ) {
        // if we (somehow) have enough lambda arguments that the `offset` threatens to overflow,
        // we can simply stop checking within there,
        // as those inner nodes will never be able to reference our captures anyway
        match mt[self] {
            ExpressionEnum::Operation(_) => {}
            ExpressionEnum::Reference(_, n) => {
                if let Some(capture_idx) = n.checked_sub(offset)
                    && let Some(capture) = captures.get_mut(capture_idx as usize)
                {
                    *capture = true;
                }
            }
            ExpressionEnum::Let(e1, e2) => {
                e1.get_captures_inner(mt, offset, captures);
                if let Some(next_offset) = offset.checked_add(1) {
                    e2.get_captures_inner(mt, next_offset, captures);
                }
            }
            ExpressionEnum::Sequence(es, en) => {
                for &e in &mt[es] {
                    e.get_captures_inner(mt, offset, captures);
                }
                en.get_captures_inner(mt, offset, captures);
            }
            ExpressionEnum::Construct(_, es) => {
                for &e in &mt[es] {
                    e.get_captures_inner(mt, offset, captures);
                }
            }
            ExpressionEnum::Apply(e1, es) => {
                e1.get_captures_inner(mt, offset, captures);
                for &e2 in &mt[es] {
                    e2.get_captures_inner(mt, offset, captures);
                }
            }
            ExpressionEnum::Member(e, _) | ExpressionEnum::Variant(_, _, e) => {
                e.get_captures_inner(mt, offset, captures);
            }
            ExpressionEnum::Match(e, es) => {
                e.get_captures_inner(mt, offset, captures);
                if let Some(next_offset) = offset.checked_add(1) {
                    for &e in &mt[es] {
                        e.get_captures_inner(mt, next_offset, captures);
                    }
                }
            }
            ExpressionEnum::Abstract(t, e) => {
                if let Some(next_offset) = u32::try_from(mt[t].len())
                    .ok()
                    .and_then(|len| offset.checked_add(len))
                {
                    e.get_captures_inner(mt, next_offset, captures);
                }
            }
            ExpressionEnum::Try(_, e) => {
                if let Some(next_offset) = offset.checked_add(1) {
                    e.get_captures_inner(mt, next_offset, captures);
                }
            }
        }
    }
}
