use std::ops::Index;

use asta_handle_map::xar::Xar;
use asta_handle_map::{HandleMap, HandleSet};
use compact_str::CompactString;
use mu::ExpressionTable as _;

use crate::ast;
use crate::mu::{Base, Callable, Constant, Operation};

pub struct TypeTable {
    types: HandleSet<mu::TypeEnum<Base>>,
    tuple_map: HandleMap<Box<[mu::Type]>, mu::Tuple>,
    tuples: Xar<Aggregate>,
    enum_map: HandleMap<Box<[mu::Type]>, mu::Enum>,
    enums: Xar<Aggregate>,
}

impl TypeTable {
    /// # Safety
    /// Every handle produced by this instance MUST only be used with this instance.
    ///
    /// Technically, we should make the methods of this unsafe, but that would cause too much unsafe blocks imo.
    /// We usually have only one global instance of a TypeTable, so we simply make the constructor unsafe.
    pub unsafe fn new() -> Self {
        Self {
            types: HandleSet::new(),
            tuple_map: HandleMap::new(),
            tuples: Xar::new(),
            enum_map: HandleMap::new(),
            enums: Xar::new(),
        }
    }
}

impl Index<mu::Type> for TypeTable {
    type Output = mu::TypeEnum<Base>;

    fn index(&self, index: mu::Type) -> &Self::Output {
        unsafe { self.types.get_unchecked(index.index()) }
    }
}

impl Index<mu::Tuple> for TypeTable {
    type Output = [mu::Type];

    fn index(&self, index: mu::Tuple) -> &Self::Output {
        let aggregate = unsafe { self.tuples.get_unchecked(index.index()) };
        match aggregate {
            &Aggregate::Unnamed(n) => unsafe { self.tuple_map.get_unchecked(n) }.0,
            Aggregate::Named { fields, .. } => fields,
        }
    }
}

impl Index<mu::Enum> for TypeTable {
    type Output = [mu::Type];

    fn index(&self, index: mu::Enum) -> &Self::Output {
        let aggregate = unsafe { self.enums.get_unchecked(index.index()) };
        match aggregate {
            &Aggregate::Unnamed(n) => unsafe { self.enum_map.get_unchecked(n) }.0,
            Aggregate::Named { fields, .. } => fields,
        }
    }
}

impl mu::TypeTable for TypeTable {
    type Base = Base;
    type Name = CompactString;

    fn insert_type(&self, ty: mu::TypeEnum<Self::Base>) -> mu::Type {
        let i = self.types.insert(ty);
        unsafe { mu::Type::new(i) }
    }

    fn insert_tuple(&self, tys: impl IntoIterator<Item = mu::Type>) -> mu::Tuple {
        let fields = tys.into_iter().collect::<Box<_>>();
        *self
            .tuple_map
            .get_or_insert(fields, |n| {
                let i = self.tuples.push(Aggregate::Unnamed(n));
                // SAFETY: We are really close to a potential race condition at this point!
                // If the fields of this new aggregate gets looked up right now, undefined memory would be read.
                // However, this aggregate isn't accessible until the function ends,
                // at which point the fields will be inserted.
                // If we allow iterating over all aggregates, then we'd be screwed.
                unsafe { mu::Tuple::new(i) }
            })
            .1
    }

    fn push_named_tuple(
        &self,
        tys: impl IntoIterator<Item = (Self::Name, mu::Type)>,
        name: Self::Name,
    ) -> mu::Tuple {
        let (field_names, fields): (Vec<_>, Vec<_>) = tys.into_iter().unzip();
        let i = self.tuples.push(Aggregate::Named {
            name,
            field_names: field_names.into_boxed_slice(),
            fields: fields.into_boxed_slice(),
        });
        unsafe { mu::Tuple::new(i) }
    }

    fn tuple_name(&self, tys: mu::Tuple) -> Option<&Self::Name> {
        let aggregate = unsafe { self.tuples.get_unchecked(tys.index()) };
        match aggregate {
            Aggregate::Unnamed(_) => None,
            Aggregate::Named { name, .. } => Some(name),
        }
    }

    fn tuple_field_name(&self, tys: mu::Tuple, index: u32) -> Option<&Self::Name> {
        let aggregate = unsafe { self.tuples.get_unchecked(tys.index()) };
        match aggregate {
            Aggregate::Unnamed(_) => None,
            Aggregate::Named { field_names, .. } => Some(&field_names[index as usize]),
        }
    }

    fn insert_enum(&self, tys: impl IntoIterator<Item = mu::Type>) -> mu::Enum {
        let fields = tys.into_iter().collect::<Box<_>>();
        *self
            .enum_map
            .get_or_insert(fields, |n| {
                let i = self.enums.push(Aggregate::Unnamed(n));
                // SAFETY: We are really close to a potential race condition at this point!
                // If the fields of this new aggregate gets looked up right now, undefined memory would be read.
                // However, this aggregate isn't accessible until the function ends,
                // at which point the fields will be inserted.
                // If we allow iterating over all aggregates, then we'd be screwed.
                unsafe { mu::Enum::new(i) }
            })
            .1
    }

    fn push_named_enum(
        &self,
        tys: impl IntoIterator<Item = (Self::Name, mu::Type)>,
        name: Self::Name,
    ) -> mu::Enum {
        let (field_names, fields): (Vec<_>, Vec<_>) = tys.into_iter().unzip();
        let i = self.enums.push(Aggregate::Named {
            name,
            field_names: field_names.into_boxed_slice(),
            fields: fields.into_boxed_slice(),
        });
        unsafe { mu::Enum::new(i) }
    }

    fn enum_name(&self, tys: mu::Enum) -> Option<&Self::Name> {
        let aggregate = unsafe { self.enums.get_unchecked(tys.index()) };
        match aggregate {
            Aggregate::Unnamed(_) => None,
            Aggregate::Named { name, .. } => Some(name),
        }
    }

    fn enum_variant_name(&self, tys: mu::Enum, index: u32) -> Option<&Self::Name> {
        let aggregate = unsafe { self.enums.get_unchecked(tys.index()) };
        match aggregate {
            Aggregate::Unnamed(_) => None,
            Aggregate::Named { field_names, .. } => Some(&field_names[index as usize]),
        }
    }
}

enum Aggregate {
    Unnamed(u32),
    Named {
        name: CompactString,
        field_names: Box<[CompactString]>,
        fields: Box<[mu::Type]>,
    },
}

pub struct ExpressionTable {
    expressions: Xar<mu::ExpressionEnum<Operation>>,
    expression_seqs: Xar<Box<[mu::Expression]>>,
}

impl ExpressionTable {
    /// # Safety
    /// Every handle produced by this instance MUST only be used with this instance.
    ///
    /// Technically, we should make the methods of this unsafe, but that would cause too much unsafe blocks imo.
    /// We usually have only one global instance of an ExpressionTable, so we simply make the constructor unsafe.
    pub unsafe fn new() -> Self {
        Self {
            expressions: Xar::new(),
            expression_seqs: Xar::new(),
        }
    }
    pub fn cast(
        &self,
        from: mu::Type,
        to: mu::Type,
        op: ast::Cast,
        value: mu::Expression,
    ) -> mu::Expression {
        self.call(Callable::Cast { from, to, op }, [value])
    }
    pub fn constant(&self, ty: mu::Type, constant: Constant) -> mu::Expression {
        self.operation(Operation::Constant(ty, constant))
    }
    pub fn call(
        &self,
        c: Callable,
        vals: impl IntoIterator<Item = mu::Expression>,
    ) -> mu::Expression {
        self.apply_operation(Operation::Callable(c), vals)
    }
}

impl Index<mu::Expression> for ExpressionTable {
    type Output = mu::ExpressionEnum<Operation>;

    fn index(&self, index: mu::Expression) -> &Self::Output {
        unsafe { self.expressions.get_unchecked(index.index()) }
    }
}

impl Index<mu::Expressions> for ExpressionTable {
    type Output = [mu::Expression];

    fn index(&self, index: mu::Expressions) -> &Self::Output {
        unsafe { self.expression_seqs.get_unchecked(index.index()) }
    }
}

impl mu::ExpressionTable for ExpressionTable {
    type Base = Base;
    type Operation = Operation;

    fn push_expression(&self, expr: mu::ExpressionEnum<Self::Operation>) -> mu::Expression {
        let i = self.expressions.push(expr);
        unsafe { mu::Expression::new(i) }
    }

    fn push_expressions(&self, exprs: impl IntoIterator<Item = mu::Expression>) -> mu::Expressions {
        let i = self.expression_seqs.push(exprs.into_iter().collect());
        unsafe { mu::Expressions::new(i) }
    }
}
