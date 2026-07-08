use std::ops::Index;

use asta_handle_map::xar::Xar;
use asta_handle_map::{HandleMap, HandleSet};
use compact_str::CompactString;
use mu::ExpressionTable as _;

use crate::ast;
use crate::mu::{Base, Callable, Constant, Operation};

pub struct TypeTable {
    types: HandleSet<mu::TypeEnum<Base>>,
    tuples: HandleMap<Box<[mu::Type]>, mu::Types>,
    aggregates: Xar<Aggregate>,
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
            tuples: HandleMap::new(),
            aggregates: Xar::new(),
        }
    }
}

impl Index<mu::Type> for TypeTable {
    type Output = mu::TypeEnum<Base>;

    fn index(&self, index: mu::Type) -> &Self::Output {
        unsafe { self.types.get_unchecked(index.index()) }
    }
}

impl Index<mu::Types> for TypeTable {
    type Output = [mu::Type];

    fn index(&self, index: mu::Types) -> &Self::Output {
        let aggregate = unsafe { self.aggregates.get_unchecked(index.index()) };
        match aggregate {
            &Aggregate::Tuple(n) => unsafe { self.tuples.get_unchecked(n) }.0,
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

    fn insert_tuple(&self, tys: impl IntoIterator<Item = mu::Type>) -> mu::Types {
        let fields = tys.into_iter().collect::<Box<_>>();
        *self
            .tuples
            .get_or_insert(fields, |n| {
                let i = self.aggregates.push(Aggregate::Tuple(n));
                // SAFETY: We are really close to a potential race condition at this point!
                // If the fields of this new aggregate gets looked up right now, undefined memory would be read.
                // However, this aggregate isn't accessible until the function ends,
                // at which point the fields will be inserted.
                // If we allow iterating over all aggregates, then we'd be screwed.
                unsafe { mu::Types::new(i) }
            })
            .1
    }

    fn push_named_tuple(
        &self,
        tys: impl IntoIterator<Item = (Self::Name, mu::Type)>,
        name: Self::Name,
    ) -> mu::Types {
        let (field_names, fields): (Vec<_>, Vec<_>) = tys.into_iter().unzip();
        let i = self.aggregates.push(Aggregate::Named {
            name,
            field_names: field_names.into_boxed_slice(),
            fields: fields.into_boxed_slice(),
        });
        unsafe { mu::Types::new(i) }
    }

    fn tuple_name(&self, tys: mu::Types) -> Option<&Self::Name> {
        let aggregate = unsafe { self.aggregates.get_unchecked(tys.index()) };
        match aggregate {
            Aggregate::Tuple(_) => None,
            Aggregate::Named { name, .. } => Some(name),
        }
    }

    fn tuple_field_name(&self, tys: mu::Types, index: u32) -> Option<&Self::Name> {
        let aggregate = unsafe { self.aggregates.get_unchecked(tys.index()) };
        match aggregate {
            Aggregate::Tuple(_) => None,
            Aggregate::Named { field_names, .. } => Some(&field_names[index as usize]),
        }
    }
}

enum Aggregate {
    Tuple(u32),
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
        self.apply(
            self.operation(Operation::Callable(Callable::Cast { from, to, op })),
            value,
        )
    }
    pub fn constant(&self, ty: mu::Type, constant: Constant) -> mu::Expression {
        self.operation(Operation::Constant(ty, constant))
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
