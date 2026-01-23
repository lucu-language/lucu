use std::sync::Arc;

use crate::type_table::{Effect, GenericArgument, Region, Type, TypeTable};

pub trait Unapply: Sized {
    fn unapply(self, tt: &mut TypeTable) -> Option<(Self, Arc<[GenericArgument]>)>;
}

impl Unapply for Region {
    fn unapply(self, tt: &mut TypeTable) -> Option<(Self, Arc<[GenericArgument]>)> {
        todo!()
    }
}

impl Unapply for Effect {
    fn unapply(self, tt: &mut TypeTable) -> Option<(Self, Arc<[GenericArgument]>)> {
        todo!()
    }
}

impl Unapply for Type {
    fn unapply(self, tt: &mut TypeTable) -> Option<(Self, Arc<[GenericArgument]>)> {
        todo!()
    }
}
