use std::slice;
use std::sync::Arc;

use itertools::Itertools;

use crate::type_table::{
    Effect, EffectEnum, FunctionParameter, FunctionReturns, FunctionSignature,
    FunctionSignatureValue, GenericArgument, GenericParameter, Item, Region, RegionEnum, Term,
    Type, TypeEnum, TypeTable,
};

pub trait Substitute {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self;
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self;
}

impl GenericParameter {
    fn instantiate(self, tt: &mut TypeTable, start: usize, arg: GenericArgument) -> Term {
        let term = if start > 0 {
            arg.shift(tt, 0, start).term
        } else {
            arg.term
        };
        match &self.apply {
            Some(apply) => {
                assert_eq!(arg.arity, Some(apply.len()));
                term.subst(tt, 0, apply)
            }
            None => {
                assert_eq!(arg.arity, None);
                term
            }
        }
    }
}

impl<T> Substitute for Arc<[T]>
where
    T: Substitute + Copy,
{
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        self.iter().map(|ty| ty.subst(tt, start, args)).collect()
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        self.iter().map(|ty| ty.shift(tt, start, offset)).collect()
    }
}

impl<T> Substitute for Option<T>
where
    T: Substitute,
{
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        self.map(|tys| tys.subst(tt, start, args))
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        self.map(|tys| tys.shift(tt, start, offset))
    }
}

impl Substitute for Item {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        Self {
            module: self.module,
            name: self.name,
            apply: self.apply.subst(tt, start, args),
        }
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        Self {
            module: self.module,
            name: self.name,
            apply: self.apply.shift(tt, start, offset),
        }
    }
}

impl Substitute for GenericParameter {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        GenericParameter {
            index: if self.index < start + args.len() {
                self.index
            } else {
                self.index - args.len()
            },
            apply: self.apply.subst(tt, start, args),
        }
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        GenericParameter {
            index: if self.index < start {
                self.index
            } else {
                self.index + offset
            },
            apply: self.apply.shift(tt, start, offset),
        }
    }
}

impl Substitute for GenericArgument {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        GenericArgument {
            term: self.term.subst(tt, start + self.arity.unwrap_or(0), args),
            arity: self.arity,
        }
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        GenericArgument {
            term: self.term.shift(tt, start + self.arity.unwrap_or(0), offset),
            arity: self.arity,
        }
    }
}

impl Substitute for Term {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.subst(tt, start, args)),
            Term::Region(region) => Term::Region(region.subst(tt, start, args)),
            Term::Effect(effect) => Term::Effect(effect.subst(tt, start, args)),
        }
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.shift(tt, start, offset)),
            Term::Region(region) => Term::Region(region.shift(tt, start, offset)),
            Term::Effect(effect) => Term::Effect(effect.shift(tt, start, offset)),
        }
    }
}

impl Substitute for Type {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match tt[self] {
            TypeEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(tt, start, args);
                // generics have *reversed* indices
                if let Some(index) = index.and_then(|index| args.len().checked_sub(index + 1)) {
                    match generic.instantiate(tt, start, args[index]) {
                        Term::Type(ty) => return ty,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    TypeEnum::Generic(generic)
                }
            }
            TypeEnum::Item(ref item) => TypeEnum::Item(item.clone().subst(tt, start, args)),
            TypeEnum::Pointer(ty, region) => {
                TypeEnum::Pointer(ty.subst(tt, start, args), region.subst(tt, start, args))
            }
            TypeEnum::PointerSlice(ty, region) => {
                TypeEnum::PointerSlice(ty.subst(tt, start, args), region.subst(tt, start, args))
            }
            TypeEnum::Integer(_) | TypeEnum::Boolean | TypeEnum::Unit => return self,
        };
        tt.insert_type(changed)
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            TypeEnum::Generic(ref generic) => {
                TypeEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            TypeEnum::Item(ref item) => TypeEnum::Item(item.clone().shift(tt, start, offset)),
            TypeEnum::Pointer(ty, region) => {
                TypeEnum::Pointer(ty.shift(tt, start, offset), region.shift(tt, start, offset))
            }
            TypeEnum::PointerSlice(ty, region) => {
                TypeEnum::PointerSlice(ty.shift(tt, start, offset), region.shift(tt, start, offset))
            }
            TypeEnum::Integer(_) | TypeEnum::Boolean | TypeEnum::Unit => return self,
        };
        tt.insert_type(changed)
    }
}

impl Substitute for Region {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match tt[self] {
            RegionEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(tt, start, args);
                // generics have *reversed* indices
                if let Some(index) = index.and_then(|index| args.len().checked_sub(index + 1)) {
                    match generic.instantiate(tt, start, args[index]) {
                        Term::Region(region) => return region,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    RegionEnum::Generic(generic)
                }
            }
        };
        tt.insert_region(changed)
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            RegionEnum::Generic(ref generic) => {
                RegionEnum::Generic(generic.clone().shift(tt, start, offset))
            }
        };
        tt.insert_region(changed)
    }
}

impl Substitute for Effect {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match tt[self] {
            EffectEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(tt, start, args);
                // generics have *reversed* indices
                if let Some(index) = index.and_then(|index| args.len().checked_sub(index + 1)) {
                    match generic.instantiate(tt, start, args[index]) {
                        Term::Effect(effect) => return effect,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    EffectEnum::Generic(generic)
                }
            }
            EffectEnum::Item(ref item) => EffectEnum::Item(item.clone().subst(tt, start, args)),
            EffectEnum::Row(ref row) => {
                let row = row
                    .clone()
                    .subst(tt, start, args)
                    .iter()
                    .flat_map(|e| match tt[*e] {
                        EffectEnum::Row(ref effects) => effects.iter().copied(),

                        _ => slice::from_ref(e).iter().copied(),
                    })
                    .unique()
                    .collect::<Arc<_>>();
                match *row {
                    [single] => return single,
                    _ => EffectEnum::Row(row),
                }
            }
        };
        tt.insert_effect(changed)
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            EffectEnum::Generic(ref generic) => {
                EffectEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            EffectEnum::Item(ref item) => EffectEnum::Item(item.clone().shift(tt, start, offset)),
            EffectEnum::Row(ref row) => EffectEnum::Row(row.clone().shift(tt, start, offset)),
        };
        tt.insert_effect(changed)
    }
}

impl Substitute for FunctionParameter {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            FunctionParameter::Data(ty) => FunctionParameter::Data(ty.subst(tt, start, args)),
            FunctionParameter::Lambda(sig) => FunctionParameter::Lambda(sig.subst(tt, start, args)),
        }
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        match self {
            FunctionParameter::Data(ty) => FunctionParameter::Data(ty.shift(tt, start, offset)),
            FunctionParameter::Lambda(sig) => {
                FunctionParameter::Lambda(sig.shift(tt, start, offset))
            }
        }
    }
}

impl Substitute for FunctionSignature {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let sig = tt[self].clone();
        let type_params = sig.type_params;
        let arity = type_params.as_ref().map(|params| params.len()).unwrap_or(0);
        let params = sig.params.subst(tt, start + arity, args);
        let returns = match sig.returns {
            FunctionReturns::Data(ty) => FunctionReturns::Data(ty.subst(tt, start + arity, args)),
            FunctionReturns::Never => FunctionReturns::Never,
        };
        let effects = sig.effects.subst(tt, start + arity, args);
        tt.insert_function_signature(FunctionSignatureValue {
            type_params,
            params,
            returns,
            effects,
        })
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        let sig = tt[self].clone();
        let type_params = sig.type_params;
        let arity = type_params.as_ref().map(|params| params.len()).unwrap_or(0);
        let params = sig.params.shift(tt, start + arity, offset);
        let returns = match sig.returns {
            FunctionReturns::Data(ty) => FunctionReturns::Data(ty.shift(tt, start + arity, offset)),
            FunctionReturns::Never => FunctionReturns::Never,
        };
        let effects = sig.effects.shift(tt, start + arity, offset);
        tt.insert_function_signature(FunctionSignatureValue {
            type_params,
            params,
            returns,
            effects,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shift() {
        let mut table = TypeTable::new();
        let lhs = GenericArgument {
            term: Term::Type(table.insert_type(TypeEnum::Generic(GenericParameter {
                index: 1,
                apply: None,
            }))),
            arity: Some(1),
        };
        let rhs = GenericArgument {
            term: Term::Type(table.insert_type(TypeEnum::Generic(GenericParameter {
                index: 0,
                apply: None,
            }))),
            arity: None,
        };
        assert_eq!(lhs.subst(&mut table, 0, &[rhs]), lhs);
    }
}
