use std::sync::Arc;

use crate::type_table::unapply::Unapply;
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionReturns,
    FunctionSignature, FunctionSignatureValue, GenericArgument, GenericParameter, Item, Region,
    RegionEnum, Sentinel, Term, Type, TypeEnum, TypeTable,
};

pub trait Substitute {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self;
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self;
    /// Used for inferring global handler generics from the function signatures
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()>;
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        Iterator::zip(self.iter().copied(), from.iter().copied())
            .map(|(a, b)| a.infer(b, tt, start, args))
            .collect()
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        assert!(self.is_some() == from.is_some());
        if let (Some(a), Some(b)) = (self, from) {
            a.infer(b, tt, start, args)
        } else {
            Some(())
        }
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        (self.module == from.module).then_some(())?;
        (self.name == from.name).then_some(())?;
        self.apply
            .clone()
            .infer(from.apply.clone(), tt, start, args)
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        (self.index == from.index).then_some(());
        self.apply
            .clone()
            .infer(from.apply.clone(), tt, start, args)
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        assert!(self.arity == from.arity);
        self.term
            .infer(from.term, tt, start + self.arity.unwrap_or(0), args)
    }
}

impl Substitute for Term {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.subst(tt, start, args)),
            Term::Region(region) => Term::Region(region.subst(tt, start, args)),
            Term::Effect(effect) => Term::Effect(effect.subst(tt, start, args)),
            Term::Constant(constant) => Term::Constant(constant.subst(tt, start, args)),
        }
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.shift(tt, start, offset)),
            Term::Region(region) => Term::Region(region.shift(tt, start, offset)),
            Term::Effect(effect) => Term::Effect(effect.shift(tt, start, offset)),
            Term::Constant(constant) => Term::Constant(constant.shift(tt, start, offset)),
        }
    }
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (self, from) {
            (Term::Type(a), Term::Type(b)) => a.infer(b, tt, start, args),
            (Term::Region(a), Term::Region(b)) => a.infer(b, tt, start, args),
            (Term::Effect(a), Term::Effect(b)) => a.infer(b, tt, start, args),
            (Term::Constant(a), Term::Constant(b)) => a.infer(b, tt, start, args),
            _ => unreachable!(),
        }
    }
}

impl Substitute for Constant {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match tt[self] {
            ConstantEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(tt, start, args);
                // generics have *reversed* indices
                if let Some(index) = index.and_then(|index| args.len().checked_sub(index + 1)) {
                    match generic.instantiate(tt, start, args[index]) {
                        Term::Constant(ty) => return ty,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    ConstantEnum::Generic(generic)
                }
            }
            ConstantEnum::True
            | ConstantEnum::False
            | ConstantEnum::Integer(_)
            | ConstantEnum::String(_)
            | ConstantEnum::Character(_)
            | ConstantEnum::Zero => return self,
        };
        tt.insert_constant(changed)
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            ConstantEnum::Generic(ref generic) => {
                ConstantEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            ConstantEnum::True
            | ConstantEnum::False
            | ConstantEnum::Integer(_)
            | ConstantEnum::String(_)
            | ConstantEnum::Character(_)
            | ConstantEnum::Zero => return self,
        };
        tt.insert_constant(changed)
    }
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (&tt[self], &tt[from]) {
            (ConstantEnum::Generic(param), _) if param.index >= start => {
                let param = param.clone();
                let arity = param.apply.as_deref().map(<[_]>::len);
                let inner = match param.apply {
                    Some(self_args) => {
                        // FIXME: unapply might fail while we can still infer
                        // like `0 u32` and `u32` should infer the generic '0' to be `lambda u32`
                        let (dummy, from_args) = from.unapply(tt)?;
                        self_args.infer(from_args, tt, start, args);
                        dummy
                    }
                    None => from,
                };
                let arg = GenericArgument {
                    term: Term::Constant(inner),
                    arity,
                };
                (*args[param.index - start].get_or_insert(arg) == arg).then_some(())
            }

            (ConstantEnum::Generic(a), ConstantEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (ConstantEnum::True, ConstantEnum::True) => Some(()),
            (ConstantEnum::False, ConstantEnum::False) => Some(()),
            (ConstantEnum::Integer(a), ConstantEnum::Integer(b)) => (a == b).then_some(()),
            (ConstantEnum::String(a), ConstantEnum::String(b)) => (a == b).then_some(()),
            (ConstantEnum::Character(a), ConstantEnum::Character(b)) => (a == b).then_some(()),
            (ConstantEnum::Integer(a), ConstantEnum::Zero)
            | (ConstantEnum::Zero, ConstantEnum::Integer(a)) => (a == &0).then_some(()),
            (ConstantEnum::Zero, ConstantEnum::Zero) => Some(()),

            (ConstantEnum::Generic(_), _) => None,
            (ConstantEnum::True, _) => None,
            (ConstantEnum::False, _) => None,
            (ConstantEnum::Integer(_), _) => None,
            (ConstantEnum::String(_), _) => None,
            (ConstantEnum::Character(_), _) => None,
            (ConstantEnum::Zero, _) => None,
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
            TypeEnum::PointerSlice(ty, region, sentinel) => TypeEnum::PointerSlice(
                ty.subst(tt, start, args),
                region.subst(tt, start, args),
                // TODO: substitute when we allow more sentinels
                sentinel,
            ),
            TypeEnum::Array(ty, size, sentinel) => TypeEnum::Array(
                ty.subst(tt, start, args),
                size.subst(tt, start, args),
                // TODO: substitute when we allow more sentinels
                sentinel,
            ),
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
            TypeEnum::PointerSlice(ty, region, sentinel) => TypeEnum::PointerSlice(
                ty.shift(tt, start, offset),
                region.shift(tt, start, offset),
                // TODO: shift when we allow more sentinels
                sentinel,
            ),
            TypeEnum::Array(ty, size, sentinel) => TypeEnum::Array(
                ty.shift(tt, start, offset),
                size.shift(tt, start, offset),
                // TODO: shift when we allow more sentinels
                sentinel,
            ),
            TypeEnum::Integer(_) | TypeEnum::Boolean | TypeEnum::Unit => return self,
        };
        tt.insert_type(changed)
    }
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (&tt[self], &tt[from]) {
            (TypeEnum::Generic(param), _) if param.index >= start => {
                let param = param.clone();
                let arity = param.apply.as_deref().map(<[_]>::len);
                let inner = match param.apply {
                    Some(self_args) => {
                        // FIXME: unapply might fail while we can still infer
                        // like `0 u32` and `u32` should infer the generic '0' to be `lambda u32`
                        let (dummy, from_args) = from.unapply(tt)?;
                        self_args.infer(from_args, tt, start, args);
                        dummy
                    }
                    None => from,
                };
                let arg = GenericArgument {
                    term: Term::Type(inner),
                    arity,
                };
                (*args[param.index - start].get_or_insert(arg) == arg).then_some(())
            }

            (TypeEnum::Generic(a), TypeEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (TypeEnum::Item(a), TypeEnum::Item(b)) => a.clone().infer(b.clone(), tt, start, args),
            (TypeEnum::Integer(a), TypeEnum::Integer(b)) => (a == b).then_some(()),
            (TypeEnum::Boolean, TypeEnum::Boolean) => Some(()),
            (TypeEnum::Unit, TypeEnum::Unit) => Some(()),
            (&TypeEnum::Pointer(ta, ra), &TypeEnum::Pointer(tb, rb))
            | (&TypeEnum::PointerSlice(ta, ra, None), &TypeEnum::PointerSlice(tb, rb, None))
            | (
                &TypeEnum::PointerSlice(ta, ra, Some(Sentinel)),
                &TypeEnum::PointerSlice(tb, rb, Some(Sentinel)),
            ) => {
                ta.infer(tb, tt, start, args)?;
                ra.infer(rb, tt, start, args)?;
                Some(())
            }
            (&TypeEnum::Array(ta, sa, None), &TypeEnum::Array(tb, sb, None))
            | (
                &TypeEnum::Array(ta, sa, Some(Sentinel)),
                &TypeEnum::Array(tb, sb, Some(Sentinel)),
            ) => {
                ta.infer(tb, tt, start, args)?;
                sa.infer(sb, tt, start, args)?;
                Some(())
            }

            (TypeEnum::Generic(_), _) => None,
            (TypeEnum::Item(_), _) => None,
            (TypeEnum::Integer(_), _) => None,
            (TypeEnum::Boolean, _) => None,
            (TypeEnum::Unit, _) => None,
            (TypeEnum::Pointer(_, _), _) => None,
            (TypeEnum::PointerSlice(_, _, _), _) => None,
            (TypeEnum::Array(_, _, _), _) => None,
        }
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (&tt[self], &tt[from]) {
            (RegionEnum::Generic(param), _) if param.index >= start => {
                let param = param.clone();
                let arity = param.apply.as_deref().map(<[_]>::len);
                let inner = match param.apply {
                    Some(self_args) => {
                        // FIXME: unapply might fail while we can still infer
                        // like `0 u32` and `u32` should infer the generic '0' to be `lambda u32`
                        let (dummy, from_args) = from.unapply(tt)?;
                        self_args.infer(from_args, tt, start, args);
                        dummy
                    }
                    None => from,
                };
                let arg = GenericArgument {
                    term: Term::Region(inner),
                    arity,
                };
                (*args[param.index - start].get_or_insert(arg) == arg).then_some(())
            }

            (RegionEnum::Generic(a), RegionEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
        }
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
                return Effect::row(row.clone().subst(tt, start, args).iter(), tt);
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (&tt[self], &tt[from]) {
            (EffectEnum::Generic(param), _) if param.index >= start => {
                let param = param.clone();
                let arity = param.apply.as_deref().map(<[_]>::len);
                let inner = match param.apply {
                    Some(self_args) => {
                        // FIXME: unapply might fail while we can still infer
                        // like `0 u32` and `u32` should infer the generic '0' to be `lambda u32`
                        let (dummy, from_args) = from.unapply(tt)?;
                        self_args.infer(from_args, tt, start, args);
                        dummy
                    }
                    None => from,
                };
                let arg = GenericArgument {
                    term: Term::Effect(inner),
                    arity,
                };
                (*args[param.index - start].get_or_insert(arg) == arg).then_some(())
            }

            (EffectEnum::Generic(a), EffectEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (EffectEnum::Item(a), EffectEnum::Item(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (EffectEnum::Row(a), EffectEnum::Row(b)) if a.is_empty() && b.is_empty() => Some(()),

            (EffectEnum::Generic(_), _) => None,
            (EffectEnum::Item(_), _) => None,
            (EffectEnum::Row(a), _) if a.is_empty() => None,

            (EffectEnum::Row(_), _) => {
                // This is the one reason why we can't completely accept or deny a generics inference...
                // If we don't have enough information to accept or deny, we accept *without* inferring.
                // Feel free to be super duper smart and add more code here later if you dare,
                // but we should probably not do it like this and use a sort of Hindley-Milner with row types.
                Some(())
            }
        }
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
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (self, from) {
            (FunctionParameter::Data(a), FunctionParameter::Data(b)) => a.infer(b, tt, start, args),
            (FunctionParameter::Lambda(a), FunctionParameter::Lambda(b)) => {
                a.infer(b, tt, start, args)
            }
            _ => unreachable!(),
        }
    }
}

impl Substitute for FunctionReturns {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            FunctionReturns::Data(ty) => FunctionReturns::Data(ty.subst(tt, start, args)),
            FunctionReturns::Never => FunctionReturns::Never,
        }
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        match self {
            FunctionReturns::Data(ty) => FunctionReturns::Data(ty.shift(tt, start, offset)),
            FunctionReturns::Never => FunctionReturns::Never,
        }
    }
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (self, from) {
            (FunctionReturns::Data(a), FunctionReturns::Data(b)) => a.infer(b, tt, start, args),
            (FunctionReturns::Never, FunctionReturns::Never) => Some(()),
            // NOTE: that idea of 'thunk kinds' might allow this
            _ => unreachable!(),
        }
    }
}

impl Substitute for FunctionSignature {
    fn subst(self, tt: &mut TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let sig = tt[self].clone();
        let type_params = sig.type_params;
        let arity = type_params.as_ref().map(|params| params.len()).unwrap_or(0);
        let params = sig.params.subst(tt, start + arity, args);
        let returns = sig.returns.subst(tt, start + arity, args);
        let effect = sig.effect.subst(tt, start + arity, args);
        tt.insert_function_signature(FunctionSignatureValue {
            type_params,
            params,
            returns,
            effect,
        })
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        let sig = tt[self].clone();
        // NOTE: if we eventually have dependent kinds we need to substitute here too
        let type_params = sig.type_params;
        let arity = type_params.as_ref().map(|params| params.len()).unwrap_or(0);
        let params = sig.params.shift(tt, start + arity, offset);
        let returns = sig.returns.shift(tt, start + arity, offset);
        let effect = sig.effect.shift(tt, start + arity, offset);
        tt.insert_function_signature(FunctionSignatureValue {
            type_params,
            params,
            returns,
            effect,
        })
    }
    fn infer(
        self,
        from: Self,
        tt: &mut TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        let a = tt[self].clone();
        let b = tt[from].clone();

        // NOTE: if we eventually have dependent kinds this might fail
        assert_eq!(a.type_params, b.type_params);
        let arity = a
            .type_params
            .as_ref()
            .map(|params| params.len())
            .unwrap_or(0);

        a.params.infer(b.params, tt, start + arity, args)?;
        a.returns.infer(b.returns, tt, start + arity, args)?;
        a.effect.infer(b.effect, tt, start + arity, args)?;
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_table::{IntSize, Integer, KindEnum};

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

    #[test]
    fn test_infer() {
        let mut table = TypeTable::new();

        let typ_kind = table.insert_kind(KindEnum::TYPE);
        let typ = table.insert_type(TypeEnum::Generic(GenericParameter {
            index: 1,
            apply: None,
        }));
        let effect = table.insert_effect(EffectEnum::empty());
        let sig = table.insert_function_signature(FunctionSignatureValue {
            type_params: Some(Arc::new([typ_kind])),
            params: Some(Arc::new([FunctionParameter::Data(typ)])),
            returns: FunctionReturns::Data(typ),
            effect,
        });

        let inserted = table.insert_type(TypeEnum::Integer(Integer::unsigned(IntSize::Exact(32))));
        let inserted_sig = table.insert_function_signature(FunctionSignatureValue {
            type_params: Some(Arc::new([typ_kind])),
            params: Some(Arc::new([FunctionParameter::Data(inserted)])),
            returns: FunctionReturns::Data(inserted),
            effect,
        });

        let mut generics = vec![None];
        assert_eq!(
            sig.infer(inserted_sig, &mut table, 0, &mut generics),
            Some(())
        );
        assert_eq!(
            generics[0],
            Some(GenericArgument {
                term: Term::Type(inserted),
                arity: None
            })
        );
    }
}
