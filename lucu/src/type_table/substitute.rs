use std::sync::Arc;

use crate::type_table::unapply::Unapply;
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionSignature,
    FunctionSignatureValue, GenericArgument, GenericParameter, Item, Region, RegionEnum, Sentinel,
    Term, Thunk, Type, TypeEnum, TypeTable,
};

pub trait Substitute {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self;
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self;
    /// Used for inferring global handler generics from the function signatures
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()>;
}

impl GenericParameter {
    fn instantiate(self, tt: &TypeTable, start: usize, arg: GenericArgument) -> Term {
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
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        self.iter().map(|ty| ty.subst(tt, start, args)).collect()
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        self.iter().map(|ty| ty.shift(tt, start, offset)).collect()
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
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
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        self.map(|tys| tys.subst(tt, start, args))
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        self.map(|tys| tys.shift(tt, start, offset))
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
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
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        Self {
            module: self.module,
            name: self.name,
            apply: self.apply.subst(tt, start, args),
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        Self {
            module: self.module,
            name: self.name,
            apply: self.apply.shift(tt, start, offset),
        }
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
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
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        GenericParameter {
            index: if self.index < start + args.len() {
                self.index
            } else {
                self.index - args.len()
            },
            apply: self.apply.subst(tt, start, args),
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
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
        tt: &TypeTable,
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
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        GenericArgument {
            term: self.term.subst(tt, start + self.arity.unwrap_or(0), args),
            arity: self.arity,
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        GenericArgument {
            term: self.term.shift(tt, start + self.arity.unwrap_or(0), offset),
            arity: self.arity,
        }
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        assert!(self.arity == from.arity);
        self.term
            .infer(from.term, tt, start + self.arity.unwrap_or(0), args)
    }
}

impl Substitute for Thunk {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        Self {
            returns: self.returns.subst(tt, start, args),
            effect: self.effect.subst(tt, start, args),
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        Self {
            returns: self.returns.shift(tt, start, offset),
            effect: self.effect.shift(tt, start, offset),
        }
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        self.returns.infer(from.returns, tt, start, args)?;
        self.effect.infer(from.effect, tt, start, args)?;
        Some(())
    }
}

impl Substitute for Term {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.subst(tt, start, args)),
            Term::Region(region) => Term::Region(region.subst(tt, start, args)),
            Term::Effect(effect) => Term::Effect(effect.subst(tt, start, args)),
            Term::Constant(constant) => Term::Constant(constant.subst(tt, start, args)),
            Term::Thunk(thunk) => Term::Thunk(thunk.subst(tt, start, args)),
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.shift(tt, start, offset)),
            Term::Region(region) => Term::Region(region.shift(tt, start, offset)),
            Term::Effect(effect) => Term::Effect(effect.shift(tt, start, offset)),
            Term::Constant(constant) => Term::Constant(constant.shift(tt, start, offset)),
            Term::Thunk(thunk) => Term::Thunk(thunk.shift(tt, start, offset)),
        }
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        match (self, from) {
            (Term::Type(a), Term::Type(b)) => a.infer(b, tt, start, args),
            (Term::Region(a), Term::Region(b)) => a.infer(b, tt, start, args),
            (Term::Effect(a), Term::Effect(b)) => a.infer(b, tt, start, args),
            (Term::Constant(a), Term::Constant(b)) => a.infer(b, tt, start, args),
            (Term::Thunk(a), Term::Thunk(b)) => a.infer(b, tt, start, args),
            _ => unreachable!(),
        }
    }
}

impl Substitute for Constant {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
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
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
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
        tt: &TypeTable,
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
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match tt[self] {
            TypeEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(tt, start, args);
                // generics have *reversed* indices
                if let Some(index) = index.and_then(|index| args.len().checked_sub(index + 1)) {
                    match generic.instantiate(tt, start, args[index]) {
                        Term::Type(ty) | Term::Thunk(Thunk { returns: ty, .. }) => return ty,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    TypeEnum::Generic(generic)
                }
            }
            TypeEnum::Item(ref item) => TypeEnum::Item(item.clone().subst(tt, start, args)),
            TypeEnum::Maybe(ty) => TypeEnum::Maybe(ty.subst(tt, start, args)),
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
            TypeEnum::Integer(_) | TypeEnum::Boolean | TypeEnum::Unit | TypeEnum::Never => {
                return self;
            }
        };
        tt.insert_type(changed)
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            TypeEnum::Generic(ref generic) => {
                TypeEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            TypeEnum::Item(ref item) => TypeEnum::Item(item.clone().shift(tt, start, offset)),
            TypeEnum::Maybe(ty) => TypeEnum::Maybe(ty.shift(tt, start, offset)),
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
            TypeEnum::Integer(_) | TypeEnum::Boolean | TypeEnum::Unit | TypeEnum::Never => {
                return self;
            }
        };
        tt.insert_type(changed)
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
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
            (TypeEnum::Never, TypeEnum::Never) => Some(()),
            (&TypeEnum::Maybe(a), &TypeEnum::Maybe(b)) => a.infer(b, tt, start, args),
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
            (TypeEnum::Never, _) => None,
            (TypeEnum::Maybe(_), _) => None,
            (TypeEnum::Pointer(_, _), _) => None,
            (TypeEnum::PointerSlice(_, _, _), _) => None,
            (TypeEnum::Array(_, _, _), _) => None,
        }
    }
}

impl Substitute for Region {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
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
            RegionEnum::Static => return self,
        };
        tt.insert_region(changed)
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            RegionEnum::Generic(ref generic) => {
                RegionEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            RegionEnum::Static => return self,
        };
        tt.insert_region(changed)
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
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
            (RegionEnum::Static, RegionEnum::Static) => Some(()),

            (RegionEnum::Generic(_), _) => None,
            (RegionEnum::Static, _) => None,
        }
    }
}

impl Substitute for Effect {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let changed = match tt[self] {
            EffectEnum::Generic(ref generic) => {
                let index = generic.index.checked_sub(start);
                let generic = generic.clone().subst(tt, start, args);
                // generics have *reversed* indices
                if let Some(index) = index.and_then(|index| args.len().checked_sub(index + 1)) {
                    match generic.instantiate(tt, start, args[index]) {
                        Term::Effect(effect) | Term::Thunk(Thunk { effect, .. }) => return effect,
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
            EffectEnum::Read(region) => EffectEnum::Read(region.subst(tt, start, args)),
            EffectEnum::Write(region) => EffectEnum::Write(region.subst(tt, start, args)),
            EffectEnum::Divergent => return self,
        };
        tt.insert_effect(changed)
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            EffectEnum::Generic(ref generic) => {
                EffectEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            EffectEnum::Item(ref item) => EffectEnum::Item(item.clone().shift(tt, start, offset)),
            EffectEnum::Row(ref row) => EffectEnum::Row(row.clone().shift(tt, start, offset)),
            EffectEnum::Read(region) => EffectEnum::Read(region.shift(tt, start, offset)),
            EffectEnum::Write(region) => EffectEnum::Write(region.shift(tt, start, offset)),
            EffectEnum::Divergent => return self,
        };
        tt.insert_effect(changed)
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
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
            (&EffectEnum::Read(a), &EffectEnum::Read(b)) => a.infer(b, tt, start, args),
            (&EffectEnum::Write(a), &EffectEnum::Write(b)) => a.infer(b, tt, start, args),
            (EffectEnum::Divergent, EffectEnum::Divergent) => Some(()),

            (EffectEnum::Generic(_), _) => None,
            (EffectEnum::Item(_), _) => None,
            (EffectEnum::Row(a), _) if a.is_empty() => None,
            (EffectEnum::Read(_), _) => None,
            (EffectEnum::Write(_), _) => None,
            (EffectEnum::Divergent, _) => None,

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
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            FunctionParameter::Data(ty) => FunctionParameter::Data(ty.subst(tt, start, args)),
            FunctionParameter::Lambda(sig) => FunctionParameter::Lambda(sig.subst(tt, start, args)),
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
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
        tt: &TypeTable,
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

impl FunctionSignature {
    pub fn apply(self, tt: &TypeTable, args: &[GenericArgument]) -> Self {
        let sig = tt[self].clone();
        let params = sig.params.subst(tt, 0, args);
        let thunk = sig.thunk.subst(tt, 0, args);
        tt.insert_function_signature(FunctionSignatureValue {
            type_params: None,
            implicit_regions: 0,
            params,
            thunk,
        })
    }
}

impl Substitute for FunctionSignature {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        let sig = tt[self].clone();
        let type_params = sig.type_params;
        let implicit_regions = sig.implicit_regions;
        let arity = type_params.as_ref().map(|params| params.len()).unwrap_or(0) + implicit_regions;
        let params = sig.params.subst(tt, start + arity, args);
        let thunk = sig.thunk.subst(tt, start + arity, args);
        tt.insert_function_signature(FunctionSignatureValue {
            type_params,
            implicit_regions,
            params,
            thunk,
        })
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        let sig = tt[self].clone();
        // NOTE: if we eventually have dependent kinds we need to substitute here too
        let type_params = sig.type_params;
        let implicit_regions = sig.implicit_regions;
        let arity = type_params.as_ref().map(|params| params.len()).unwrap_or(0) + implicit_regions;
        let params = sig.params.shift(tt, start + arity, offset);
        let thunk = sig.thunk.shift(tt, start + arity, offset);
        tt.insert_function_signature(FunctionSignatureValue {
            type_params,
            implicit_regions,
            params,
            thunk,
        })
    }
    fn infer(
        self,
        from: Self,
        tt: &TypeTable,
        start: usize,
        args: &mut Vec<Option<GenericArgument>>,
    ) -> Option<()> {
        let a = tt[self].clone();
        let b = tt[from].clone();

        // NOTE: if we eventually have dependent kinds this might fail
        assert_eq!(a.type_params, b.type_params);
        assert_eq!(a.implicit_regions, b.implicit_regions);
        let arity = a
            .type_params
            .as_ref()
            .map(|params| params.len())
            .unwrap_or(0)
            + a.implicit_regions;

        a.params.infer(b.params, tt, start + arity, args)?;
        a.thunk.infer(b.thunk, tt, start + arity, args)?;
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_table::{IntSize, Integer, KindEnum};

    #[test]
    fn test_shift() {
        let table = TypeTable::new();
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
        assert_eq!(lhs.subst(&table, 0, &[rhs]), lhs);
    }

    #[test]
    fn test_infer() {
        let table = TypeTable::new();

        let typ_kind = table.insert_kind(KindEnum::TYPE);
        let typ = table.insert_type(TypeEnum::Generic(GenericParameter {
            index: 1,
            apply: None,
        }));
        let effect = table.insert_effect(EffectEnum::empty());
        let sig = table.insert_function_signature(FunctionSignatureValue {
            type_params: Some(Arc::new([typ_kind])),
            implicit_regions: 0,
            params: Some(Arc::new([FunctionParameter::Data(typ)])),
            thunk: Thunk {
                returns: typ,
                effect,
            },
        });

        let inserted = table.insert_type(TypeEnum::Integer(Integer::unsigned(IntSize::Exact(32))));
        let inserted_sig = table.insert_function_signature(FunctionSignatureValue {
            type_params: Some(Arc::new([typ_kind])),
            implicit_regions: 0,
            params: Some(Arc::new([FunctionParameter::Data(inserted)])),
            thunk: Thunk {
                returns: inserted,
                effect,
            },
        });

        let mut generics = vec![None];
        assert_eq!(sig.infer(inserted_sig, &table, 0, &mut generics), Some(()));
        assert_eq!(
            generics[0],
            Some(GenericArgument {
                term: Term::Type(inserted),
                arity: None
            })
        );
    }
}
