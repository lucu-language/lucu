use std::sync::Arc;

use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionSignature,
    FunctionSignatureValue, GenericArgument, GenericParameter, Item, Region, RegionEnum, Term,
    Thunk, Type, TypeEnum, TypeTable,
};

pub trait Substitute {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self;
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self;
    fn subtype(self, to: Self, tt: &TypeTable) -> bool;
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool;
    fn no_holes(self, tt: &TypeTable) -> bool;
}

impl GenericParameter {
    fn instantiate(self, tt: &TypeTable, start: usize, arg: GenericArgument) -> Term {
        let arg = if start > 0 {
            arg.shift(tt, 0, start)
        } else {
            arg
        };
        match arg {
            GenericArgument::Instance { term, arity } => match &self.apply {
                Some(apply) => {
                    assert_eq!(arity, Some(apply.len()));
                    term.subst(tt, 0, apply)
                }
                None => {
                    assert_eq!(arity, None);
                    term
                }
            },
            GenericArgument::Hole => Term::Hole,
        }
    }
    fn infer_arg(self, from: Term, tt: &TypeTable, arg: &mut GenericArgument) -> bool {
        let arity = self.apply.as_deref().map(<[_]>::len);
        let inner = match self.apply {
            Some(_) => todo!(),
            None => from,
        };
        let new = GenericArgument::Instance { term: inner, arity };
        let old = *arg;

        // TODO: proper hole filling thing
        let do_subst = from.no_holes(tt)
            || match old {
                GenericArgument::Instance { term, .. } => match term {
                    Term::Type(ty) => tt[ty] == TypeEnum::Hole,
                    Term::Region(region) => tt[region] == RegionEnum::Hole,
                    Term::Effect(effect) => tt[effect] == EffectEnum::Hole,
                    Term::Constant(constant) => tt[constant] == ConstantEnum::Hole,
                    Term::Thunk(thunk) => {
                        tt[thunk.returns] == TypeEnum::Hole && tt[thunk.effect] == EffectEnum::Hole
                    }
                    Term::Hole => true,
                },
                GenericArgument::Hole => true,
            };
        if do_subst {
            *arg = new;
            true
        } else {
            !new.subtype(old, tt) && !old.subtype(new, tt)
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
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        assert_eq!(self.len(), to.len());
        Iterator::zip(self.iter(), to.iter()).all(|(&a, &b)| a.subtype(b, tt))
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        Iterator::zip(self.iter().copied(), from.iter().copied())
            .all(|(a, b)| a.infer(b, tt, start, args))
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        self.iter().all(|t| t.no_holes(tt))
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
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        assert!(self.is_some() == to.is_some());
        Option::zip(self, to).is_none_or(|(a, b)| a.subtype(b, tt))
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        assert!(self.is_some() == from.is_some());
        Option::zip(self, from).is_none_or(|(a, b)| a.infer(b, tt, start, args))
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        self.is_none_or(|t| t.no_holes(tt))
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
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        // FIXME: this assumes all generics are covariant
        self.module == to.module && self.name == to.name && self.apply.subtype(to.apply, tt)
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        // FIXME: this assumes all generics are covariant
        self.module == from.module
            && self.name == from.name
            && self.apply.infer(from.apply, tt, start, args)
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        self.apply.no_holes(tt)
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
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        // FIXME: this assumes all generics are covariant
        self.index == to.index && self.apply.subtype(to.apply, tt)
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        // FIXME: this assumes all generics are covariant
        self.index == from.index
            && self
                .apply
                .clone()
                .infer(from.apply.clone(), tt, start, args)
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        self.apply.no_holes(tt)
    }
}

impl Substitute for GenericArgument {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            GenericArgument::Instance { term, arity } => GenericArgument::Instance {
                term: term.subst(tt, start + arity.unwrap_or(0), args),
                arity,
            },
            GenericArgument::Hole => GenericArgument::Hole,
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        match self {
            GenericArgument::Instance { term, arity } => GenericArgument::Instance {
                term: term.shift(tt, start + arity.unwrap_or(0), offset),
                arity,
            },
            GenericArgument::Hole => GenericArgument::Hole,
        }
    }
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        match (self, to) {
            (
                GenericArgument::Instance {
                    term: term_from,
                    arity: arity_from,
                },
                GenericArgument::Instance {
                    term: term_to,
                    arity: arity_to,
                },
            ) => {
                assert_eq!(arity_from, arity_to);
                term_from.subtype(term_to, tt)
            }
            _ => true,
        }
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        match (self, from) {
            (
                GenericArgument::Instance {
                    term: term_to,
                    arity: arity_to,
                },
                GenericArgument::Instance {
                    term: term_from,
                    arity: arity_from,
                },
            ) => {
                assert_eq!(arity_to, arity_from);
                term_to.infer(term_from, tt, start + arity_to.unwrap_or(0), args)
            }
            _ => true,
        }
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        match self {
            GenericArgument::Instance { term, .. } => term.no_holes(tt),
            GenericArgument::Hole => false,
        }
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
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        self.returns.subtype(to.returns, tt) && self.effect.subtype(to.effect, tt)
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        self.returns.infer(from.returns, tt, start, args)
            && self.effect.infer(from.effect, tt, start, args)
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        self.returns.no_holes(tt) && self.effect.no_holes(tt)
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
            Term::Hole => Term::Hole,
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        match self {
            Term::Type(ty) => Term::Type(ty.shift(tt, start, offset)),
            Term::Region(region) => Term::Region(region.shift(tt, start, offset)),
            Term::Effect(effect) => Term::Effect(effect.shift(tt, start, offset)),
            Term::Constant(constant) => Term::Constant(constant.shift(tt, start, offset)),
            Term::Thunk(thunk) => Term::Thunk(thunk.shift(tt, start, offset)),
            Term::Hole => Term::Hole,
        }
    }
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        match (self, to) {
            (Term::Type(a), Term::Type(b)) => a.subtype(b, tt),
            (Term::Region(a), Term::Region(b)) => a.subtype(b, tt),
            (Term::Effect(a), Term::Effect(b)) => a.subtype(b, tt),
            (Term::Constant(a), Term::Constant(b)) => a.subtype(b, tt),
            (Term::Thunk(a), Term::Thunk(b)) => a.subtype(b, tt),
            (Term::Hole, _) | (_, Term::Hole) => true,
            _ => panic!(),
        }
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        match (self, from) {
            (Term::Type(a), Term::Type(b)) => a.infer(b, tt, start, args),
            (Term::Region(a), Term::Region(b)) => a.infer(b, tt, start, args),
            (Term::Effect(a), Term::Effect(b)) => a.infer(b, tt, start, args),
            (Term::Constant(a), Term::Constant(b)) => a.infer(b, tt, start, args),
            (Term::Thunk(a), Term::Thunk(b)) => a.infer(b, tt, start, args),
            (Term::Hole, _) | (_, Term::Hole) => true,
            _ => panic!(),
        }
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        match self {
            Term::Type(ty) => ty.no_holes(tt),
            Term::Region(region) => region.no_holes(tt),
            Term::Effect(effect) => effect.no_holes(tt),
            Term::Constant(constant) => constant.no_holes(tt),
            Term::Thunk(thunk) => thunk.no_holes(tt),
            Term::Hole => false,
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
                        Term::Hole => ConstantEnum::Hole,
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
            | ConstantEnum::Zero
            | ConstantEnum::Hole => return self,
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
            | ConstantEnum::Zero
            | ConstantEnum::Hole => return self,
        };
        tt.insert_constant(changed)
    }
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        self == to
            || match (&tt[self], &tt[to]) {
                (ConstantEnum::Generic(a), ConstantEnum::Generic(b)) => {
                    a.clone().subtype(b.clone(), tt)
                }
                (ConstantEnum::Hole, _) | (_, ConstantEnum::Hole) => true,
                _ => false,
            }
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        match (&tt[self], &tt[from]) {
            (ConstantEnum::Generic(param), _) if param.index >= start => param.clone().infer_arg(
                Term::Constant(from),
                tt,
                &mut args[args.len() - 1 - (param.index - start)],
            ),
            (ConstantEnum::Generic(a), ConstantEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (ConstantEnum::True, ConstantEnum::True) => true,
            (ConstantEnum::False, ConstantEnum::False) => true,
            (ConstantEnum::Integer(a), ConstantEnum::Integer(b)) => a == b,
            (ConstantEnum::String(a), ConstantEnum::String(b)) => a == b,
            (ConstantEnum::Character(a), ConstantEnum::Character(b)) => a == b,
            (ConstantEnum::Zero, ConstantEnum::Zero) => true,
            (ConstantEnum::Hole, _) | (_, ConstantEnum::Hole) => true,
            _ => false,
        }
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            ConstantEnum::Generic(generic_parameter) => generic_parameter.clone().no_holes(tt),
            ConstantEnum::True => true,
            ConstantEnum::False => true,
            ConstantEnum::Integer(_) => true,
            ConstantEnum::String(_) => true,
            ConstantEnum::Character(_) => true,
            ConstantEnum::Zero => true,
            ConstantEnum::Hole => false,
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
                        Term::Hole => TypeEnum::Hole,
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
            TypeEnum::Integer(_)
            | TypeEnum::Boolean
            | TypeEnum::Unit
            | TypeEnum::Never
            | TypeEnum::NullPointer
            | TypeEnum::Hole => {
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
            TypeEnum::Integer(_)
            | TypeEnum::Boolean
            | TypeEnum::Unit
            | TypeEnum::Never
            | TypeEnum::NullPointer
            | TypeEnum::Hole => {
                return self;
            }
        };
        tt.insert_type(changed)
    }
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        self == to
            || match (&tt[self], &tt[to]) {
                (TypeEnum::Generic(a), TypeEnum::Generic(b)) => a.clone().subtype(b.clone(), tt),
                (TypeEnum::Item(a), TypeEnum::Item(b)) => a.clone().subtype(b.clone(), tt),
                (TypeEnum::Maybe(a), TypeEnum::Maybe(b)) => a.subtype(*b, tt),
                (TypeEnum::Pointer(ta, ra), TypeEnum::Pointer(tb, rb)) => {
                    ta.subtype(*tb, tt) && ra.subtype(*rb, tt)
                }
                (TypeEnum::PointerSlice(ta, ra, sa), TypeEnum::PointerSlice(tb, rb, sb)) => {
                    ta.subtype(*tb, tt) && ra.subtype(*rb, tt) && sa == sb
                }
                (TypeEnum::Array(ta, ca, sa), TypeEnum::Array(tb, cb, sb)) => {
                    ta.subtype(*tb, tt) && ca.subtype(*cb, tt) && sa == sb
                }
                (TypeEnum::NullPointer, TypeEnum::Maybe(b))
                    if matches!(
                        tt[*b],
                        TypeEnum::Pointer(_, _) | TypeEnum::PointerSlice(_, _, _)
                    ) =>
                {
                    true
                }
                (TypeEnum::Never, _) => true,
                (TypeEnum::Hole, _) | (_, TypeEnum::Hole) => true,
                _ => false,
            }
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        match (&tt[self], &tt[from]) {
            (TypeEnum::Generic(param), _) if param.index >= start => param.clone().infer_arg(
                Term::Type(from),
                tt,
                &mut args[args.len() - 1 - (param.index - start)],
            ),
            (TypeEnum::Generic(a), TypeEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (TypeEnum::Item(a), TypeEnum::Item(b)) => a.clone().infer(b.clone(), tt, start, args),
            (TypeEnum::Integer(a), TypeEnum::Integer(b)) => a == b,
            (TypeEnum::Boolean, TypeEnum::Boolean) => true,
            (TypeEnum::Unit, TypeEnum::Unit) => true,
            (TypeEnum::Never, TypeEnum::Never) => true,
            (TypeEnum::NullPointer, TypeEnum::NullPointer) => true,
            (TypeEnum::Maybe(a), TypeEnum::Maybe(b)) => a.infer(*b, tt, start, args),
            (TypeEnum::Pointer(ta, ra), TypeEnum::Pointer(tb, rb)) => {
                ta.infer(*tb, tt, start, args) && ra.infer(*rb, tt, start, args)
            }
            (TypeEnum::PointerSlice(ta, ra, sa), TypeEnum::PointerSlice(tb, rb, sb)) => {
                ta.infer(*tb, tt, start, args) && ra.infer(*rb, tt, start, args) && sa == sb
            }
            (TypeEnum::Array(ta, ca, sa), TypeEnum::Array(tb, cb, sb)) => {
                ta.infer(*tb, tt, start, args) && ca.infer(*cb, tt, start, args) && sa == sb
            }
            (TypeEnum::Never, _) | (_, TypeEnum::Never) => true,
            (TypeEnum::Hole, _) | (_, TypeEnum::Hole) => true,
            _ => false,
        }
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            TypeEnum::Generic(generic_parameter) => generic_parameter.clone().no_holes(tt),
            TypeEnum::Item(item) => item.clone().no_holes(tt),
            TypeEnum::Integer(_) => true,
            TypeEnum::Boolean => true,
            TypeEnum::Unit => true,
            TypeEnum::Never => true,
            TypeEnum::NullPointer => true,
            TypeEnum::Pointer(ty, region) => ty.no_holes(tt) && region.no_holes(tt),
            TypeEnum::PointerSlice(ty, region, _) => ty.no_holes(tt) && region.no_holes(tt),
            TypeEnum::Array(ty, constant, _) => ty.no_holes(tt) && constant.no_holes(tt),
            TypeEnum::Maybe(ty) => ty.no_holes(tt),
            TypeEnum::Hole => false,
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
                        Term::Hole => RegionEnum::Hole,
                        _ => panic!("ICE: unexpected kind of generic argument"),
                    }
                } else {
                    RegionEnum::Generic(generic)
                }
            }
            RegionEnum::Static | RegionEnum::Heap | RegionEnum::Hole => return self,
        };
        tt.insert_region(changed)
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            RegionEnum::Generic(ref generic) => {
                RegionEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            RegionEnum::Static | RegionEnum::Heap | RegionEnum::Hole => return self,
        };
        tt.insert_region(changed)
    }
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        self == to
            || match (&tt[self], &tt[to]) {
                (RegionEnum::Generic(a), RegionEnum::Generic(b)) => {
                    a.clone().subtype(b.clone(), tt)
                }
                (RegionEnum::Hole, _) | (_, RegionEnum::Hole) => true,
                _ => false,
            }
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        match (&tt[self], &tt[from]) {
            (RegionEnum::Generic(param), _) if param.index >= start => param.clone().infer_arg(
                Term::Region(from),
                tt,
                &mut args[args.len() - 1 - (param.index - start)],
            ),
            (RegionEnum::Generic(a), RegionEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (RegionEnum::Static, RegionEnum::Static) => true,
            (RegionEnum::Heap, RegionEnum::Heap) => true,
            (RegionEnum::Hole, _) | (_, RegionEnum::Hole) => true,
            _ => false,
        }
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            RegionEnum::Generic(generic_parameter) => generic_parameter.clone().no_holes(tt),
            RegionEnum::Static => true,
            RegionEnum::Heap => true,
            RegionEnum::Hole => false,
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
                        Term::Hole => EffectEnum::Hole,
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
            EffectEnum::Divergent | EffectEnum::World | EffectEnum::Hole => return self,
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
            EffectEnum::Divergent | EffectEnum::World | EffectEnum::Hole => return self,
        };
        tt.insert_effect(changed)
    }
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        self == to
            || match (&tt[self], &tt[to]) {
                (EffectEnum::Generic(a), EffectEnum::Generic(b)) => {
                    a.clone().subtype(b.clone(), tt)
                }
                (EffectEnum::Item(a), EffectEnum::Item(b)) => a.clone().subtype(b.clone(), tt),
                (EffectEnum::Row(_a), EffectEnum::Row(_b)) => todo!(),
                (EffectEnum::Read(a), EffectEnum::Read(b)) => a.subtype(*b, tt),
                (EffectEnum::Write(a), EffectEnum::Write(b)) => a.subtype(*b, tt),
                (EffectEnum::Hole, _) | (_, EffectEnum::Hole) => true,
                _ => false,
            }
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        match (&tt[self], &tt[from]) {
            (EffectEnum::Generic(param), _) if param.index >= start => param.clone().infer_arg(
                Term::Effect(from),
                tt,
                &mut args[args.len() - 1 - (param.index - start)],
            ),
            (EffectEnum::Generic(a), EffectEnum::Generic(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (EffectEnum::Item(a), EffectEnum::Item(b)) => {
                a.clone().infer(b.clone(), tt, start, args)
            }
            (EffectEnum::Row(a), EffectEnum::Row(b)) if a.is_empty() && b.is_empty() => true,
            (EffectEnum::Read(a), EffectEnum::Read(b)) => a.infer(*b, tt, start, args),
            (EffectEnum::Write(a), EffectEnum::Write(b)) => a.infer(*b, tt, start, args),
            (EffectEnum::Divergent, EffectEnum::Divergent) => true,
            (EffectEnum::World, EffectEnum::World) => true,
            (EffectEnum::Row(_), _) => {
                // This is the one reason why we can't completely accept or deny a generics inference...
                // If we don't have enough information to accept or deny, we accept *without* inferring.
                // Feel free to be super duper smart and add more code here later if you dare,
                // but we should probably not do it like this and use a sort of Hindley-Milner with row types.
                true
            }
            (EffectEnum::Hole, _) | (_, EffectEnum::Hole) => true,
            _ => false,
        }
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        match &tt[self] {
            EffectEnum::Generic(generic_parameter) => generic_parameter.clone().no_holes(tt),
            EffectEnum::Item(item) => item.clone().no_holes(tt),
            EffectEnum::Row(effects) => effects.iter().all(|e| e.no_holes(tt)),
            EffectEnum::Read(region) | EffectEnum::Write(region) => region.no_holes(tt),
            EffectEnum::Divergent => true,
            EffectEnum::World => true,
            EffectEnum::Hole => false,
        }
    }
}

impl Substitute for FunctionParameter {
    fn subst(self, tt: &TypeTable, start: usize, args: &[GenericArgument]) -> Self {
        match self {
            FunctionParameter::Data(ty) => FunctionParameter::Data(ty.subst(tt, start, args)),
            FunctionParameter::Lambda(sig) => FunctionParameter::Lambda(sig.subst(tt, start, args)),
            FunctionParameter::Hole => FunctionParameter::Hole,
        }
    }
    fn shift(self, tt: &TypeTable, start: usize, offset: usize) -> Self {
        match self {
            FunctionParameter::Data(ty) => FunctionParameter::Data(ty.shift(tt, start, offset)),
            FunctionParameter::Lambda(sig) => {
                FunctionParameter::Lambda(sig.shift(tt, start, offset))
            }
            FunctionParameter::Hole => FunctionParameter::Hole,
        }
    }
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        match (self, to) {
            (FunctionParameter::Data(a), FunctionParameter::Data(b)) => a.subtype(b, tt),
            (FunctionParameter::Lambda(a), FunctionParameter::Lambda(b)) => a.subtype(b, tt),
            (FunctionParameter::Hole, _) | (_, FunctionParameter::Hole) => true,
            _ => panic!(),
        }
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        match (self, from) {
            (FunctionParameter::Data(a), FunctionParameter::Data(b)) => a.infer(b, tt, start, args),
            (FunctionParameter::Lambda(a), FunctionParameter::Lambda(b)) => {
                a.infer(b, tt, start, args)
            }
            (FunctionParameter::Hole, _) | (_, FunctionParameter::Hole) => true,
            _ => panic!(),
        }
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        match self {
            FunctionParameter::Data(ty) => ty.no_holes(tt),
            FunctionParameter::Lambda(function_signature) => function_signature.no_holes(tt),
            FunctionParameter::Hole => false,
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
    pub fn infer_params(
        self,
        from: &[FunctionParameter],
        tt: &TypeTable,
        args: &mut [GenericArgument],
    ) -> bool {
        tt[self].params.as_ref().is_none_or(|p| {
            Iterator::zip(p.iter(), from.iter()).all(|(a, b)| a.infer(*b, tt, 0, args))
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
    fn subtype(self, to: Self, tt: &TypeTable) -> bool {
        let (from, to) = (tt[self].clone(), tt[to].clone());
        from.type_params == to.type_params
            && from.implicit_regions == to.implicit_regions
            && to.params.subtype(from.params, tt)
            && from.thunk.subtype(to.thunk, tt)
    }
    fn infer(self, from: Self, tt: &TypeTable, start: usize, args: &mut [GenericArgument]) -> bool {
        let (to, from) = (tt[self].clone(), tt[from].clone());
        assert_eq!(to.type_params, from.type_params);
        assert_eq!(to.implicit_regions, from.implicit_regions);
        let arity = to.arity();
        to.params.infer(from.params, tt, start + arity, args)
            && to.thunk.infer(from.thunk, tt, start + arity, args)
    }
    fn no_holes(self, tt: &TypeTable) -> bool {
        let sig = tt[self].clone();
        sig.params.no_holes(tt) && sig.thunk.no_holes(tt)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_table::{IntSize, Integer, KindEnum};

    #[test]
    fn test_shift() {
        let table = TypeTable::new();
        let lhs = GenericArgument::Instance {
            term: Term::Type(table.insert_type(TypeEnum::Generic(GenericParameter {
                index: 1,
                apply: None,
            }))),
            arity: Some(1),
        };
        let rhs = GenericArgument::Instance {
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

        let mut generics = vec![GenericArgument::Hole];
        assert!(sig.infer(inserted_sig, &table, 0, &mut generics));
        assert_eq!(
            generics[0],
            GenericArgument::Instance {
                term: Term::Type(inserted),
                arity: None
            }
        );
    }
}
