use std::cell::OnceCell;
use std::collections::HashMap;
use std::ops::Index;
use std::sync::Arc;

use compact_str::CompactString;
use indexmap::IndexSet;

use crate::module::Module;

pub mod display;
pub mod lower;

#[derive(Default, Debug)]
pub struct TypeTable {
    kinds: IndexSet<KindEnum>,
    types: IndexSet<TypeEnum>,
    regions: IndexSet<RegionEnum>,
    effects: IndexSet<EffectEnum>,
    function_signatures: IndexSet<FunctionSignatureValue>,
}

#[derive(Default, Debug)]
pub struct Untyped {
    functions: Vec<OnceCell<FunctionDefinition>>,
    structs: Vec<OnceCell<StructDefinition>>,
    effects: Vec<OnceCell<EffectDefinition>>,
    items: HashMap<CompactString, Item>,
}

impl Untyped {
    fn push_function(&mut self) -> FunctionDef {
        let idx = self.functions.len();
        self.functions.push(OnceCell::new());
        FunctionDef(idx)
    }
    fn push_struct(&mut self) -> StructDef {
        let idx = self.structs.len();
        self.structs.push(OnceCell::new());
        StructDef(idx)
    }
    fn push_effect(&mut self) -> EffectDef {
        let idx = self.effects.len();
        self.effects.push(OnceCell::new());
        EffectDef(idx)
    }
    fn realize_function(&self, fun: FunctionDef, value: FunctionDefinition) {
        self.functions[fun.0]
            .set(value)
            .expect("ICE: function already realized");
    }
    fn realize_struct(&self, struc: StructDef, value: StructDefinition) {
        self.structs[struc.0]
            .set(value)
            .expect("ICE: struct already realized");
    }
    fn realize_effect(&self, effect: EffectDef, value: EffectDefinition) {
        self.effects[effect.0]
            .set(value)
            .expect("ICE: effect already realized")
    }
}

impl Index<FunctionDef> for Untyped {
    type Output = FunctionDefinition;

    fn index(&self, index: FunctionDef) -> &Self::Output {
        self.functions[index.0]
            .get()
            .expect("ICE: function not yet realized")
    }
}

impl Index<StructDef> for Untyped {
    type Output = StructDefinition;

    fn index(&self, index: StructDef) -> &Self::Output {
        self.structs[index.0]
            .get()
            .expect("ICE: struct not yet realized")
    }
}

impl Index<EffectDef> for Untyped {
    type Output = EffectDefinition;

    fn index(&self, index: EffectDef) -> &Self::Output {
        self.effects[index.0]
            .get()
            .expect("ICE: effect not yet realized")
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct FunctionDef(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct StructDef(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct EffectDef(usize);

// TODO
pub type Body = ();

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntrinsicFunction {
    // Div-related functions
    Loop,
    Unfounded,
    // debug printing
    PrintStr,
}

#[derive(Debug)]
pub enum FunctionDefinition {
    Expression {
        /// The amount of outer variables this function captures.
        /// Top level functions and default effect functions have a value of 0.
        captures: usize,
        body: Body,
    },
    Intrinsic(IntrinsicFunction),
}

#[derive(Debug)]
pub struct StructDefinition {
    pub members: Vec<StructMember>,
}

#[derive(Debug)]
pub enum EffectDefinition {
    Body {
        members: Vec<EffectMember>,
    },
    /// Does not allow user-defined handlers
    Intrinsic,
}

#[derive(Debug, Clone, Copy)]
pub enum Item {
    Alias(Kind, Term),
    Struct(Kind, StructDef),
    Effect(Kind, EffectDef),
    Function(FunctionSignature, Parent<FunctionDef>),
}

#[derive(Debug, Clone, Copy)]
pub enum Parent<T> {
    TopLevel(T),
    Effect(EffectDef),
}

#[derive(Debug)]
pub struct EffectMember {
    pub name: CompactString,
    pub signature: FunctionSignature,
}

#[derive(Debug)]
pub struct StructMember {
    pub name: CompactString,
    pub ty: Type,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum IntSize {
    Exact(usize),
    Register,
    Address,
    Index,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct GenericParameter {
    /// a De Bruijn index
    pub index: usize,
    pub apply: Option<Arc<[GenericArgument]>>,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Integer {
    signed: bool,
    size: IntSize,
}

impl Integer {
    pub const fn signed(size: IntSize) -> Self {
        Self { signed: true, size }
    }
    pub const fn unsigned(size: IntSize) -> Self {
        Self {
            signed: false,
            size,
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum TypeEnum {
    Generic(GenericParameter),
    Item(Module, CompactString, Option<Arc<[GenericArgument]>>),
    Integer(Integer),
    Boolean,
    Unit,
    Pointer(Type, Region),
    Slice(Type, Region),
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum RegionEnum {
    Generic(GenericParameter),
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum EffectEnum {
    Generic(GenericParameter),
    Item(Module, CompactString, Option<Arc<[GenericArgument]>>),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum SimpleKind {
    Type,
    Effect,
    Region,
    Constant(Type),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct KindEnum {
    params: Option<Arc<[Kind]>>,
    output: SimpleKind,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct FunctionSignatureValue {
    type_params: Option<Arc<[Kind]>>,
    params: Option<Arc<[FunctionParameter]>>,
    returns: FunctionReturns,
    effects: Arc<[Effect]>,
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum FunctionParameter {
    Data(Type),
    Lambda(FunctionSignature),
}

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum FunctionReturns {
    Data(Type),
    Never,
}

impl KindEnum {
    pub const TYPE: KindEnum = KindEnum {
        params: None,
        output: SimpleKind::Type,
    };
    pub const EFFECT: KindEnum = KindEnum {
        params: None,
        output: SimpleKind::Effect,
    };
    pub const REGION: KindEnum = KindEnum {
        params: None,
        output: SimpleKind::Region,
    };
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Type(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Region(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Effect(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Kind(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct FunctionSignature(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Term {
    Type(Type),
    Region(Region),
    Effect(Effect),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct GenericArgument {
    pub term: Term,
    pub arity: Option<usize>,
}

impl Index<Type> for TypeTable {
    type Output = TypeEnum;

    fn index(&self, index: Type) -> &Self::Output {
        &self.types[index.0]
    }
}

impl Index<Region> for TypeTable {
    type Output = RegionEnum;

    fn index(&self, index: Region) -> &Self::Output {
        &self.regions[index.0]
    }
}

impl Index<Effect> for TypeTable {
    type Output = EffectEnum;

    fn index(&self, index: Effect) -> &Self::Output {
        &self.effects[index.0]
    }
}

impl Index<Kind> for TypeTable {
    type Output = KindEnum;

    fn index(&self, index: Kind) -> &Self::Output {
        &self.kinds[index.0]
    }
}

impl Index<FunctionSignature> for TypeTable {
    type Output = FunctionSignatureValue;

    fn index(&self, index: FunctionSignature) -> &Self::Output {
        &self.function_signatures[index.0]
    }
}

impl TypeTable {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert_type(&mut self, value: TypeEnum) -> Type {
        Type(self.types.insert_full(value).0)
    }
    pub fn insert_region(&mut self, value: RegionEnum) -> Region {
        Region(self.regions.insert_full(value).0)
    }
    pub fn insert_effect(&mut self, value: EffectEnum) -> Effect {
        Effect(self.effects.insert_full(value).0)
    }
    pub fn insert_kind(&mut self, value: KindEnum) -> Kind {
        Kind(self.kinds.insert_full(value).0)
    }
    pub fn insert_function_signature(
        &mut self,
        value: FunctionSignatureValue,
    ) -> FunctionSignature {
        FunctionSignature(self.function_signatures.insert_full(value).0)
    }
}

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
            TypeEnum::Item(ref module, ref name, ref types) => TypeEnum::Item(
                module.clone(),
                name.clone(),
                types.clone().subst(tt, start, args),
            ),
            TypeEnum::Pointer(ty, region) => {
                TypeEnum::Pointer(ty.subst(tt, start, args), region.subst(tt, start, args))
            }
            TypeEnum::Slice(ty, region) => {
                TypeEnum::Slice(ty.subst(tt, start, args), region.subst(tt, start, args))
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
            TypeEnum::Item(ref module, ref name, ref types) => TypeEnum::Item(
                module.clone(),
                name.clone(),
                types.clone().shift(tt, start, offset),
            ),
            TypeEnum::Pointer(ty, region) => {
                TypeEnum::Pointer(ty.shift(tt, start, offset), region.shift(tt, start, offset))
            }
            TypeEnum::Slice(ty, region) => {
                TypeEnum::Slice(ty.shift(tt, start, offset), region.shift(tt, start, offset))
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
            EffectEnum::Item(ref module, ref name, ref types) => EffectEnum::Item(
                module.clone(),
                name.clone(),
                types.clone().subst(tt, start, args),
            ),
        };
        tt.insert_effect(changed)
    }
    fn shift(self, tt: &mut TypeTable, start: usize, offset: usize) -> Self {
        let changed = match tt[self] {
            EffectEnum::Generic(ref generic) => {
                EffectEnum::Generic(generic.clone().shift(tt, start, offset))
            }
            EffectEnum::Item(ref module, ref name, ref types) => EffectEnum::Item(
                module.clone(),
                name.clone(),
                types.clone().shift(tt, start, offset),
            ),
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
