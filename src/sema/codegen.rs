use std::{
    collections::{HashMap, HashSet},
    fmt::{self},
};

use either::Either;

use crate::{
    ast::{
        self, BinOp, EffFunIdx, EffIdx, ExprIdx, Expression, Ident, PackageIdx, ParamIdx, UnOp, AST,
    },
    error::{Error, Errors, Range},
    sema::Instruction,
    vecmap::{VecMap, VecSet},
    Target,
};

use super::{
    get_param, get_value, get_value_mut, Assoc, AssocDef, AssocIdx, Block, BlockIdx, Effect,
    EffectIdent, FunIdx, FunImpl, FunSign, Generic, GenericIdx, GenericParams, GenericVal,
    Generics, Handler, HandlerIdx, InstrIdx, IntSize, LazyIdx, Param, ReturnType, SemIR, Type,
    TypeConstraints, TypeIdx, Value,
};

struct SemCtx<'a> {
    ir: SemIR,
    ast: &'a AST,
    errors: &'a mut Errors,
    packages: VecMap<PackageIdx, Scope>,
}

#[derive(Clone, Copy)]
enum FunIdent {
    Top(FunIdx),
    Effect(EffIdx, EffFunIdx),
}

impl FunIdent {
    fn ident(self, ctx: &SemCtx) -> Ident {
        match self {
            FunIdent::Top(idx) => ctx.ast.functions[idx].decl.name,
            FunIdent::Effect(eff, idx) => ctx.ast.effects[eff].functions[idx].name,
        }
    }
}

struct ScopeStack {
    scopes: Vec<Scope>,
    package: PackageIdx,
}

#[derive(Clone)]
struct Variable {
    value: Value,
    ty: TypeIdx,
    mutable: bool,
}

#[derive(Default)]
struct Scope {
    funs: HashMap<String, FunIdent>,
    effects: HashMap<String, GenericVal<EffIdx>>,
    types: HashMap<String, TypeIdx>,
    generics: HashMap<String, Generic>,
    values: HashMap<String, Variable>,
}

impl ScopeStack {
    fn new(package: PackageIdx) -> ScopeStack {
        Self {
            scopes: Vec::new(),
            package,
        }
    }
    fn search<T>(&self, ctx: &SemCtx, f: impl FnMut(&Scope) -> Option<T>) -> Option<T> {
        let iter = self
            .scopes
            .iter()
            .rev()
            .chain([&ctx.packages[self.package], &ctx.packages[ctx.ast.preamble]]);
        iter.map(f).find(Option::is_some).flatten()
    }

    fn push(&mut self) {
        self.scopes.push(Scope::default());
    }
    fn pop(&mut self) {
        self.scopes.pop();
    }
    fn child<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.push();
        let t = f(self);
        self.pop();
        t
    }
    fn top(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    fn get_function(&self, ctx: &SemCtx, name: &str) -> Option<FunIdent> {
        self.search(ctx, |s| s.funs.get(name).copied())
    }
    fn get_effect(&self, ctx: &SemCtx, name: &str) -> Option<GenericVal<EffIdx>> {
        self.search(ctx, |s| s.effects.get(name).copied())
    }
    fn get_type(&self, ctx: &SemCtx, name: &str) -> Option<TypeIdx> {
        self.search(ctx, |s| s.types.get(name).copied())
    }
    fn get_generic(&self, ctx: &SemCtx, name: &str) -> Option<Generic> {
        self.search(ctx, |s| s.generics.get(name).copied())
    }

    fn try_function(&self, ctx: &mut SemCtx, id: Ident) -> Option<FunIdent> {
        let name = &ctx.ast.idents[id];
        match self.get_function(ctx, &name.0) {
            Some(fun) => Some(fun),
            None => {
                ctx.errors.push(name.with(Error::UnknownFunction));
                None
            }
        }
    }
    fn try_effect(&self, ctx: &mut SemCtx, id: Ident) -> Option<GenericVal<EffIdx>> {
        let name = &ctx.ast.idents[id];
        match self.get_effect(ctx, &name.0) {
            Some(eff) => Some(eff),
            None => {
                ctx.errors.push(name.with(Error::UnknownEffect));
                None
            }
        }
    }
    fn try_type(&self, ctx: &mut SemCtx, id: Ident) -> TypeIdx {
        let name = &ctx.ast.idents[id];
        match self.get_type(ctx, &name.0) {
            Some(ty) => ty,
            None => {
                ctx.errors.push(name.with(Error::UnknownType));
                TYPE_UNKNOWN
            }
        }
    }

    fn try_package(&self, ctx: &mut SemCtx, id: Ident) -> Option<PackageIdx> {
        let name = &ctx.ast.idents[id];
        match ctx.ast.packages[self.package].imports.get(&name.0).copied() {
            Some(pkg) => Some(pkg),
            None => {
                ctx.errors.push(name.with(Error::UnknownPackage));
                None
            }
        }
    }
    fn try_package_effect(
        &self,
        ctx: &mut SemCtx,
        pkg: Ident,
        id: Ident,
    ) -> Option<GenericVal<EffIdx>> {
        let package = self.try_package(ctx, pkg)?;
        let name = &ctx.ast.idents[id];
        match ctx.packages[package].effects.get(&name.0).copied() {
            Some(eff) => Some(eff),
            None => {
                ctx.errors
                    .push(name.with(Error::UnknownPackageEffect(ctx.ast.idents[pkg].empty())));
                None
            }
        }
    }
    fn try_package_type(&self, ctx: &mut SemCtx, pkg: Ident, id: Ident) -> TypeIdx {
        let Some(package) = self.try_package(ctx, pkg) else {
            return TYPE_UNKNOWN;
        };
        let name = &ctx.ast.idents[id];
        match ctx.packages[package].types.get(&name.0).copied() {
            Some(eff) => eff,
            None => {
                ctx.errors
                    .push(name.with(Error::UnknownPackageType(ctx.ast.idents[pkg].empty())));
                TYPE_UNKNOWN
            }
        }
    }
}

const TYPE_UNKNOWN: TypeIdx = TypeIdx(0 << 2);
const TYPE_NONE: TypeIdx = TypeIdx(1 << 2);
const TYPE_NEVER: TypeIdx = TypeIdx(2 << 2);
const TYPE_DATATYPE: TypeIdx = TypeIdx(3 << 2);
const TYPE_EFFECT: TypeIdx = TypeIdx(4 << 2);
const TYPE_SELF: TypeIdx = TypeIdx(5 << 2);
const TYPE_USIZE: TypeIdx = TypeIdx(6 << 2);
const TYPE_BOOL: TypeIdx = TypeIdx(7 << 2);
const TYPE_INT: TypeIdx = TypeIdx(8 << 2);
const TYPE_STR: TypeIdx = TypeIdx(9 << 2);
const TYPE_CHAR: TypeIdx = TypeIdx(10 << 2);
const TYPE_U8: TypeIdx = TypeIdx(11 << 2);

struct FmtType<'a>(&'a SemIR, TypeIdx);

impl fmt::Display for FmtType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'")?;
        self.1.display(self.0, &GenericParams::default(), f)?;
        write!(f, "'")?;
        Ok(())
    }
}

impl SemCtx<'_> {
    fn lazy_handler(&mut self, _: &mut Generics, ty: TypeIdx, _: ast::TypeIdx) -> TypeIdx {
        let idx = self.ir.lazy_handlers.push(LazyIdx, None);
        self.insert_type(Type::LazyHandler(ty, idx), false, false)
    }
    fn no_handler(&mut self, _: &mut Generics, _: TypeIdx, ty: ast::TypeIdx) -> TypeIdx {
        self.errors
            .push(self.ast.types[ty].with(Error::NotEnoughInfo));
        TYPE_UNKNOWN
    }
    fn insert_type(&mut self, ty: Type, is_const: bool, is_lent: bool) -> TypeIdx {
        self.ir
            .types
            .insert(|idx| TypeIdx::new(idx, is_const, is_lent), ty)
            .clone()
    }
    fn push_handler(&mut self, handler: Handler) -> HandlerIdx {
        self.ir.handlers.push(HandlerIdx, handler)
    }
    fn analyze_fail(
        &mut self,
        scope: &mut ScopeStack,
        fail: ast::FailType,
        generics: Option<&mut Generics>,
        generic_handler: bool,
        handler_output: &mut impl FnMut(&mut Self, &mut Generics, TypeIdx, ast::TypeIdx) -> TypeIdx,
    ) -> TypeIdx {
        match fail {
            ast::FailType::Never => TYPE_NEVER,
            ast::FailType::None => TYPE_NONE,
            ast::FailType::Some(ty) => {
                self.analyze_type(scope, ty, generics, generic_handler, handler_output)
            }
        }
    }
    fn translate_generics(
        &mut self,
        ty: TypeIdx,
        generic_params: &GenericParams,
        parent_generics: usize,
        handler_self: TypeIdx,
        assoc_types: Option<&Vec<(AssocIdx, TypeIdx)>>,
    ) -> TypeIdx {
        let translate_generic =
            |ctx: &mut Self, generic: Generic| match get_param(generic_params, generic.idx) {
                Some(ty) => match ctx.ir.types[ty] {
                    Type::Generic(generic) => generic,
                    _ => todo!(),
                },
                None => generic,
            };
        match self.ir.types[ty] {
            Type::DataType(ref constraints) => match *constraints {
                TypeConstraints::None => ty,
                TypeConstraints::Handler(ref effect, fail) => {
                    let effect = match *effect {
                        GenericVal::Literal(ref ident) => {
                            let effect = ident.effect;
                            let params = ident.generic_params.clone();
                            let params =
                                GenericParams::from_iter(params.into_iter().map(|(idx, ty)| {
                                    (
                                        idx,
                                        self.translate_generics(
                                            ty,
                                            generic_params,
                                            parent_generics,
                                            handler_self,
                                            assoc_types,
                                        ),
                                    )
                                }));
                            GenericVal::Literal(EffectIdent {
                                effect,
                                generic_params: params,
                            })
                        }
                        GenericVal::Generic(idx) => {
                            let generic = translate_generic(
                                self,
                                Generic {
                                    idx,
                                    typeof_ty: TYPE_EFFECT,
                                },
                            );
                            GenericVal::Generic(generic.idx)
                        }
                    };
                    let fail = self.translate_generics(
                        fail,
                        generic_params,
                        parent_generics,
                        handler_self,
                        assoc_types,
                    );
                    self.insert_type(
                        Type::DataType(TypeConstraints::Handler(effect, fail)),
                        ty.is_const(),
                        ty.is_lent(),
                    )
                }
                TypeConstraints::BoundHandler(ref effect) => {
                    let effect = match *effect {
                        GenericVal::Literal(ref ident) => {
                            let effect = ident.effect;
                            let params = ident.generic_params.clone();
                            let params =
                                GenericParams::from_iter(params.into_iter().map(|(idx, ty)| {
                                    (
                                        idx,
                                        self.translate_generics(
                                            ty,
                                            generic_params,
                                            parent_generics,
                                            handler_self,
                                            assoc_types,
                                        ),
                                    )
                                }));
                            GenericVal::Literal(EffectIdent {
                                effect,
                                generic_params: params,
                            })
                        }
                        GenericVal::Generic(idx) => {
                            let generic = translate_generic(
                                self,
                                Generic {
                                    idx,
                                    typeof_ty: TYPE_EFFECT,
                                },
                            );
                            GenericVal::Generic(generic.idx)
                        }
                    };
                    self.insert_type(
                        Type::DataType(TypeConstraints::BoundHandler(effect)),
                        ty.is_const(),
                        ty.is_lent(),
                    )
                }
            },
            Type::AssocType {
                assoc,
                handler,
                effect,
                generic_params: ref params,
            } => {
                let params = params.clone();
                let params = GenericParams::from_iter(params.into_iter().map(|(idx, ty)| {
                    (
                        idx,
                        self.translate_generics(
                            ty,
                            generic_params,
                            parent_generics,
                            handler_self,
                            assoc_types,
                        ),
                    )
                }));

                let ty = self.translate_generics(
                    assoc.typeof_ty,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                let handler = self.translate_generics(
                    handler,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );

                if let Some(assoc_types) = assoc_types.filter(|_| handler == handler_self) {
                    self.translate_generics(
                        get_value(assoc_types, &assoc.idx).copied().unwrap(),
                        &params,
                        parent_generics,
                        handler_self,
                        Some(assoc_types),
                    )
                } else {
                    self.insert_type(
                        Type::AssocType {
                            assoc: Assoc {
                                idx: assoc.idx,
                                typeof_ty: ty,
                            },
                            handler,
                            effect,
                            generic_params: params,
                        },
                        ty.is_const(),
                        ty.is_lent(),
                    )
                }
            }
            Type::Handler {
                idx,
                generic_params: ref params,
                bound,
            } => {
                let params = params.clone();
                let params = GenericParams::from_iter(params.into_iter().map(|(idx, ty)| {
                    (
                        idx,
                        self.translate_generics(
                            ty,
                            generic_params,
                            parent_generics,
                            handler_self,
                            assoc_types,
                        ),
                    )
                }));

                self.insert_type(
                    Type::Handler {
                        idx,
                        generic_params: params,
                        bound,
                    },
                    ty.is_const(),
                    ty.is_lent(),
                )
            }
            Type::Generic(generic) => match get_param(generic_params, generic.idx) {
                Some(ty) => ty,
                None => ty,
            },
            Type::Pointer(inner) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::Pointer(inner), ty.is_const(), ty.is_lent())
            }
            Type::ConstArray(size, inner) => {
                let size = match size {
                    GenericVal::Literal(_) => size,
                    GenericVal::Generic(idx) => {
                        let generic = translate_generic(
                            self,
                            Generic {
                                idx,
                                typeof_ty: TYPE_USIZE,
                            },
                        );
                        GenericVal::Generic(generic.idx)
                    }
                };
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::ConstArray(size, inner), ty.is_const(), ty.is_lent())
            }
            Type::Slice(inner) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::Slice(inner), ty.is_const(), ty.is_lent())
            }
            Type::LazyHandler(inner, idx) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::LazyHandler(inner, idx), ty.is_const(), ty.is_lent())
            }
            Type::HandlerSelf => handler_self,

            Type::Effect
            | Type::Integer(_, _)
            | Type::Str
            | Type::Char
            | Type::Bool
            | Type::None
            | Type::Unknown
            | Type::Never => ty,
        }
    }
    fn analyze_generic(
        &mut self,
        scope: &mut ScopeStack,
        id: Ident,
        typeof_generic: TypeIdx,
        generics: Option<&mut Generics>,
    ) -> Option<Generic> {
        let name = &self.ast.idents[id];
        match scope.get_generic(self, &name.0) {
            Some(generic) => {
                // check if generic type matches
                self.check_move_rev(
                    typeof_generic,
                    generic.typeof_ty,
                    &mut TypeError {
                        loc: name.empty(),
                        def: None,
                        layers: Vec::new(),
                    },
                );
                Some(generic)
            }
            None => match generics {
                Some(generics) => {
                    let idx = self.ir.generic_names.push(GenericIdx, name.0.clone());
                    let value = Generic {
                        idx,
                        typeof_ty: typeof_generic,
                    };
                    generics.push(value);
                    scope.top().generics.insert(name.0.clone(), value);
                    Some(value)
                }
                None => {
                    self.errors.push(name.with(Error::UnknownGeneric));
                    None
                }
            },
        }
    }
    fn analyze_type(
        &mut self,
        scope: &mut ScopeStack,
        ty: ast::TypeIdx,
        mut generics: Option<&mut Generics>,
        generic_handler: bool,
        handler_output: &mut impl FnMut(&mut Self, &mut Generics, TypeIdx, ast::TypeIdx) -> TypeIdx,
    ) -> TypeIdx {
        use ast::Type as T;
        match self.ast.types[ty].0 {
            T::Never => TYPE_NEVER,
            T::Error => TYPE_UNKNOWN,
            T::Path(ref id) => {
                // TODO: handle generic params
                match id.ident.package {
                    Some(pkg) => scope.try_package_type(self, pkg, id.ident.ident),
                    None => scope.try_type(self, id.ident.ident),
                }
            }
            T::Handler(ref id, fail) => {
                // get signature
                let params = match id.params {
                    Some(ref params) => params
                        .iter()
                        .copied()
                        .map(|ty| {
                            self.analyze_type(
                                scope,
                                ty,
                                generics.as_deref_mut(),
                                generic_handler,
                                handler_output,
                            )
                        })
                        .collect(),
                    None => Vec::new(),
                };
                let fail = self.analyze_fail(
                    scope,
                    fail,
                    generics.as_deref_mut(),
                    generic_handler,
                    handler_output,
                );
                let effect = match self.analyze_effect(scope, &id.ident) {
                    Some(effect) => effect,
                    None => return TYPE_UNKNOWN,
                };

                // create handler type
                let handler_ty = self.insert_type(
                    Type::DataType(TypeConstraints::Handler(
                        effect.map(|&effect| EffectIdent {
                            effect,
                            // TODO: error on length mismatch
                            generic_params: self.ir.effects[effect]
                                .generics
                                .iter()
                                .map(|g| g.idx)
                                .zip(params)
                                .collect(),
                        }),
                        fail,
                    )),
                    false,
                    false,
                );
                match generics.as_deref_mut().filter(|_| generic_handler) {
                    Some(generics) => {
                        let len = self.ir.generic_names.len() + self.ir.assoc_names.len();
                        let idx = self.ir.generic_names.push(GenericIdx, format!("`_{}", len));

                        let value = Generic {
                            idx,
                            typeof_ty: handler_ty,
                        };
                        generics.push(value);
                        self.insert_type(Type::Generic(value), false, false)
                    }
                    None => {
                        handler_output(self, generics.unwrap_or(&mut Vec::new()), handler_ty, ty)
                    }
                }
            }
            T::Generic(id) => match self.analyze_generic(scope, id, TYPE_DATATYPE, generics) {
                Some(generic) => self.insert_type(Type::Generic(generic), false, false),
                None => TYPE_UNKNOWN,
            },
            T::GenericHandler(id, fail) => {
                let fail = self.analyze_fail(
                    scope,
                    fail,
                    generics.as_deref_mut(),
                    generic_handler,
                    handler_output,
                );

                let effect =
                    match self.analyze_generic(scope, id, TYPE_EFFECT, generics.as_deref_mut()) {
                        Some(generic) => GenericVal::Generic(generic.idx),
                        None => return TYPE_UNKNOWN,
                    };

                // create handler type
                let handler_ty = self.insert_type(
                    Type::DataType(TypeConstraints::Handler(effect, fail)),
                    false,
                    false,
                );
                match generics.as_deref_mut().filter(|_| generic_handler) {
                    Some(generics) => {
                        let len = self.ir.generic_names.len() + self.ir.assoc_names.len();
                        let idx = self.ir.generic_names.push(GenericIdx, format!("`_{}", len));

                        let value = Generic {
                            idx,
                            typeof_ty: handler_ty,
                        };
                        generics.push(value);
                        self.insert_type(Type::Generic(value), false, false)
                    }
                    None => {
                        handler_output(self, generics.unwrap_or(&mut Vec::new()), handler_ty, ty)
                    }
                }
            }
            T::Pointer(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Pointer(inner), false, true)
            }
            T::Const(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                inner.with(true, inner.is_lent())
            }
            T::ConstArray(size, ty) => {
                let inner = self.analyze_type(
                    scope,
                    ty,
                    generics.as_deref_mut(),
                    generic_handler,
                    handler_output,
                );
                let size = match self.ast.exprs[size].0 {
                    Expression::Int(i) => GenericVal::Literal(i),
                    Expression::Ident(id) => {
                        match self.analyze_generic(scope, id, TYPE_USIZE, generics) {
                            Some(generic) => GenericVal::Generic(generic.idx),
                            None => return TYPE_UNKNOWN,
                        }
                    }
                    _ => todo!(),
                };
                self.insert_type(Type::ConstArray(size, inner), false, false)
            }
            T::Slice(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Slice(inner), false, true)
            }
            T::ConstExpr(_) => todo!(),
        }
    }
    fn analyze_effect(
        &mut self,
        scope: &mut ScopeStack,
        effect: &ast::PackagedIdent,
    ) -> Option<GenericVal<EffIdx>> {
        match effect.package {
            Some(id) => scope.try_package_effect(self, id, effect.ident),
            None => scope.try_effect(self, effect.ident),
        }
    }
    fn analyze_sign(
        &mut self,
        scope: &mut ScopeStack,
        name: Ident,
        effect: Option<EffIdx>,
        fun: &ast::FunSign,
        mut assocs: Option<&mut Vec<AssocDef>>,
    ) -> FunSign {
        scope.child(|scope| {
            let name = &self.ast.idents[name];
            let mut generics = Generics::new();
            let mut params = VecMap::new();
            let mut handler_params = Vec::new();

            // base params
            for param in fun.inputs.values() {
                let ty = self.analyze_type(
                    scope,
                    param.ty,
                    Some(&mut generics),
                    true,
                    &mut Self::no_handler,
                );
                if param.const_generic {
                    let ty = match self.analyze_generic(scope, param.name, ty, Some(&mut generics))
                    {
                        Some(generic) => self.insert_type(Type::Generic(generic), false, false),
                        None => TYPE_UNKNOWN,
                    };
                    params.push_value(Param {
                        name_def: self.ast.idents[param.name].empty(),
                        name: self.ast.idents[param.name].0.clone(),
                        type_def: self.ast.types[param.ty].empty(),
                        ty,
                        mutable: param.mutable,
                    });
                } else {
                    params.push_value(Param {
                        name_def: self.ast.idents[param.name].empty(),
                        name: self.ast.idents[param.name].0.clone(),
                        type_def: self.ast.types[param.ty].empty(),
                        ty,
                        mutable: param.mutable,
                    });
                }
            }

            // bound handlers
            for id in fun.effects.iter() {
                let effect_params = match id.params {
                    Some(ref params) => params
                        .iter()
                        .copied()
                        .map(|ty| {
                            self.analyze_type(
                                scope,
                                ty,
                                Some(&mut generics),
                                true,
                                &mut Self::no_handler,
                            )
                        })
                        .collect(),
                    None => Vec::new(),
                };
                match self.analyze_effect(scope, &id.ident) {
                    Some(effect) => {
                        let handler_ty = self.insert_type(
                            Type::DataType(TypeConstraints::BoundHandler(effect.map(|&effect| {
                                EffectIdent {
                                    effect,
                                    // TODO: error on length mismatch
                                    generic_params: self.ir.effects[effect]
                                        .generics
                                        .iter()
                                        .map(|generic| generic.idx)
                                        .zip(effect_params)
                                        .collect(),
                                }
                            }))),
                            false,
                            false,
                        );

                        let len = self.ir.generic_names.len() + self.ir.assoc_names.len();
                        let idx = self.ir.generic_names.push(GenericIdx, format!("`_{}", len));

                        let value = Generic {
                            idx,
                            typeof_ty: handler_ty,
                        };
                        generics.push(value);
                        let ty = self.insert_type(Type::Generic(value), false, false);

                        handler_params.push(Param {
                            name_def: self.ast.idents[id.ident.ident].empty(),
                            name: self.ast.idents[id.ident.ident].0.clone(),
                            type_def: self.ast.idents[id.ident.ident].empty(),
                            ty,
                            mutable: false,
                        });
                    }
                    None => {}
                }
            }

            // parent handler
            if let Some(effect) = effect {
                handler_params.push(Param {
                    name_def: self.ast.idents[self.ast.effects[effect].name].empty(),
                    name: self.ast.idents[self.ast.effects[effect].name].0.clone(),
                    type_def: self.ast.idents[self.ast.effects[effect].name].empty(),
                    ty: TYPE_SELF,
                    mutable: false,
                });
            }

            // return type
            let return_type = match fun.output {
                Some(ty) => self.analyze_type(
                    scope,
                    ty,
                    Some(&mut generics),
                    false,
                    &mut |ctx, generics, ty, _| match &mut assocs {
                        Some(assocs) => {
                            let effect = effect.unwrap();
                            let idx = ctx.ir.assoc_names.push(
                                AssocIdx,
                                format!(
                                    "_{}",
                                    ctx.ir.generic_names.len() + ctx.ir.assoc_names.len()
                                ),
                            );
                            let assoc = Assoc { idx, typeof_ty: ty };
                            assocs.push(AssocDef {
                                assoc,
                                infer: true,
                                generics: generics.clone(),
                            });
                            let generic_params = generics
                                .iter()
                                .copied()
                                .map(|generic| {
                                    (
                                        generic.idx,
                                        ctx.insert_type(Type::Generic(generic), false, false),
                                    )
                                })
                                .collect();
                            ctx.insert_type(
                                Type::AssocType {
                                    assoc,
                                    handler: TYPE_SELF,
                                    effect,
                                    generic_params,
                                },
                                false,
                                false,
                            )
                        }
                        None => {
                            let idx = ctx.ir.lazy_handlers.push(LazyIdx, None);
                            ctx.insert_type(Type::LazyHandler(ty, idx), false, false)
                        }
                    },
                ),
                None => TYPE_NONE,
            };

            FunSign {
                def: Some(name.empty()),
                name: name.0.clone(),
                generics,
                params,
                effect_params: handler_params,
                return_type: ReturnType {
                    type_def: fun.output.map(|ty| self.ast.types[ty].empty()),
                    ty: return_type,
                },
            }
        })
    }
    fn check_sign(
        &mut self,
        a: &FunSign,
        b: FunIdent,
        generic_params: &GenericParams,
        parent_generics: usize,
        assoc_types: &Vec<(AssocIdx, TypeIdx)>,
    ) {
        let b = match b {
            FunIdent::Top(idx) => &self.ir.fun_sign[idx],
            FunIdent::Effect(eff, idx) => &self.ir.effects[eff].funs[idx],
        };

        let params = b.params.clone();

        if a.params.len() != b.params.len() {
            // TODO: get correct amount of parameters
            // this now also includes effect params and 'self'
            // which might be confusing
            self.errors
                .push(b.def.unwrap().with(Error::ParameterMismatch(
                    Some(a.def.unwrap()),
                    a.params.len(),
                    b.params.len(),
                )));
            return;
        }

        for (a, b) in a.params.values().zip(Vec::from(params).into_iter()) {
            let translated = self.translate_generics(
                b.ty,
                generic_params,
                parent_generics,
                TYPE_SELF,
                Some(assoc_types),
            );
            self.check_move(
                translated,
                a.ty,
                &mut TypeError {
                    loc: b.type_def,
                    def: Some(a.type_def),
                    layers: Vec::new(),
                },
            );
        }

        // NOTE: output already has been checked
    }
    fn analyze_implied(&mut self, scope: &mut ScopeStack, implied: &ast::Handler) {
        scope.child(|scope| {
            let mut generics = Generics::default();

            let (id, fail, functions) = match *implied {
                ast::Handler::Full {
                    ref effect,
                    fail_type,
                    ref functions,
                } => (effect, fail_type, functions),
                ast::Handler::Lambda(_) => unreachable!(),
            };

            // get signature
            let params = match id.params {
                Some(ref params) => params
                    .iter()
                    .copied()
                    .map(|ty| {
                        self.analyze_type(
                            scope,
                            ty,
                            Some(&mut generics),
                            true,
                            &mut Self::no_handler,
                        )
                    })
                    .collect(),
                None => Vec::new(),
            };
            let fail = self.analyze_fail(
                scope,
                fail,
                Some(&mut generics),
                true,
                &mut Self::no_handler,
            );
            let effect = self.analyze_effect(scope, &id.ident)?.literal().copied()?;

            let generics = generics;
            // TODO: error on length mismatch
            let generic_params = self.ir.effects[effect]
                .generics
                .iter()
                .map(|generic| generic.idx)
                .zip(params)
                .collect::<Vec<_>>();

            // check functions
            let mut funs: VecMap<EffFunIdx, (FunSign, FunImpl)> =
                std::iter::repeat_with(Default::default)
                    .take(self.ast.effects[effect].functions.len())
                    .collect();
            let assoc_typeof_types = self.ir.effects[effect]
                .assocs
                .iter()
                .map(|assoc| (assoc.assoc.idx, assoc.assoc.typeof_ty))
                .collect::<Vec<_>>();
            let assoc_typeof_types = assoc_typeof_types
                .into_iter()
                .map(|(idx, typeof_ty)| {
                    (
                        idx,
                        self.translate_generics(
                            typeof_ty,
                            &generic_params,
                            generics.len(),
                            TYPE_SELF,
                            None,
                        ),
                    )
                })
                .collect::<Vec<_>>();
            let mut assoc_types = assoc_typeof_types
                .iter()
                .map(|a| a.0)
                .zip(std::iter::repeat(TYPE_UNKNOWN))
                .collect::<Vec<_>>();
            for function in functions {
                // analyze signature
                let name = &self.ast.idents[function.decl.name];
                let matching = self.ast.effects[effect]
                    .functions
                    .iter(EffFunIdx)
                    .find(|(_, decl)| self.ast.idents[decl.name].0.eq(&name.0));

                let sign = self.analyze_sign(
                    scope,
                    function.decl.name,
                    Some(effect),
                    &function.decl.sign,
                    None,
                );

                // analyze function
                let imp = self.generate_function(
                    Either::Right(&sign),
                    function.body,
                    scope,
                    Some(fail),
                    None,
                );

                match matching {
                    Some((idx, _)) => {
                        // infer assoc types
                        // type mismatch is ignored as this will be checked later on as well
                        let parent_return = self.translate_generics(
                            self.ir.effects[effect].funs[idx].return_type.ty,
                            &generic_params,
                            generics.len(),
                            TYPE_SELF,
                            None,
                        );
                        self.check_and_infer(
                            |ctx, ty| match *ty {
                                Type::AssocType { handler, assoc, .. } => {
                                    if handler == TYPE_SELF
                                        && ctx.ir.effects[effect]
                                            .assocs
                                            .iter()
                                            .find(|a| a.assoc.idx == assoc.idx)
                                            .unwrap()
                                            .infer
                                    {
                                        Some(assoc.idx)
                                    } else {
                                        None
                                    }
                                }
                                _ => None,
                            },
                            &assoc_typeof_types,
                            &mut assoc_types,
                            parent_return,
                            sign.return_type.ty,
                            true,
                            &mut TypeError {
                                loc: function
                                    .decl
                                    .sign
                                    .output
                                    .map(|ty| self.ast.types[ty].empty())
                                    .unwrap_or(name.empty()),
                                def: Some(
                                    self.ast.effects[effect].functions[idx]
                                        .sign
                                        .output
                                        .map(|ty| self.ast.types[ty].empty())
                                        .unwrap_or(
                                            self.ast.idents
                                                [self.ast.effects[effect].functions[idx].name]
                                                .empty(),
                                        ),
                                ),
                                layers: Vec::new(),
                            },
                        );

                        // set function
                        funs[idx] = (sign, imp);
                    }
                    None => {
                        self.errors.push(name.with(Error::UnknownEffectFun(
                            Some(self.ast.idents[self.ast.effects[effect].name].empty()),
                            Some(self.ast.idents[id.ident.ident].empty()),
                        )));
                    }
                }
            }
            let assoc_types = assoc_types;

            // TODO: error on UNKNOWN assoc (non-infer)

            // check if signatures match
            let mut missing = Vec::new();
            for (idx, (sign, _)) in funs.iter(EffFunIdx) {
                let name = self.ast.idents[self.ast.effects[effect].functions[idx].name].empty();

                // check if missing
                if sign.def.is_none() {
                    missing.push(name);
                    continue;
                };

                // check sign mismatch
                self.check_sign(
                    &sign,
                    FunIdent::Effect(effect, idx),
                    &generic_params,
                    generics.len(),
                    &assoc_types,
                );
            }
            if !missing.is_empty() {
                self.errors.push(self.ast.idents[id.ident.ident].with(
                    Error::UnimplementedMethods(
                        self.ast.idents[self.ast.effects[effect].name].empty(),
                        missing,
                    ),
                ));
            }

            // add implied handler to effect
            let handler = self.push_handler(Handler {
                debug_name: format!("H{}", self.ir.handlers.len()),
                generics,

                effect,
                generic_params,
                fail,

                assoc_types,

                captures: Vec::new(),
                funs,
            });
            self.ir.effects[effect].implied.push(handler);

            Some(())
        });
    }
    fn check_and_infer<K: Copy + Into<usize> + PartialEq>(
        &mut self,
        convert: impl Fn(&Self, &Type) -> Option<K>,
        typeof_types: &Vec<(K, TypeIdx)>,
        types: &mut Vec<(K, TypeIdx)>,
        parent: TypeIdx,
        ty: TypeIdx,
        output: bool,
        error_loc: &mut TypeError,
    ) {
        self.matches(
            parent,
            ty,
            error_loc,
            &mut |ctx, a, b, error_loc| match convert(ctx, &ctx.ir.types[a]) {
                Some(idx) => {
                    let typeof_b = ctx.typeof_ty(b);
                    if output {
                        ctx.check_move_rev(
                            get_value(typeof_types, &idx).copied().unwrap(),
                            typeof_b,
                            error_loc,
                        );
                    } else {
                        ctx.check_move(
                            get_value(typeof_types, &idx).copied().unwrap(),
                            typeof_b,
                            error_loc,
                        );
                    }

                    let type_idx = get_value_mut(types, &idx).unwrap();
                    *type_idx = ctx.supertype(*type_idx, b, error_loc);
                    Some(*type_idx)
                }
                None => None,
            },
        );
    }
    fn supertype(&mut self, a: TypeIdx, b: TypeIdx, error_loc: &mut TypeError) -> TypeIdx {
        self.matches(a, b, error_loc, &mut |ctx, a, b, error_loc| {
            if a == b {
                return Some(a);
            }
            if a.is_const() != b.is_const() || a.is_lent() != b.is_lent() {
                let is_const = a.is_const() || b.is_const();
                let is_lent = a.is_lent() || b.is_lent();
                return Some(ctx.supertype(
                    a.with(is_const, is_lent),
                    b.with(is_const, is_lent),
                    error_loc,
                ));
            }
            match (&ctx.ir.types[a], &ctx.ir.types[b]) {
                (&Type::DataType(TypeConstraints::None), &Type::DataType(_)) => Some(TYPE_DATATYPE),
                (&Type::DataType(_), &Type::DataType(TypeConstraints::None)) => Some(TYPE_DATATYPE),

                (_, Type::Never) => Some(a),
                (_, Type::Unknown) => Some(a),
                (Type::Never, _) => Some(b),
                (Type::Unknown, _) => Some(b),

                _ => None,
            }
        })
    }
    fn check_move(&mut self, from: TypeIdx, to: TypeIdx, error_loc: &mut TypeError) {
        self.matches(from, to, error_loc, &mut |ctx, from, to, error_loc| {
            if from == to {
                return Some(from);
            }
            if (to.is_const() && !from.is_const()) || (to.is_lent() && !from.is_lent()) {
                let from = from.with(to.is_const(), to.is_lent());
                ctx.check_move(from, to, error_loc);
                return Some(from);
            }
            match (&ctx.ir.types[from], &ctx.ir.types[to]) {
                (&Type::DataType(_), &Type::DataType(TypeConstraints::None)) => Some(TYPE_DATATYPE),

                (
                    Type::DataType(TypeConstraints::BoundHandler(_)),
                    Type::DataType(TypeConstraints::Handler(eff_b, _)),
                ) => {
                    let to = ctx.insert_type(
                        Type::DataType(TypeConstraints::BoundHandler(eff_b.clone())),
                        to.is_const(),
                        to.is_lent(),
                    );
                    ctx.check_move(from, to, error_loc);
                    Some(from)
                }

                (_, Type::Unknown) => Some(from),
                (Type::Never, _) => Some(to),
                (Type::Unknown, _) => Some(to),

                _ => None,
            }
        });
    }
    fn check_move_rev(&mut self, to: TypeIdx, from: TypeIdx, error_loc: &mut TypeError) {
        self.matches(to, from, error_loc, &mut |ctx, to, from, error_loc| {
            if to == from {
                return Some(from);
            }
            if (to.is_const() && !from.is_const()) || (to.is_lent() && !from.is_lent()) {
                let from = from.with(to.is_const(), to.is_lent());
                ctx.check_move_rev(to, from, error_loc);
                return Some(from);
            }
            match (&ctx.ir.types[to], &ctx.ir.types[from]) {
                (&Type::DataType(TypeConstraints::None), &Type::DataType(_)) => Some(TYPE_DATATYPE),

                (
                    Type::DataType(TypeConstraints::Handler(eff_a, _)),
                    Type::DataType(TypeConstraints::BoundHandler(_)),
                ) => {
                    let to = ctx.insert_type(
                        Type::DataType(TypeConstraints::BoundHandler(eff_a.clone())),
                        to.is_const(),
                        to.is_lent(),
                    );
                    ctx.check_move_rev(to, from, error_loc);
                    Some(from)
                }

                (_, Type::Never) => Some(to),
                (_, Type::Unknown) => Some(to),
                (Type::Unknown, _) => Some(from),

                _ => None,
            }
        });
    }
    fn typeof_ty(&mut self, ty: TypeIdx) -> TypeIdx {
        match self.ir.types[ty] {
            Type::Handler { idx, bound, .. } => {
                let handler = &self.ir.handlers[idx];
                if bound {
                    self.insert_type(
                        Type::DataType(TypeConstraints::BoundHandler(GenericVal::Literal(
                            EffectIdent {
                                effect: handler.effect,
                                generic_params: handler.generic_params.clone(),
                            },
                        ))),
                        false,
                        false,
                    )
                } else {
                    self.insert_type(
                        Type::DataType(TypeConstraints::Handler(
                            GenericVal::Literal(EffectIdent {
                                effect: handler.effect,
                                generic_params: handler.generic_params.clone(),
                            }),
                            handler.fail,
                        )),
                        false,
                        false,
                    )
                }
            }

            Type::Generic(generic) => generic.typeof_ty,
            Type::LazyHandler(typeof_ty, _) => typeof_ty,
            Type::AssocType { assoc, .. } => assoc.typeof_ty,

            Type::HandlerSelf => TYPE_DATATYPE,
            Type::Pointer(_) => TYPE_DATATYPE,
            Type::ConstArray(_, _) => TYPE_DATATYPE,
            Type::Slice(_) => TYPE_DATATYPE,
            Type::Integer(_, _) => TYPE_DATATYPE,
            Type::Str => TYPE_DATATYPE,
            Type::Char => TYPE_DATATYPE,
            Type::Bool => TYPE_DATATYPE,
            Type::None => TYPE_DATATYPE,

            Type::Never => TYPE_NEVER,
            Type::Unknown => TYPE_UNKNOWN,

            Type::DataType(_) => todo!(),
            Type::Effect => todo!(),
        }
    }
    fn matches(
        &mut self,
        a: TypeIdx,
        b: TypeIdx,
        error_loc: &mut TypeError,
        compare: &mut impl FnMut(&mut Self, TypeIdx, TypeIdx, &mut TypeError) -> Option<TypeIdx>,
    ) -> TypeIdx {
        // NOTE: 'matches' is generic-agnositc,
        // so it doesn't think two generics with same indices are the same
        TypeError::child(error_loc, a, b, |error_loc| {
            compare(self, a, b, error_loc).unwrap_or_else(|| {
                if a.is_const() != b.is_const() || a.is_lent() != b.is_lent() {
                    TypeError::commit(error_loc, self);
                    return TYPE_UNKNOWN;
                }

                let is_const = a.is_const();
                let is_lent = a.is_lent();

                match (&self.ir.types[a], &self.ir.types[b]) {
                    (
                        &Type::DataType(TypeConstraints::Handler(ref eff_a, fail_a)),
                        &Type::DataType(TypeConstraints::Handler(ref eff_b, fail_b)),
                    ) => {
                        if let (GenericVal::Literal(a), GenericVal::Literal(b)) = (eff_a, eff_b) {
                            if a.effect == b.effect {
                                let effect = a.effect;
                                let generic_params = a
                                    .generic_params
                                    .iter()
                                    .map(|&(_, b)| b)
                                    .zip(b.generic_params.iter().map(|&(_, b)| b))
                                    .collect::<Vec<_>>();

                                let fail = self.matches(fail_a, fail_b, error_loc, compare);
                                let generic_params = generic_params
                                    .into_iter()
                                    .map(|(a, b)| self.matches(a, b, error_loc, compare))
                                    .collect::<Vec<_>>();
                                let generic_params = self.ir.effects[effect]
                                    .generics
                                    .iter()
                                    .map(|generic| generic.idx)
                                    .zip(generic_params)
                                    .collect();

                                self.insert_type(
                                    Type::DataType(TypeConstraints::Handler(
                                        GenericVal::Literal(EffectIdent {
                                            effect,
                                            generic_params,
                                        }),
                                        fail,
                                    )),
                                    is_const,
                                    is_lent,
                                )
                            } else {
                                TypeError::commit(error_loc, self);
                                TYPE_UNKNOWN
                            }
                        } else {
                            if eff_a == eff_b {
                                // TODO: compare effect
                                let eff = eff_a.clone();
                                let fail = self.matches(fail_a, fail_b, error_loc, compare);

                                self.insert_type(
                                    Type::DataType(TypeConstraints::Handler(eff, fail)),
                                    is_const,
                                    is_lent,
                                )
                            } else {
                                TypeError::commit(error_loc, self);
                                TYPE_UNKNOWN
                            }
                        }
                    }
                    (
                        &Type::DataType(TypeConstraints::BoundHandler(ref eff_a)),
                        &Type::DataType(TypeConstraints::BoundHandler(ref eff_b)),
                    ) => {
                        if let (GenericVal::Literal(a), GenericVal::Literal(b)) = (eff_a, eff_b) {
                            if a.effect == b.effect {
                                let effect = a.effect;
                                let generic_params = a
                                    .generic_params
                                    .iter()
                                    .map(|&(_, b)| b)
                                    .zip(b.generic_params.iter().map(|&(_, b)| b))
                                    .collect::<Vec<_>>();

                                let generic_params = generic_params
                                    .into_iter()
                                    .map(|(a, b)| self.matches(a, b, error_loc, compare))
                                    .collect::<Vec<_>>();
                                let generic_params = self.ir.effects[effect]
                                    .generics
                                    .iter()
                                    .map(|generic| generic.idx)
                                    .zip(generic_params)
                                    .collect();

                                self.insert_type(
                                    Type::DataType(TypeConstraints::BoundHandler(
                                        GenericVal::Literal(EffectIdent {
                                            effect,
                                            generic_params,
                                        }),
                                    )),
                                    is_const,
                                    is_lent,
                                )
                            } else {
                                TypeError::commit(error_loc, self);
                                TYPE_UNKNOWN
                            }
                        } else {
                            if eff_a == eff_b {
                                // TODO: compare effect
                                let eff = eff_a.clone();

                                self.insert_type(
                                    Type::DataType(TypeConstraints::BoundHandler(eff)),
                                    is_const,
                                    is_lent,
                                )
                            } else {
                                TypeError::commit(error_loc, self);
                                TYPE_UNKNOWN
                            }
                        }
                    }

                    (
                        &Type::AssocType {
                            assoc:
                                Assoc {
                                    idx: idx_a,
                                    typeof_ty: ty_a,
                                },
                            handler: handler_a,
                            effect: eff_a,
                            generic_params: ref generic_a,
                        },
                        &Type::AssocType {
                            assoc:
                                Assoc {
                                    idx: idx_b,
                                    typeof_ty: ty_b,
                                },
                            handler: handler_b,
                            effect: eff_b,
                            generic_params: ref generic_b,
                        },
                    ) if eff_a == eff_b && idx_a == idx_b => {
                        let generic_params = generic_a
                            .iter()
                            .map(|&(_, b)| b)
                            .zip(generic_b.iter().map(|&(_, b)| b))
                            .collect::<Vec<_>>();

                        let ty = self.matches(ty_a, ty_b, error_loc, compare);
                        let handler = self.matches(handler_a, handler_b, error_loc, compare);
                        let generic_params = generic_params
                            .into_iter()
                            .map(|(a, b)| self.matches(a, b, error_loc, compare))
                            .collect::<Vec<_>>();
                        let generic_params = self.ir.effects[eff_a]
                            .generics
                            .iter()
                            .map(|generic| generic.idx)
                            .zip(generic_params)
                            .collect();

                        self.insert_type(
                            Type::AssocType {
                                assoc: Assoc {
                                    idx: idx_a,
                                    typeof_ty: ty,
                                },
                                handler,
                                effect: eff_a,
                                generic_params,
                            },
                            is_const,
                            is_lent,
                        )
                    }

                    (
                        &Type::Handler {
                            idx: idx_a,
                            generic_params: ref generic_a,
                            bound: bound_a,
                        },
                        &Type::Handler {
                            idx: idx_b,
                            generic_params: ref generic_b,
                            bound: bound_b,
                        },
                    ) if idx_a == idx_b && bound_a == bound_b => {
                        let generic_params = generic_a
                            .iter()
                            .map(|&(_, b)| b)
                            .zip(generic_b.iter().map(|&(_, b)| b))
                            .collect::<Vec<_>>();
                        let generic_params = generic_params
                            .into_iter()
                            .map(|(a, b)| self.matches(a, b, error_loc, compare))
                            .collect::<Vec<_>>();
                        let generic_params = self.ir.effects[self.ir.handlers[idx_a].effect]
                            .generics
                            .iter()
                            .map(|generic| generic.idx)
                            .zip(generic_params)
                            .collect();

                        self.insert_type(
                            Type::Handler {
                                idx: idx_a,
                                generic_params,
                                bound: bound_a,
                            },
                            is_const,
                            is_lent,
                        )
                    }

                    (&Type::Pointer(a), &Type::Pointer(b)) => {
                        let inner = self.matches(a, b, error_loc, compare);
                        self.insert_type(Type::Pointer(inner), is_const, is_lent)
                    }
                    (&Type::Slice(a), &Type::Slice(b)) => {
                        let inner = self.matches(a, b, error_loc, compare);
                        self.insert_type(Type::Slice(inner), is_const, is_lent)
                    }
                    (&Type::ConstArray(size_a, a), &Type::ConstArray(size_b, b))
                        if size_a == size_b =>
                    {
                        // TODO: compare size
                        let inner = self.matches(a, b, error_loc, compare);
                        self.insert_type(Type::ConstArray(size_a, inner), is_const, is_lent)
                    }

                    (Type::Integer(sa, ia), Type::Integer(sb, ib)) if sa == sb && ia == ib => a,

                    (Type::Unknown, Type::Unknown)
                    | (Type::Effect, Type::Effect)
                    | (
                        Type::DataType(TypeConstraints::None),
                        Type::DataType(TypeConstraints::None),
                    )
                    | (Type::Str, Type::Str)
                    | (Type::Bool, Type::Bool)
                    | (Type::None, Type::None)
                    | (Type::Never, Type::Never) => a,

                    (&Type::LazyHandler(_, idx), &Type::LazyHandler(_, idx2)) if idx == idx2 => a,

                    _ => {
                        TypeError::commit(error_loc, self);
                        TYPE_UNKNOWN
                    }
                }
            })
        })
    }
    fn generate_function(
        &mut self,
        sign: Either<FunIdx, &FunSign>,
        body: ExprIdx,
        scope: &mut ScopeStack,
        yeetable: Option<TypeIdx>,
        yeetable_def: Option<Range>,
    ) -> FunImpl {
        scope.child(|scope| {
            let ir_sign = match sign {
                Either::Left(idx) => &self.ir.fun_sign[idx],
                Either::Right(sign) => sign,
            };
            let handler_stack = ir_sign
                .effect_params
                .iter()
                .map(|param| param.ty)
                .collect::<Vec<_>>();

            for (idx, param) in ir_sign.params.iter(ParamIdx) {
                scope.top().values.insert(
                    param.name.clone(),
                    Variable {
                        value: Value::Param(idx),
                        ty: param.ty,
                        mutable: param.mutable,
                    },
                );
            }
            for generic in ir_sign.generics.iter() {
                scope
                    .top()
                    .generics
                    .insert(self.ir.generic_names[generic.idx].clone(), generic.clone());
            }

            let mut blocks = VecMap::new();
            let block = blocks.push(BlockIdx, Block::default());
            let mut fun_ctx = FunCtx {
                handler_stack,
                internal_handler_stack: Vec::new(),
                phis: PhiStack::default(),
                scope,
                sign,
                blocks,
                block,
                yeetable,
                yeetable_def,
            };

            let out = self.check_expr(
                &mut fun_ctx,
                body,
                ir_sign.return_type.ty,
                ir_sign.return_type.type_def,
            );

            match out {
                Some(val) => fun_ctx.blocks[fun_ctx.block]
                    .instructions
                    .push_value(Instruction::Return(val)),
                None => fun_ctx.blocks[fun_ctx.block]
                    .instructions
                    .push_value(Instruction::Unreachable),
            }

            FunImpl {
                blocks: fun_ctx.blocks,
            }
        })
    }
    fn check_expr(
        &mut self,
        ctx: &mut FunCtx,
        expr: ExprIdx,
        expected: TypeIdx,
        expected_def: Option<Range>,
    ) -> Option<Value> {
        let error_loc = &mut TypeError {
            loc: self.ast.exprs[expr].empty(),
            def: expected_def,
            layers: Vec::new(),
        };

        use Expression as E;
        match (&self.ast.exprs[expr].0, &self.ir.types[expected]) {
            (&E::Body(ref body), _) => ctx.child(|ctx| {
                for expr in body.main.iter().copied() {
                    self.synth_expr(ctx, expr)?;
                }
                body.last
                    .map(|expr| self.check_expr(ctx, expr, expected, expected_def))
                    .unwrap_or_else(|| {
                        self.check_move(TYPE_NONE, expected, error_loc);
                        Some(Value::ConstantNone)
                    })
            }),
            (&E::IfElse(cond, yes, no), _) => {
                let cond = self.check_expr(ctx, cond, TYPE_BOOL, None)?;
                let (yes_block, no_block) = ctx.branch(cond);

                let mut phis = HashMap::new();

                ctx.block = yes_block;
                let yes_val = ctx.phi(false, &mut phis, |ctx| {
                    self.check_expr(ctx, yes, expected, expected_def)
                });
                let yes_end = ctx.block;

                ctx.block = no_block;
                let no_val = match no {
                    Some(no) => ctx.phi(false, &mut phis, |ctx| {
                        self.check_expr(ctx, no, expected, expected_def)
                    }),
                    None => {
                        self.check_move(TYPE_NONE, expected, error_loc);
                        Some(Value::ConstantNone)
                    }
                };
                let no_end = ctx.block;

                ctx.complete_phi(&[yes_end, no_end], phis);
                match (yes_val, no_val) {
                    (Some(yes_val), Some(no_val)) => {
                        let instr = ctx.blocks[ctx.block].instructions.push(
                            InstrIdx,
                            Instruction::Phi(vec![(yes_val, yes_end), (no_val, no_end)]),
                        );
                        Some(Value::Reg(ctx.block, instr))
                    }
                    (Some(v), None) => Some(v),
                    (None, Some(v)) => Some(v),
                    (None, None) => None,
                }
            }
            (&E::Array(ref exprs), &Type::Slice(elem)) => {
                let elems = exprs
                    .iter()
                    .copied()
                    .map(|expr| self.check_expr(ctx, expr, elem, expected_def))
                    .collect::<Option<Vec<_>>>()?;
                let len = elems.len() as u64;

                let arr = Value::ConstantAggregate(elems);
                let ptr = ctx.push(Instruction::Reference(arr));
                let slice = Value::ConstantAggregate(vec![ptr, Value::ConstantInt(false, len)]);
                Some(slice)
            }
            (&E::Array(ref exprs), &Type::ConstArray(GenericVal::Literal(n), elem))
                if n == exprs.len() as u64 =>
            {
                let elems = exprs
                    .iter()
                    .copied()
                    .map(|expr| self.check_expr(ctx, expr, elem, expected_def))
                    .collect::<Option<Vec<_>>>()?;
                Some(Value::ConstantAggregate(elems))
            }
            (&E::Uninit, _) => {
                // TODO: test if allowed
                Some(Value::ConstantUninit)
            }
            (&E::Int(0), _) => {
                // TODO: test if allowed
                Some(Value::ConstantZero)
            }
            (&E::Int(n), &Type::Integer(_signed, _size)) => {
                // TODO: test if fits
                Some(Value::ConstantInt(false, n))
            }
            (&E::Character(ref str), &Type::Integer(_signed, _size)) => {
                // TODO: test if fits, test if single char
                let c = str.chars().next().unwrap();
                let c = u64::from(c);
                Some(Value::ConstantInt(false, c))
            }
            (&E::String(ref str), &Type::Slice(elem)) if elem == TYPE_U8 => {
                Some(Value::ConstantString(str.clone()))
            }
            (&E::UnOp(inner, UnOp::Cast), _) => {
                // TODO: test if allowed
                let (value, ty) = self.synth_expr(ctx, inner)?;
                let instr = ctx.blocks[ctx.block]
                    .instructions
                    .push(InstrIdx, Instruction::Cast(value, expected));
                Some(Value::Reg(ctx.block, instr))
            }
            _ => {
                let (found, found_ty) = self.synth_expr(ctx, expr)?;
                self.check_move(found_ty, expected, error_loc);
                Some(found)
            }
        }
    }
    fn assignable_expr(
        &mut self,
        ctx: &mut FunCtx,
        expr: ExprIdx,
    ) -> Option<Either<(String, Variable), (Value, TypeIdx)>> {
        // TODO: return Value::Reference on Right

        use Expression as E;
        match self.ast.exprs[expr].0 {
            E::BinOp(left, BinOp::Index, right) => {
                let right = self.check_expr(ctx, right, TYPE_USIZE, None)?;
                match self.assignable_expr(ctx, left)? {
                    Either::Left((name, var)) => {
                        let (ptr, elem_ty) = match self.ir.types[var.ty] {
                            Type::ConstArray(_, inner) => {
                                let instr = ctx.blocks[ctx.block]
                                    .instructions
                                    .push(InstrIdx, Instruction::Reference(var.value));
                                ctx.modify(
                                    name,
                                    Variable {
                                        value: Value::Reference(ctx.block, instr),
                                        ..var
                                    },
                                );
                                (Value::Reg(ctx.block, instr), inner)
                            }
                            Type::Slice(inner) => {
                                let ptr = ctx.push(Instruction::Member(var.value, 0));
                                (ptr, inner)
                            }
                            Type::Unknown => {
                                return Some(Either::Right((Value::ConstantUnknown, TYPE_UNKNOWN)));
                            }
                            _ => todo!("give error"),
                        };

                        let elem = ctx.push(Instruction::AdjacentPtr(ptr, right));
                        Some(Either::Right((elem, elem_ty)))
                    }
                    Either::Right((value, ty)) => {
                        let inner = match self.ir.types[ty] {
                            Type::Pointer(inner) => inner,
                            Type::Unknown => {
                                return Some(Either::Right((Value::ConstantUnknown, TYPE_UNKNOWN)));
                            }
                            _ => unreachable!(),
                        };

                        let (ptr, elem_ty) = match self.ir.types[inner] {
                            Type::ConstArray(_, inner) => (value, inner),
                            Type::Slice(inner) => {
                                let slice = ctx.push(Instruction::Load(value));
                                let ptr = ctx.push(Instruction::Member(slice, 0));
                                (ptr, inner)
                            }
                            Type::Unknown => {
                                return Some(Either::Right((Value::ConstantUnknown, TYPE_UNKNOWN)));
                            }
                            _ => todo!("give error"),
                        };

                        let elem = ctx.push(Instruction::AdjacentPtr(ptr, right));
                        Some(Either::Right((elem, elem_ty)))
                    }
                }
            }
            E::Ident(id) => {
                let name = &self.ast.idents[id].0;
                match ctx.get_value(self, name) {
                    Some(var) => {
                        if let Value::Reference(block, instr) = var.value {
                            // variable is already a reference
                            let ptr_ty = self.insert_type(Type::Pointer(var.ty), false, true);
                            Some(Either::Right((Value::Reg(block, instr), ptr_ty)))
                        } else {
                            // return variable
                            Some(Either::Left((name.clone(), var)))
                        }
                    }
                    None => {
                        self.errors
                            .push(self.ast.idents[id].with(Error::UnknownValue));
                        Some(Either::Right((Value::ConstantUnknown, TYPE_UNKNOWN)))
                    }
                }
            }
            E::Error => Some(Either::Right((Value::ConstantUnknown, TYPE_UNKNOWN))),
            _ => todo!("give error"),
        }
    }
    fn synth_expr(&mut self, ctx: &mut FunCtx, expr: ExprIdx) -> Option<(Value, TypeIdx)> {
        use Expression as E;
        match self.ast.exprs[expr].0 {
            E::Body(ref body) => ctx.child(|ctx| {
                for expr in body.main.iter().copied() {
                    self.synth_expr(ctx, expr)?;
                }
                body.last
                    .map(|expr| self.synth_expr(ctx, expr))
                    .unwrap_or(Some((Value::ConstantNone, TYPE_NONE)))
            }),
            E::Loop(inner) => {
                ctx.phi(true, &mut HashMap::new(), |ctx| self.synth_expr(ctx, inner));
                None
            }
            E::IfElse(cond, yes, no) => {
                let cond = self.check_expr(ctx, cond, TYPE_BOOL, None)?;
                let (yes_block, no_block) = ctx.branch(cond);

                let mut phis = HashMap::new();

                ctx.block = yes_block;
                let yes_val = ctx.phi(false, &mut phis, |ctx| self.synth_expr(ctx, yes));
                let yes_end = ctx.block;

                ctx.block = no_block;
                let no_val = match no {
                    Some(no) => ctx.phi(false, &mut phis, |ctx| self.synth_expr(ctx, no)),
                    None => Some((Value::ConstantNone, TYPE_NONE)),
                };
                let no_end = ctx.block;

                ctx.complete_phi(&[yes_end, no_end], phis);
                match (yes_val, no_val) {
                    (Some(yes_val), Some(no_val)) => {
                        let common = self.supertype(
                            yes_val.1,
                            no_val.1,
                            &mut TypeError {
                                loc: self.ast.exprs[no.unwrap_or(yes)].empty(),
                                def: match no {
                                    Some(_) => Some(self.ast.exprs[yes].empty()),
                                    None => None,
                                },
                                layers: Vec::new(),
                            },
                        );
                        let instr = ctx.blocks[ctx.block].instructions.push(
                            InstrIdx,
                            Instruction::Phi(vec![(yes_val.0, yes_end), (no_val.0, no_end)]),
                        );
                        Some((Value::Reg(ctx.block, instr), common))
                    }
                    (Some(v), None) => Some(v),
                    (None, Some(v)) => Some(v),
                    (None, None) => None,
                }
            }

            E::TryWith(_, _) => {
                ctx.push(Instruction::Trap);
                Some((Value::ConstantUnknown, TYPE_UNKNOWN))
            }
            E::Handler(_) => {
                ctx.push(Instruction::Trap);
                Some((Value::ConstantUnknown, TYPE_UNKNOWN))
            }
            E::Call(_, _) => {
                ctx.push(Instruction::Trap);
                Some((Value::ConstantUnknown, TYPE_UNKNOWN))
            }

            E::BinOp(left, BinOp::Assign, right) => {
                match self.assignable_expr(ctx, left)? {
                    Either::Left((name, var)) => {
                        let right = self.check_expr(ctx, right, var.ty, None)?;
                        ctx.modify(
                            name,
                            Variable {
                                value: right,
                                ..var
                            },
                        );
                    }
                    Either::Right((value, ty)) => {
                        let inner = match self.ir.types[ty] {
                            Type::Pointer(inner) => inner,
                            Type::Unknown => {
                                return Some((Value::ConstantNone, TYPE_NONE));
                            }
                            _ => unreachable!(),
                        };
                        let right = self.check_expr(ctx, right, inner, None)?;
                        ctx.push(Instruction::Store(value, right));
                    }
                }
                Some((Value::ConstantNone, TYPE_NONE))
            }
            E::BinOp(left, BinOp::Index, right) => {
                let (left, left_ty) = self.synth_expr(ctx, left)?;
                let (ptr, elem_ty) = match self.ir.types[left_ty] {
                    Type::Slice(elem) => {
                        let ptr = ctx.push(Instruction::Member(left, 0));
                        (ptr, elem)
                    }
                    Type::ConstArray(_, elem) => {
                        let ptr = ctx.push(Instruction::Reference(left));
                        (ptr, elem)
                    }
                    Type::Unknown => {
                        return Some((Value::ConstantUnknown, TYPE_UNKNOWN));
                    }
                    _ => todo!("give error"),
                };
                // TODO: allow range
                let right = self.check_expr(ctx, right, TYPE_USIZE, None)?;
                let elem = ctx.push(Instruction::AdjacentPtr(ptr, right));
                Some((elem, elem_ty))
            }
            E::BinOp(left, op, right) => {
                let (left, left_ty) = self.synth_expr(ctx, left)?;
                let (right, right_ty) = self.synth_expr(ctx, right)?;
                // TODO: check if same ints

                let out = match op {
                    BinOp::Index => unreachable!(),
                    BinOp::Assign => unreachable!(),
                    BinOp::Range => unreachable!(),
                    BinOp::Equals => TYPE_BOOL,
                    BinOp::Less => TYPE_BOOL,
                    BinOp::Greater => TYPE_BOOL,
                    BinOp::Divide => left_ty,
                    BinOp::Multiply => left_ty,
                    BinOp::Subtract => left_ty,
                    BinOp::Add => left_ty,
                };

                let res = ctx.push(match op {
                    BinOp::Index => unreachable!(),
                    BinOp::Assign => unreachable!(),
                    BinOp::Range => unreachable!(),
                    BinOp::Equals => Instruction::Equals(left, right),
                    BinOp::Less => Instruction::Less(left, right),
                    BinOp::Greater => Instruction::Greater(left, right),
                    BinOp::Divide => Instruction::Div(left, right),
                    BinOp::Multiply => Instruction::Mul(left, right),
                    BinOp::Subtract => Instruction::Sub(left, right),
                    BinOp::Add => Instruction::Add(left, right),
                });

                Some((res, out))
            }
            E::UnOp(inner, UnOp::PostIncrement) => match self.assignable_expr(ctx, inner)? {
                Either::Left((name, var)) => {
                    let incremented = ctx.push(Instruction::Add(
                        var.value.clone(),
                        Value::ConstantInt(false, 1),
                    ));
                    ctx.modify(
                        name,
                        Variable {
                            value: incremented,
                            ..var.clone()
                        },
                    );
                    Some((var.value, var.ty))
                }
                Either::Right((value, ty)) => {
                    // TODO: check if integer type
                    let inner = match self.ir.types[ty] {
                        Type::Pointer(inner) => inner,
                        Type::Unknown => {
                            return Some((Value::ConstantUnknown, TYPE_UNKNOWN));
                        }
                        _ => unreachable!(),
                    };

                    let loaded = ctx.push(Instruction::Load(value.clone()));
                    let incremented = ctx.push(Instruction::Add(
                        loaded.clone(),
                        Value::ConstantInt(false, 1),
                    ));
                    ctx.push(Instruction::Store(value, incremented));

                    Some((loaded, inner))
                }
            },
            E::UnOp(inner, UnOp::Reference) => match self.assignable_expr(ctx, inner)? {
                Either::Left((name, var)) => {
                    let instr = ctx.blocks[ctx.block]
                        .instructions
                        .push(InstrIdx, Instruction::Reference(var.value));
                    ctx.modify(
                        name,
                        Variable {
                            value: Value::Reference(ctx.block, instr),
                            ..var
                        },
                    );

                    let ptr_ty = self.insert_type(Type::Pointer(var.ty), false, true);
                    Some((Value::Reg(ctx.block, instr), ptr_ty))
                }
                Either::Right((value, ty)) => Some((value, ty)),
            },
            E::UnOp(_, UnOp::Cast) => {
                self.errors
                    .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                Some((Value::ConstantUninit, TYPE_UNKNOWN))
            }
            E::Yeet(inner) => {
                match ctx.yeetable {
                    Some(yeet_ty) => {
                        let value = match inner {
                            Some(inner) => {
                                self.check_expr(ctx, inner, yeet_ty, ctx.yeetable_def)?
                            }
                            None => {
                                self.check_move(
                                    TYPE_NONE,
                                    yeet_ty,
                                    &mut TypeError {
                                        loc: self.ast.exprs[expr].empty(),
                                        def: ctx.yeetable_def,
                                        layers: Vec::new(),
                                    },
                                );
                                Value::ConstantNone
                            }
                        };
                        ctx.blocks[ctx.block]
                            .instructions
                            .push_value(Instruction::Yeet(value));
                    }
                    None => {
                        // TODO: error
                    }
                }
                None
            }
            E::Let(mutable, id, ty, expr) => {
                let (value, ty) = match ty {
                    Some(ty) => {
                        let def = self.ast.types[ty].empty();
                        let ty =
                            self.analyze_type(ctx.scope, ty, None, false, &mut Self::lazy_handler);
                        (self.check_expr(ctx, expr, ty, Some(def))?, ty)
                    }
                    None => self.synth_expr(ctx, expr)?,
                };
                let name = self.ast.idents[id].0.clone();
                ctx.define(name, Variable { value, ty, mutable });
                Some((Value::ConstantNone, TYPE_NONE))
            }
            E::Array(ref exprs) => {
                let mut iter = exprs.iter().copied();
                match iter.next() {
                    Some(first) => {
                        let (val, ty) = self.synth_expr(ctx, first)?;
                        let elems = std::iter::once(Some(val))
                            .chain(iter.map(|expr| self.check_expr(ctx, expr, ty, None)))
                            .collect::<Option<Vec<_>>>()?;
                        let arr_ty = self.insert_type(
                            Type::ConstArray(GenericVal::Literal(elems.len() as u64), ty),
                            false,
                            false,
                        );
                        Some((Value::ConstantAggregate(elems), arr_ty))
                    }
                    None => {
                        self.errors
                            .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                        Some((Value::ConstantUninit, TYPE_UNKNOWN))
                    }
                }
            }
            E::String(ref str) => Some((Value::ConstantString(str.clone()), TYPE_STR)),
            E::Character(ref str) => {
                // TODO: test if fits, test if single char (otherwise test if rune)
                let c = str.chars().next().unwrap();
                let c = u64::from(c);
                Some((Value::ConstantInt(false, c), TYPE_CHAR))
            }
            E::Ident(id) => {
                let name = &self.ast.idents[id].0;
                match ctx.get_value(self, name) {
                    Some(var) => Some((var.value, var.ty)),
                    None => {
                        self.errors
                            .push(self.ast.idents[id].with(Error::UnknownValue));
                        Some((Value::ConstantUnknown, TYPE_UNKNOWN))
                    }
                }
            }
            E::Int(n) => Some((Value::ConstantInt(false, n), TYPE_INT)),
            E::Uninit => {
                self.errors
                    .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                Some((Value::ConstantUninit, TYPE_UNKNOWN))
            }
            E::Error => Some((Value::ConstantUnknown, TYPE_UNKNOWN)),
            E::Member(_, _) => todo!(),
        }
    }
}

struct FunCtx<'a> {
    sign: Either<FunIdx, &'a FunSign>,
    handler_stack: Vec<TypeIdx>,
    internal_handler_stack: Vec<(TypeIdx, usize, BlockIdx)>,

    phis: PhiStack,
    scope: &'a mut ScopeStack,

    yeetable: Option<TypeIdx>,
    yeetable_def: Option<Range>,

    blocks: VecMap<BlockIdx, Block>,
    block: BlockIdx,
}

impl FunCtx<'_> {
    fn child<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push();
        let t = f(self);
        self.scope.pop();
        t
    }
    fn phi<T>(
        &mut self,
        loops: bool,
        phis: &mut HashMap<String, Vec<(Value, BlockIdx)>>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.push_phi(loops);
        self.scope.push();
        let t = f(self);
        self.scope.pop();
        self.commit_phi(phis);
        self.pop_phi();
        t
    }
    fn push(&mut self, instr: Instruction) -> Value {
        let idx = self.blocks[self.block].instructions.push(InstrIdx, instr);
        Value::Reg(self.block, idx)
    }
    fn get_value(&mut self, ctx: &mut SemCtx, name: &str) -> Option<Variable> {
        let var = self.scope.search(ctx, |s| s.values.get(name).cloned())?;

        let header = self.phis.phis.last().and_then(|p| p.header.as_ref());
        match header {
            Some(header) => {
                let idx = self.blocks[header.init]
                    .instructions
                    .push(InstrIdx, Instruction::Phi(vec![(var.value, header.entry)]));
                Some(Variable {
                    value: Value::Reg(header.init, idx),
                    ..var
                })
            }
            None => Some(var),
        }
    }
    fn push_phi(&mut self, loops: bool) {
        let header = if loops {
            let entry = self.block;
            let init = self.blocks.push(BlockIdx, Block::default());
            self.blocks[entry]
                .instructions
                .push_value(Instruction::Jump(init));
            let first = self.blocks.push(BlockIdx, Block::default());

            self.block = first;
            Some(PhiHeader {
                entry,
                init,
                first,
                instructions: HashMap::new(),
            })
        } else {
            None
        };

        self.phis.phis.push(Phi {
            scope_pos: self.scope.scopes.len(),
            own_vars: HashSet::new(),
            modified_vars: HashMap::new(),
            header,
        })
    }
    fn branch(&mut self, v: Value) -> (BlockIdx, BlockIdx) {
        let yes = self.blocks.push(BlockIdx, Block::default());
        let no = self.blocks.push(BlockIdx, Block::default());
        self.blocks[self.block]
            .instructions
            .push_value(Instruction::Branch(v, yes, no));
        (yes, no)
    }
    fn commit_phi(&mut self, phis: &mut HashMap<String, Vec<(Value, BlockIdx)>>) {
        let prev = self.block;
        let phi = self.phis.phis.last().unwrap();
        if let Some(header) = &phi.header {
            for (name, &idx) in header.instructions.iter() {
                let phis = match self.blocks[header.init].instructions[idx] {
                    Instruction::Phi(ref mut v) => v,
                    _ => unreachable!(),
                };
                match phi.modified_vars.get(name).cloned() {
                    Some(value) => phis.push((value, prev)),
                    None => {
                        let base_val = phis[0].0.clone();
                        phis.push((base_val, prev));
                    }
                }
            }
        }
        for (name, value) in phi.modified_vars.iter() {
            match phis.get_mut(name) {
                Some(vec) => {
                    vec.push((value.clone(), prev));
                }
                None => {
                    phis.insert(name.clone(), vec![(value.clone(), prev)]);
                }
            }
        }
        for (name, vec) in phis.iter_mut() {
            if !phi.modified_vars.contains_key(name) {
                let base_var = self.scope.scopes[0..phi.scope_pos]
                    .iter()
                    .rev()
                    .map(|scope| scope.values.get(name))
                    .find(Option::is_some)
                    .flatten()
                    .expect("no base val");
                vec.push((base_var.value.clone(), prev));
            }
        }
    }
    fn pop_phi(&mut self) {
        let phi = self.phis.phis.pop().unwrap();
        if let Some(header) = phi.header {
            self.blocks[header.init]
                .instructions
                .push_value(Instruction::Jump(header.first));
        }
    }
    fn complete_phi(&mut self, from: &[BlockIdx], phis: HashMap<String, Vec<(Value, BlockIdx)>>) {
        let idx = self.blocks.push(BlockIdx, Block::default());
        for block in from.iter().copied() {
            self.blocks[block]
                .instructions
                .push_value(Instruction::Jump(idx));
        }

        for (name, mut phis) in phis {
            let base_var = self
                .scope
                .scopes
                .iter()
                .rev()
                .map(|scope| scope.values.get(&name))
                .find(Option::is_some)
                .flatten()
                .expect("no base val");
            for block in from.iter().copied() {
                if !phis.iter().any(|(_, idx)| idx.eq(&block)) {
                    phis.push((base_var.value.clone(), block));
                }
            }
            let instr = self.blocks[idx]
                .instructions
                .push(InstrIdx, Instruction::Phi(phis));
            self.modify(
                name,
                Variable {
                    value: Value::Reg(idx, instr),
                    ..base_var.clone()
                },
            );
        }

        self.block = idx;
    }
    fn modify(&mut self, s: String, v: Variable) {
        for phis in self.phis.phis.iter_mut().rev() {
            if phis.own_vars.contains(&s) {
                break;
            } else {
                phis.modified_vars.insert(s.clone(), v.value.clone());
            }
        }
        self.scope.top().values.insert(s, v);
    }
    fn define(&mut self, s: String, v: Variable) {
        if let Some(phi) = self.phis.phis.last_mut() {
            phi.own_vars.insert(s.clone());
        }
        self.scope.top().values.insert(s, v);
    }
}

#[derive(Default)]
struct PhiStack {
    phis: Vec<Phi>,
}

#[derive(Default)]
struct Phi {
    scope_pos: usize,
    own_vars: HashSet<String>,
    modified_vars: HashMap<String, Value>,
    header: Option<PhiHeader>,
}

struct PhiHeader {
    entry: BlockIdx,
    init: BlockIdx,
    first: BlockIdx,
    instructions: HashMap<String, InstrIdx>,
}

type ExprResult = Option<Value>;

struct TypeError {
    loc: Range,
    def: Option<Range>,
    layers: Vec<(TypeIdx, TypeIdx)>,
}

impl TypeError {
    fn child<T>(&mut self, a: TypeIdx, b: TypeIdx, f: impl FnOnce(&mut Self) -> T) -> T {
        self.layers.push((a, b));
        let t = f(self);
        self.layers.pop();
        t
    }
    fn commit(&mut self, ctx: &mut SemCtx) {
        let expected = format!("{}", FmtType(&ctx.ir, self.layers.first().unwrap().0));
        let found = format!("{}", FmtType(&ctx.ir, self.layers.first().unwrap().1));

        if self.layers.len() == 1 {
            ctx.errors.push(
                self.loc
                    .with(Error::TypeMismatch(self.def, expected, found)),
            );
        } else {
            let extended = self
                .layers
                .iter()
                .copied()
                .skip(1)
                .map(|(a, b)| {
                    (
                        format!("{}", FmtType(&ctx.ir, a)),
                        format!("{}", FmtType(&ctx.ir, b)),
                    )
                })
                .collect();
            ctx.errors.push(self.loc.with(Error::ExtendedTypeMismatch(
                self.def, expected, found, extended,
            )));
        }
    }
}

pub fn analyze(ast: &AST, errors: &mut Errors, target: &Target) -> SemIR {
    let mut ctx = SemCtx {
        ir: SemIR {
            effects: std::iter::repeat_with(Effect::default)
                .take(ast.effects.len())
                .collect(),
            fun_sign: std::iter::repeat_with(FunSign::default)
                .take(ast.functions.len())
                .collect(),
            fun_impl: std::iter::repeat_with(FunImpl::default)
                .take(ast.functions.len())
                .collect(),
            entry: None,

            types: VecSet::new(),
            handlers: VecMap::new(),
            lazy_handlers: VecMap::new(),

            generic_names: VecMap::new(),
            assoc_names: VecMap::new(),
        },
        ast,
        errors,
        packages: std::iter::repeat_with(Scope::default)
            .take(ast.packages.len())
            .collect(),
    };

    ctx.insert_type(Type::Unknown, false, false);
    ctx.insert_type(Type::None, false, false);
    ctx.insert_type(Type::Never, false, false);
    ctx.insert_type(Type::DataType(TypeConstraints::None), false, false);
    ctx.insert_type(Type::Effect, false, false);
    ctx.insert_type(Type::HandlerSelf, false, false);
    ctx.insert_type(Type::Integer(false, IntSize::Size), false, false);
    ctx.insert_type(Type::Bool, false, false);
    ctx.insert_type(Type::Integer(true, IntSize::Reg), false, false);
    ctx.insert_type(Type::Str, false, false);
    ctx.insert_type(Type::Char, false, false);
    ctx.insert_type(Type::Integer(false, IntSize::Bits(8)), false, false);

    let mut insert = |t: Type| {
        let ty = ctx.insert_type(t, false, false);
        let name = format!("{}", FmtType(&ctx.ir, ty));
        let name = String::from(&name[1..name.len() - 1]);
        let types = &mut ctx.packages[ast.preamble].types;
        types.insert(name, ty);
    };

    insert(Type::Str);
    insert(Type::Bool);
    insert(Type::Char);
    insert(Type::None);

    insert(Type::Integer(false, IntSize::Reg));
    insert(Type::Integer(true, IntSize::Reg));
    insert(Type::Integer(false, IntSize::Size));
    insert(Type::Integer(true, IntSize::Size));
    insert(Type::Integer(false, IntSize::Ptr));
    insert(Type::Integer(true, IntSize::Ptr));

    for i in 0u32..4 {
        let bits = 8u32 << i;
        insert(Type::Integer(false, IntSize::Bits(bits)));
        insert(Type::Integer(true, IntSize::Bits(bits)));
    }

    // analyze effect signatures
    for (idx, package) in ast.packages.iter(PackageIdx) {
        // TODO: single error on multiple effect names

        // put names in scope
        for (i, effect) in package
            .effects
            .iter()
            .copied()
            .map(|idx| (idx, &ast.effects[idx]))
        {
            let name = &ast.idents[effect.name];
            if let Some(&GenericVal::Literal(old)) = ctx.packages[idx].effects.get(&name.0) {
                // error on conflict
                ctx.errors.push(name.with(Error::MultipleEffectDefinitions(
                    ast.idents[ast.effects[old].name].empty(),
                )));
            } else {
                // add effect to scope
                ctx.packages[idx]
                    .effects
                    .insert(name.0.clone(), GenericVal::Literal(i));
            }
        }
    }

    // analyze function signatures
    for (idx, package) in ast.packages.iter(PackageIdx) {
        // TODO: single error on multiple function names

        let mut scope = ScopeStack::new(idx);
        for (i, effect) in package
            .effects
            .iter()
            .copied()
            .map(|idx| (idx, &ast.effects[idx]))
        {
            scope.child(|scope| {
                // get effect generics
                let mut generics = Generics::default();
                for param in effect.generics.iter().flat_map(|v| v.values()) {
                    let name = ast.idents[param.name].0.clone();
                    let ty = param
                        .ty
                        .map(|ty| ctx.analyze_type(scope, ty, None, true, &mut SemCtx::no_handler))
                        .unwrap_or(TYPE_DATATYPE);

                    let idx = ctx.ir.generic_names.push(GenericIdx, name.clone());
                    let value = Generic { idx, typeof_ty: ty };
                    generics.push(value);
                    scope.top().generics.insert(name, value);
                }
                ctx.ir.effects[i] = Effect {
                    name: ast.idents[effect.name].0.clone(),
                    generics,
                    assocs: Vec::new(),
                    funs: VecMap::new(),
                    implied: Vec::new(),
                };

                // add functions to scope
                let mut assoc_types = Vec::new();
                for (fi, decl) in effect.functions.iter(EffFunIdx) {
                    let sign = ctx.analyze_sign(
                        scope,
                        decl.name,
                        Some(i),
                        &decl.sign,
                        Some(&mut assoc_types),
                    );
                    ctx.ir.effects[i].funs.push_value(sign);

                    let name = &ast.idents[decl.name];
                    if let Some(&old) = ctx.packages[idx].funs.get(&name.0) {
                        // error on conflict
                        ctx.errors
                            .push(name.with(Error::MultipleFunctionDefinitions(
                                ast.idents[old.ident(&ctx)].empty(),
                            )));
                    } else {
                        // add function to scope
                        ctx.packages[idx]
                            .funs
                            .insert(name.0.clone(), FunIdent::Effect(i, fi));
                    }
                }
                ctx.ir.effects[i].assocs = assoc_types;
            });
        }

        for (i, fun) in package
            .functions
            .iter()
            .copied()
            .map(|i| (i, &ast.functions[i]))
        {
            // add function to scope
            let sign = ctx.analyze_sign(&mut scope, fun.decl.name, None, &fun.decl.sign, None);
            ctx.ir.fun_sign[i] = sign;

            let name = &ast.idents[fun.decl.name];
            if let Some(&old) = ctx.packages[idx].funs.get(&name.0) {
                // error on conflict
                ctx.errors
                    .push(name.with(Error::MultipleFunctionDefinitions(
                        ast.idents[old.ident(&ctx)].empty(),
                    )));
            } else {
                // add function to scope
                ctx.packages[idx]
                    .funs
                    .insert(name.0.clone(), FunIdent::Top(i));

                // check if main
                if idx == ast.main && name.0.eq("main") {
                    ctx.ir.entry = Some(i);
                }
            }
        }
    }

    // analyze implied
    // TODO: this doesn't allow implied handlers to use other implied handlers
    for (idx, package) in ast.packages.iter(PackageIdx) {
        let mut scope = ScopeStack::new(idx);
        for &implied in package.implied.iter() {
            let handler = match ast.exprs[implied].0 {
                Expression::Handler(ref handler) => handler,
                _ => unreachable!(),
            };
            ctx.analyze_implied(&mut scope, handler);
        }
    }

    // analyze functions
    for (idx, package) in ast.packages.iter(PackageIdx) {
        let mut scope = ScopeStack::new(idx);
        for (i, fun) in package
            .functions
            .iter()
            .copied()
            .map(|i| (i, &ast.functions[i]))
        {
            ctx.ir.fun_impl[i] =
                ctx.generate_function(Either::Left(i), fun.body, &mut scope, None, None);
        }
    }

    ctx.ir
}
