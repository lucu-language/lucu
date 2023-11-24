use std::{
    collections::HashMap,
    fmt::{self},
};

use crate::{
    ast::{self, EffFunIdx, EffIdx, Expression, Ident, PackageIdx, AST},
    error::{Error, Errors, Range},
    vecmap::{VecMap, VecMapOffset, VecSet},
    Target,
};

use super::{
    Assoc, AssocIdx, Effect, EffectIdent, FunIdx, FunSign, GenericIdx, GenericParams, GenericVal,
    Generics, Handler, HandlerIdx, LazyIdx, Param, ReturnType, SemIR, Type, TypeConstraints,
    TypeIdx,
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

#[derive(Default, Clone)]
struct Scope {
    funs: HashMap<String, FunIdent>,
    effects: HashMap<String, GenericVal<EffIdx>>,
    types: HashMap<String, TypeIdx>,
    generics: HashMap<String, (TypeIdx, GenericIdx)>,
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
    fn get_generic(&self, ctx: &SemCtx, name: &str) -> Option<(TypeIdx, GenericIdx)> {
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

const TYPE_UNKNOWN: TypeIdx = TypeIdx(0);
const TYPE_NONE: TypeIdx = TypeIdx(1);
const TYPE_NEVER: TypeIdx = TypeIdx(2);
const TYPE_DATATYPE: TypeIdx = TypeIdx(3);
const TYPE_EFFECT: TypeIdx = TypeIdx(4);
const TYPE_SELF: TypeIdx = TypeIdx(5);
const TYPE_USIZE: TypeIdx = TypeIdx(6);

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
    fn no_handler(&mut self, _: &mut Generics, _: TypeIdx, ty: ast::TypeIdx) -> TypeIdx {
        self.errors
            .push(self.ast.types[ty].with(Error::NotEnoughInfo));
        TYPE_UNKNOWN
    }
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        self.ir.types.insert(TypeIdx, ty).clone()
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
        assoc_types: Option<&VecMap<AssocIdx, TypeIdx>>,
    ) -> TypeIdx {
        let translate = |ctx: &mut Self, ty: TypeIdx, idx: GenericIdx| {
            if idx.0 < generic_params.start() {
                ctx.insert_type(Type::Generic(ty, idx))
            } else if idx.0 < generic_params.start() + generic_params.len() {
                generic_params[idx]
            } else {
                let idx = GenericIdx(idx.0 - generic_params.len() + parent_generics);
                ctx.insert_type(Type::Generic(ty, idx))
            }
        };
        match self.ir.types[ty] {
            Type::DataType(ref constraints) => match *constraints {
                TypeConstraints::None => ty,
                TypeConstraints::Handler(ref effect, fail) => {
                    let effect = match *effect {
                        GenericVal::Literal(ref ident) => {
                            let effect = ident.effect;
                            let start = ident.generic_params.start();
                            let params = Vec::from(ident.generic_params.clone());
                            let params = GenericParams::from_iter(
                                start,
                                params.into_iter().map(|ty| {
                                    self.translate_generics(
                                        ty,
                                        generic_params,
                                        parent_generics,
                                        handler_self,
                                        assoc_types,
                                    )
                                }),
                            );
                            GenericVal::Literal(EffectIdent {
                                effect,
                                generic_params: params,
                            })
                        }
                        GenericVal::Generic(idx) => {
                            let ty = translate(self, TYPE_EFFECT, idx);
                            match self.ir.types[ty] {
                                Type::Generic(_, idx) => GenericVal::Generic(idx),
                                _ => todo!(),
                            }
                        }
                    };
                    let fail = self.translate_generics(
                        fail,
                        generic_params,
                        parent_generics,
                        handler_self,
                        assoc_types,
                    );
                    self.insert_type(Type::DataType(TypeConstraints::Handler(effect, fail)))
                }
            },
            Type::AssocType {
                ty,
                handler,
                effect,
                idx,
                generic_params: ref params,
            } => {
                let start = params.start();
                let params = Vec::from(params.clone());
                let params = GenericParams::from_iter(
                    start,
                    params.into_iter().map(|ty| {
                        self.translate_generics(
                            ty,
                            generic_params,
                            parent_generics,
                            handler_self,
                            assoc_types,
                        )
                    }),
                );

                let ty = self.translate_generics(
                    ty,
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
                        assoc_types[idx],
                        &params,
                        parent_generics,
                        handler_self,
                        Some(assoc_types),
                    )
                } else {
                    self.insert_type(Type::AssocType {
                        ty,
                        handler,
                        effect,
                        idx,
                        generic_params: params,
                    })
                }
            }
            Type::Generic(ty, idx) => translate(self, ty, idx),
            Type::Pointer(inner) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::Pointer(inner))
            }
            Type::Const(inner) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::Const(inner))
            }
            Type::ConstArray(size, inner) => {
                let size = match size {
                    GenericVal::Literal(_) => size,
                    GenericVal::Generic(idx) => {
                        let ty = translate(self, TYPE_USIZE, idx);
                        match self.ir.types[ty] {
                            Type::Generic(_, idx) => GenericVal::Generic(idx),
                            _ => todo!(),
                        }
                    }
                };
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::ConstArray(size, inner))
            }
            Type::Slice(inner) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::Slice(inner))
            }
            Type::LazyHandler(inner, idx) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::LazyHandler(inner, idx))
            }
            Type::HandlerSelf => handler_self,

            Type::Handler(_)
            | Type::Effect
            | Type::Int
            | Type::UInt
            | Type::USize
            | Type::UPtr
            | Type::U8
            | Type::Str
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
    ) -> Option<GenericIdx> {
        let name = &self.ast.idents[id];
        match scope.get_generic(self, &name.0) {
            Some((ty, idx)) => {
                // check if generic type matches
                self.check_move_rev(
                    typeof_generic,
                    ty,
                    &mut TypeError {
                        loc: name.empty(),
                        def: None,
                        layers: Vec::new(),
                    },
                );
                Some(idx)
            }
            None => match generics {
                Some(generics) => {
                    let idx = generics.push(GenericIdx, typeof_generic);
                    scope
                        .top()
                        .generics
                        .insert(name.0.clone(), (typeof_generic, idx));
                    Some(idx)
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
                let handler_ty = self.insert_type(Type::DataType(TypeConstraints::Handler(
                    effect.map(|&effect| EffectIdent {
                        effect,
                        generic_params: Generics::from_iter(0, params),
                    }),
                    fail,
                )));
                match generics.as_deref_mut().filter(|_| generic_handler) {
                    Some(generics) => {
                        let idx = generics.push(GenericIdx, handler_ty);
                        self.insert_type(Type::Generic(handler_ty, idx))
                    }
                    None => handler_output(
                        self,
                        generics.unwrap_or(&mut VecMapOffset::new(0)),
                        handler_ty,
                        ty,
                    ),
                }
            }
            T::Generic(id) => match self.analyze_generic(scope, id, TYPE_DATATYPE, generics) {
                Some(idx) => self.insert_type(Type::Generic(TYPE_DATATYPE, idx)),
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
                        Some(idx) => GenericVal::Generic(idx),
                        None => return TYPE_UNKNOWN,
                    };

                // create handler type
                let handler_ty =
                    self.insert_type(Type::DataType(TypeConstraints::Handler(effect, fail)));
                match generics.as_deref_mut().filter(|_| generic_handler) {
                    Some(generics) => {
                        let idx = generics.push(GenericIdx, handler_ty);
                        self.insert_type(Type::Generic(handler_ty, idx))
                    }
                    None => handler_output(
                        self,
                        generics.unwrap_or(&mut VecMapOffset::new(0)),
                        handler_ty,
                        ty,
                    ),
                }
            }
            T::Pointer(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Pointer(inner))
            }
            T::Const(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Const(inner))
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
                            Some(idx) => GenericVal::Generic(idx),
                            None => return TYPE_UNKNOWN,
                        }
                    }
                    _ => todo!(),
                };
                self.insert_type(Type::ConstArray(size, inner))
            }
            T::Slice(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Slice(inner))
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
        parent_generics: usize,
        name: Ident,
        effect: Option<EffIdx>,
        fun: &ast::FunSign,
        mut assoc: Option<&mut VecMap<AssocIdx, Assoc>>,
    ) -> FunSign {
        scope.child(|scope| {
            let name = &self.ast.idents[name];
            let mut generics = Generics::new(parent_generics);
            let mut params = Vec::new();

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
                        Some(idx) => self.insert_type(Type::Generic(ty, idx)),
                        None => TYPE_UNKNOWN,
                    };
                    params.push(Param {
                        name_def: Some(self.ast.idents[param.name].empty()),
                        type_def: self.ast.types[param.ty].empty(),
                        ty,
                    });
                } else {
                    params.push(Param {
                        name_def: Some(self.ast.idents[param.name].empty()),
                        type_def: self.ast.types[param.ty].empty(),
                        ty,
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
                        let handler_ty =
                            self.insert_type(Type::DataType(TypeConstraints::Handler(
                                effect.map(|&effect| EffectIdent {
                                    effect,
                                    generic_params: Generics::from_iter(0, effect_params),
                                }),
                                TYPE_NEVER,
                            )));
                        let idx = generics.push(GenericIdx, handler_ty);
                        let ty = self.insert_type(Type::Generic(handler_ty, idx));
                        params.push(Param {
                            name_def: Some(self.ast.idents[id.ident.ident].empty()),
                            type_def: self.ast.idents[id.ident.ident].empty(),
                            ty,
                        });
                    }
                    None => {}
                }
            }

            // parent handler
            if let Some(effect) = effect {
                params.push(Param {
                    name_def: Some(self.ast.idents[self.ast.effects[effect].name].empty()),
                    type_def: self.ast.idents[self.ast.effects[effect].name].empty(),
                    ty: TYPE_SELF,
                });
            }

            // return type
            let mut assocs = 0;
            let return_type = match fun.output {
                Some(ty) => self.analyze_type(
                    scope,
                    ty,
                    Some(&mut generics),
                    false,
                    &mut |ctx, generics, ty, _| match &mut assoc {
                        Some(assoc) => {
                            let effect = effect.unwrap();
                            let idx = assoc.push(
                                AssocIdx,
                                Assoc {
                                    name: format!("{}${}", name.0, assocs),
                                    infer: true,
                                    typeof_ty: ty,
                                    generics: generics.clone(),
                                },
                            );
                            assocs += 1;
                            let effect_generics_len = ctx.ir.effects[effect].generics.len();
                            let generic_params = generics
                                .iter(GenericIdx)
                                .map(|(idx, &ty)| ctx.insert_type(Type::Generic(ty, idx)))
                                .collect::<Vec<_>>();
                            ctx.insert_type(Type::AssocType {
                                ty,
                                handler: TYPE_SELF,
                                effect,
                                idx,
                                generic_params: GenericParams::from_iter(
                                    effect_generics_len,
                                    generic_params,
                                ),
                            })
                        }
                        None => {
                            let idx = ctx.ir.lazy_handlers.push(LazyIdx, None);
                            ctx.insert_type(Type::LazyHandler(ty, idx))
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
        assoc_types: &VecMap<AssocIdx, TypeIdx>,
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

        for (a, b) in a.params.iter().zip(params.into_iter()) {
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
            let generic_params = Generics::from_iter(0, params);

            // check functions
            let mut funs: VecMap<EffFunIdx, FunSign> = std::iter::repeat_with(FunSign::default)
                .take(self.ast.effects[effect].functions.len())
                .collect();
            let assoc_typeof_types = self.ir.effects[effect]
                .assoc_types
                .values()
                .map(|assoc| assoc.typeof_ty)
                .collect::<Vec<_>>();
            let assoc_typeof_types = assoc_typeof_types
                .into_iter()
                .map(|assoc| {
                    self.translate_generics(assoc, &generic_params, generics.len(), TYPE_SELF, None)
                })
                .collect::<VecMap<_, _>>();
            let mut assoc_types = std::iter::repeat(TYPE_UNKNOWN)
                .take(assoc_typeof_types.len())
                .collect::<VecMap<_, _>>();
            for function in functions {
                // analyze signature
                let name = &self.ast.idents[function.decl.name];
                let matching = self.ast.effects[effect]
                    .functions
                    .iter(EffFunIdx)
                    .find(|(_, decl)| self.ast.idents[decl.name].0.eq(&name.0));

                let sign = self.analyze_sign(
                    scope,
                    generics.len(),
                    function.decl.name,
                    Some(effect),
                    &function.decl.sign,
                    None,
                );

                // analyze function
                // TODO

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
                                Type::AssocType { handler, idx, .. } => {
                                    if handler == TYPE_SELF
                                        && ctx.ir.effects[effect].assoc_types[idx].infer
                                    {
                                        Some(idx)
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
                        funs[idx] = sign;
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
            for (idx, sign) in funs.iter(EffFunIdx) {
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
    fn check_and_infer<K: Copy + Into<usize>>(
        &mut self,
        convert: impl Fn(&Self, &Type) -> Option<K>,
        typeof_types: &VecMap<K, TypeIdx>,
        types: &mut VecMap<K, TypeIdx>,
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
                        ctx.check_move_rev(typeof_types[idx], typeof_b, error_loc);
                    } else {
                        ctx.check_move(typeof_types[idx], typeof_b, error_loc);
                    }

                    let type_idx = &mut types[idx];
                    *type_idx = ctx.supertype(*type_idx, b, error_loc);
                    Some(*type_idx)
                }
                None => None,
            },
        );
    }
    fn supertype(&mut self, a: TypeIdx, b: TypeIdx, error_loc: &mut TypeError) -> TypeIdx {
        self.matches(a, b, error_loc, &mut |ctx, a, b, _| {
            if a == b {
                return Some(a);
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
        self.matches(from, to, error_loc, &mut |ctx, from, to, _| {
            if from == to {
                return Some(from);
            }
            match (&ctx.ir.types[from], &ctx.ir.types[to]) {
                (&Type::DataType(_), &Type::DataType(TypeConstraints::None)) => Some(TYPE_DATATYPE),

                (_, Type::Unknown) => Some(from),
                (Type::Never, _) => Some(to),
                (Type::Unknown, _) => Some(to),

                _ => None,
            }
        });
    }
    fn check_move_rev(&mut self, to: TypeIdx, from: TypeIdx, error_loc: &mut TypeError) {
        self.matches(to, from, error_loc, &mut |ctx, to, from, _| {
            if to == from {
                return Some(to);
            }
            match (&ctx.ir.types[to], &ctx.ir.types[from]) {
                (&Type::DataType(TypeConstraints::None), &Type::DataType(_)) => Some(TYPE_DATATYPE),

                (_, Type::Never) => Some(to),
                (_, Type::Unknown) => Some(to),
                (Type::Unknown, _) => Some(from),

                _ => None,
            }
        });
    }
    fn typeof_ty(&mut self, ty: TypeIdx) -> TypeIdx {
        match self.ir.types[ty] {
            Type::Handler(idx) => {
                let handler = &self.ir.handlers[idx];
                self.insert_type(Type::DataType(TypeConstraints::Handler(
                    GenericVal::Literal(EffectIdent {
                        effect: handler.effect,
                        generic_params: handler.generic_params.clone(),
                    }),
                    handler.fail,
                )))
            }

            Type::Generic(typeof_ty, _) => typeof_ty,
            Type::LazyHandler(typeof_ty, _) => typeof_ty,
            Type::AssocType { ty: typeof_ty, .. } => typeof_ty,

            Type::HandlerSelf => TYPE_DATATYPE,
            Type::Pointer(_) => TYPE_DATATYPE,
            Type::Const(_) => TYPE_DATATYPE,
            Type::ConstArray(_, _) => TYPE_DATATYPE,
            Type::Slice(_) => TYPE_DATATYPE,
            Type::Int => TYPE_DATATYPE,
            Type::UInt => TYPE_DATATYPE,
            Type::USize => TYPE_DATATYPE,
            Type::UPtr => TYPE_DATATYPE,
            Type::U8 => TYPE_DATATYPE,
            Type::Str => TYPE_DATATYPE,
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
                match (&self.ir.types[a], &self.ir.types[b]) {
                    (
                        &Type::DataType(TypeConstraints::Handler(ref eff_a, fail_a)),
                        &Type::DataType(TypeConstraints::Handler(ref eff_b, fail_b)),
                    ) => {
                        if let (GenericVal::Literal(a), GenericVal::Literal(b)) = (eff_a, eff_b) {
                            if a.effect == b.effect {
                                let effect = a.effect;
                                let start = a.generic_params.start();
                                let generic_params = a
                                    .generic_params
                                    .values()
                                    .copied()
                                    .zip(b.generic_params.values().copied())
                                    .collect::<Vec<_>>();

                                let fail = self.matches(fail_a, fail_b, error_loc, compare);
                                let generic_params = generic_params
                                    .into_iter()
                                    .map(|(a, b)| self.matches(a, b, error_loc, compare));
                                let generic_params =
                                    GenericParams::from_iter(start, generic_params);

                                self.insert_type(Type::DataType(TypeConstraints::Handler(
                                    GenericVal::Literal(EffectIdent {
                                        effect,
                                        generic_params,
                                    }),
                                    fail,
                                )))
                            } else {
                                TypeError::commit(error_loc, self);
                                TYPE_UNKNOWN
                            }
                        } else {
                            if eff_a == eff_b {
                                // TODO: compare effect
                                let eff = eff_a.clone();
                                let fail = self.matches(fail_a, fail_b, error_loc, compare);

                                self.insert_type(Type::DataType(TypeConstraints::Handler(
                                    eff, fail,
                                )))
                            } else {
                                TypeError::commit(error_loc, self);
                                TYPE_UNKNOWN
                            }
                        }
                    }

                    (
                        &Type::AssocType {
                            ty: ty_a,
                            handler: handler_a,
                            effect: eff_a,
                            idx: idx_a,
                            generic_params: ref generic_a,
                        },
                        &Type::AssocType {
                            ty: ty_b,
                            handler: handler_b,
                            effect: eff_b,
                            idx: idx_b,
                            generic_params: ref generic_b,
                        },
                    ) if eff_a == eff_b && idx_a == idx_b => {
                        let start = generic_a.start();
                        let generic_params = generic_a
                            .values()
                            .copied()
                            .zip(generic_b.values().copied())
                            .collect::<Vec<_>>();

                        let ty = self.matches(ty_a, ty_b, error_loc, compare);
                        let handler = self.matches(handler_a, handler_b, error_loc, compare);
                        let generic_params = generic_params
                            .into_iter()
                            .map(|(a, b)| self.matches(a, b, error_loc, compare));
                        let generic_params = GenericParams::from_iter(start, generic_params);

                        self.insert_type(Type::AssocType {
                            ty,
                            handler,
                            effect: eff_a,
                            idx: idx_a,
                            generic_params,
                        })
                    }

                    (&Type::Pointer(a), &Type::Pointer(b)) => {
                        let inner = self.matches(a, b, error_loc, compare);
                        self.insert_type(Type::Pointer(inner))
                    }
                    (&Type::Const(a), &Type::Const(b)) => {
                        let inner = self.matches(a, b, error_loc, compare);
                        self.insert_type(Type::Const(inner))
                    }
                    (&Type::Slice(a), &Type::Slice(b)) => {
                        let inner = self.matches(a, b, error_loc, compare);
                        self.insert_type(Type::Slice(inner))
                    }
                    (&Type::ConstArray(size_a, a), &Type::ConstArray(size_b, b))
                        if size_a == size_b =>
                    {
                        // TODO: compare size
                        let inner = self.matches(a, b, error_loc, compare);
                        self.insert_type(Type::ConstArray(size_a, inner))
                    }

                    (Type::Int, Type::Int)
                    | (Type::Unknown, Type::Unknown)
                    | (Type::Effect, Type::Effect)
                    | (
                        Type::DataType(TypeConstraints::None),
                        Type::DataType(TypeConstraints::None),
                    )
                    | (Type::UInt, Type::UInt)
                    | (Type::USize, Type::USize)
                    | (Type::UPtr, Type::UPtr)
                    | (Type::U8, Type::U8)
                    | (Type::Str, Type::Str)
                    | (Type::Bool, Type::Bool)
                    | (Type::None, Type::None)
                    | (Type::Never, Type::Never) => a,

                    (&Type::Handler(idx), &Type::Handler(idx2)) if idx == idx2 => a,
                    (&Type::LazyHandler(_, idx), &Type::LazyHandler(_, idx2)) if idx == idx2 => a,

                    _ => {
                        TypeError::commit(error_loc, self);
                        TYPE_UNKNOWN
                    }
                }
            })
        })
    }
}

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
            entry: None,

            types: VecSet::new(),
            handlers: VecMap::new(),
            lazy_handlers: VecMap::new(),
        },
        ast,
        errors,
        packages: VecMap::filled(ast.packages.len(), Scope::default()),
    };

    ctx.insert_type(Type::Unknown);
    ctx.insert_type(Type::None);
    ctx.insert_type(Type::Never);
    ctx.insert_type(Type::DataType(TypeConstraints::None));
    ctx.insert_type(Type::Effect);
    ctx.insert_type(Type::HandlerSelf);
    ctx.insert_type(Type::USize);

    let mut insert = |s: &str, t: Type| {
        let ty = ctx.insert_type(t);
        let types = &mut ctx.packages[ast.preamble].types;
        types.insert(s.into(), ty);
    };

    insert("str", Type::Str);
    insert("int", Type::Int);
    insert("uint", Type::UInt);
    insert("usize", Type::USize);
    insert("uptr", Type::UPtr);
    insert("u8", Type::U8);
    insert("bool", Type::Bool);
    insert("void", Type::None);

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
                    let ty = param
                        .ty
                        .map(|ty| ctx.analyze_type(scope, ty, None, true, &mut SemCtx::no_handler))
                        .unwrap_or(TYPE_DATATYPE);
                    let idx = generics.push(GenericIdx, ty);

                    let name = ast.idents[param.name].0.clone();
                    scope.top().generics.insert(name, (ty, idx));
                }
                let generics_len = generics.len();
                ctx.ir.effects[i] = Effect {
                    name: ast.idents[effect.name].0.clone(),
                    generics,
                    assoc_types: VecMap::new(),
                    funs: VecMap::new(),
                    implied: Vec::new(),
                };

                // add functions to scope
                let mut assoc_types = VecMap::new();
                for (fi, decl) in effect.functions.iter(EffFunIdx) {
                    let sign = ctx.analyze_sign(
                        scope,
                        generics_len,
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
                ctx.ir.effects[i].assoc_types = assoc_types;
            });
        }

        for (i, fun) in package
            .functions
            .iter()
            .copied()
            .map(|i| (i, &ast.functions[i]))
        {
            // add function to scope
            let sign = ctx.analyze_sign(&mut scope, 0, fun.decl.name, None, &fun.decl.sign, None);
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
    // TODO

    ctx.ir
}
