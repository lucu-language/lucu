use std::{
    collections::HashMap,
    fmt::{self},
};

use crate::{
    ast::{self, EffFunIdx, EffIdx, Expression, Ident, PackageIdx, AST},
    error::{Error, Errors},
    vecmap::{VecMap, VecMapOffset, VecSet},
    Target,
};

use super::{
    Assoc, AssocIdx, Effect, EffectIdent, FunIdx, FunSign, GenericIdx, GenericParams, GenericVal,
    Generics, Handler, HandlerIdx, LazyIdx, SemIR, Type, TypeConstraints, TypeIdx,
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
                TYPE_UNKNOWN_DATATYPE
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
            return TYPE_UNKNOWN_DATATYPE;
        };
        let name = &ctx.ast.idents[id];
        match ctx.packages[package].types.get(&name.0).copied() {
            Some(eff) => eff,
            None => {
                ctx.errors
                    .push(name.with(Error::UnknownPackageType(ctx.ast.idents[pkg].empty())));
                TYPE_UNKNOWN_DATATYPE
            }
        }
    }
}

const TYPE_UNKNOWN_DATATYPE: TypeIdx = TypeIdx(0);
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
        TYPE_UNKNOWN_DATATYPE
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

                if let Some(assoc_types) =
                    assoc_types.filter(|_| handler.can_move_to(handler_self, &self.ir))
                {
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
            Type::Unknown(inner) => {
                let inner = self.translate_generics(
                    inner,
                    generic_params,
                    parent_generics,
                    handler_self,
                    assoc_types,
                );
                self.insert_type(Type::Unknown(inner))
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
                if ty.can_move_to(typeof_generic, &self.ir) {
                    Some(idx)
                } else {
                    self.errors
                        .push(self.ast.idents[id].with(Error::TypeMismatch(
                            format!("{}", FmtType(&self.ir, typeof_generic)),
                            format!("{}", FmtType(&self.ir, ty)),
                        )));
                    None
                }
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
            T::Error => TYPE_UNKNOWN_DATATYPE,
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
                    None => return TYPE_UNKNOWN_DATATYPE,
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
                None => TYPE_UNKNOWN_DATATYPE,
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
                        None => return TYPE_UNKNOWN_DATATYPE,
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
                            None => return TYPE_UNKNOWN_DATATYPE,
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
                    generics.push(GenericIdx, ty);
                } else {
                    params.push(ty);
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
                        params.push(self.insert_type(Type::Generic(handler_ty, idx)));
                    }
                    None => {}
                }
            }

            // parent handler
            if effect.is_some() {
                params.push(TYPE_SELF);
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
                return_type,
            }
        })
    }
    fn sign_matches(
        &mut self,
        a: &FunSign,
        b: FunIdent,
        generic_params: &GenericParams,
        parent_generics: usize,
        assoc_types: &VecMap<AssocIdx, TypeIdx>,
    ) -> bool {
        let b = match b {
            FunIdent::Top(idx) => &self.ir.fun_sign[idx],
            FunIdent::Effect(eff, idx) => &self.ir.effects[eff].funs[idx],
        };
        let params = b.params.clone();
        let return_type = b.return_type;

        if a.params.len() != b.params.len() {
            return false;
        }

        for (a, b) in a.params.iter().copied().zip(params.into_iter()) {
            let translated = self.translate_generics(
                b,
                generic_params,
                parent_generics,
                TYPE_SELF,
                Some(assoc_types),
            );
            if !translated.can_move_to(a, &self.ir) {
                return false;
            }
        }

        let translated = self.translate_generics(
            return_type,
            generic_params,
            parent_generics,
            TYPE_SELF,
            Some(assoc_types),
        );
        if !a.return_type.can_move_to(translated, &self.ir) {
            return false;
        }

        true
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

            let generic_params = Generics::from_iter(0, params);

            // check functions
            let mut funs: VecMap<EffFunIdx, FunSign> = std::iter::repeat_with(FunSign::default)
                .take(self.ast.effects[effect].functions.len())
                .collect();
            let assoc_typeof = self.ir.effects[effect]
                .assoc_types
                .values()
                .map(|assoc| assoc.typeof_ty)
                .collect::<Vec<_>>();
            let mut assoc_types = assoc_typeof
                .into_iter()
                .map(|typeof_assoc| {
                    let translated = self.translate_generics(
                        typeof_assoc,
                        &generic_params,
                        generics.len(),
                        TYPE_SELF,
                        None,
                    );
                    self.insert_type(Type::Unknown(translated))
                })
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
                            self.ir.effects[effect].funs[idx].return_type,
                            &generic_params,
                            generics.len(),
                            TYPE_SELF,
                            None,
                        );
                        let _ = self.infer_type_params(
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
                            &mut assoc_types,
                            parent_return,
                            sign.return_type,
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

            // check if signatures match
            let mut missing = Vec::new();
            for (idx, sign) in funs.iter(EffFunIdx) {
                let name = self.ast.idents[self.ast.effects[effect].functions[idx].name].empty();

                // check if missing
                let Some(def) = sign.def else {
                    missing.push(name);
                    continue;
                };

                // check sign mismatch
                if !self.sign_matches(
                    &sign,
                    FunIdent::Effect(effect, idx),
                    &generic_params,
                    generics.len(),
                    &assoc_types,
                ) {
                    self.errors.push(def.with(Error::SignatureMismatch(
                        self.ast.idents[self.ast.effects[effect].name].empty(),
                        self.ast.idents[self.ast.effects[effect].functions[idx].name].empty(),
                    )));
                }
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
    fn infer_type_params<K: Into<usize>>(
        &mut self,
        convert: impl Fn(&Self, &Type) -> Option<K>,
        types: &mut VecMap<K, TypeIdx>,
        parent: TypeIdx,
        ty: TypeIdx,
    ) -> bool {
        self.matches(
            parent,
            ty,
            &mut |ctx, a, b| match convert(ctx, &ctx.ir.types[a]) {
                Some(idx) => {
                    let type_idx = &mut types[idx];
                    *type_idx = ctx.supertype(*type_idx, b)?;
                    Some(*type_idx)
                }
                None => None,
            },
        )
        .is_some()
    }
    fn supertype(&mut self, a: TypeIdx, b: TypeIdx) -> Option<TypeIdx> {
        self.matches(a, b, &mut |ctx, a, b| {
            if a == b {
                return Some(a);
            }
            match (&ctx.ir.types[a], &ctx.ir.types[b]) {
                (&Type::DataType(TypeConstraints::None), &Type::DataType(_)) => Some(TYPE_DATATYPE),
                (&Type::DataType(_), &Type::DataType(TypeConstraints::None)) => Some(TYPE_DATATYPE),

                (_, &Type::Never) if a.is_instance(TYPE_DATATYPE, &ctx.ir) => Some(a),
                (&Type::Never, _) if b.is_instance(TYPE_DATATYPE, &ctx.ir) => Some(b),
                (_, &Type::Unknown(typeof_ty)) if a.is_instance(typeof_ty, &ctx.ir) => Some(a),
                (&Type::Unknown(typeof_ty), _) if b.is_instance(typeof_ty, &ctx.ir) => Some(b),

                _ => None,
            }
        })
    }
    fn matches(
        &mut self,
        a: TypeIdx,
        b: TypeIdx,
        compare: &mut impl FnMut(&mut Self, TypeIdx, TypeIdx) -> Option<TypeIdx>,
    ) -> Option<TypeIdx> {
        // NOTE: 'matches' is generic-agnositc,
        // so it doesn't think two generics with same indices are the same

        // TODO: don't short-circuit
        compare(self, a, b).or_else(|| {
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

                            let fail = self.matches(fail_a, fail_b, compare)?;
                            let generic_params = generic_params
                                .into_iter()
                                .map(|(a, b)| self.matches(a, b, compare))
                                .collect::<Option<Vec<_>>>()?;
                            let generic_params = GenericParams::from_iter(start, generic_params);

                            Some(self.insert_type(Type::DataType(TypeConstraints::Handler(
                                GenericVal::Literal(EffectIdent {
                                    effect,
                                    generic_params,
                                }),
                                fail,
                            ))))
                        } else {
                            None
                        }
                    } else {
                        if eff_a == eff_b {
                            // TODO: compare effect
                            let eff = eff_a.clone();
                            let fail = self.matches(fail_a, fail_b, compare)?;
                            Some(
                                self.insert_type(Type::DataType(TypeConstraints::Handler(
                                    eff, fail,
                                ))),
                            )
                        } else {
                            None
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

                    let ty = self.matches(ty_a, ty_b, compare)?;
                    let handler = self.matches(handler_a, handler_b, compare)?;
                    let generic_params = generic_params
                        .into_iter()
                        .map(|(a, b)| self.matches(a, b, compare))
                        .collect::<Option<Vec<_>>>()?;
                    let generic_params = GenericParams::from_iter(start, generic_params);

                    Some(self.insert_type(Type::AssocType {
                        ty,
                        handler,
                        effect: eff_a,
                        idx: idx_a,
                        generic_params,
                    }))
                }

                (&Type::Unknown(ty_a), &Type::Unknown(ty_b)) => {
                    let typeof_ty = self.matches(ty_a, ty_b, compare)?;
                    Some(self.insert_type(Type::Unknown(typeof_ty)))
                }

                (&Type::Pointer(a), &Type::Pointer(b)) => {
                    let inner = self.matches(a, b, compare)?;
                    Some(self.insert_type(Type::Pointer(inner)))
                }
                (&Type::Const(a), &Type::Const(b)) => {
                    let inner = self.matches(a, b, compare)?;
                    Some(self.insert_type(Type::Const(inner)))
                }
                (&Type::Slice(a), &Type::Slice(b)) => {
                    let inner = self.matches(a, b, compare)?;
                    Some(self.insert_type(Type::Slice(inner)))
                }
                (&Type::ConstArray(size_a, a), &Type::ConstArray(size_b, b))
                    if size_a == size_b =>
                {
                    // TODO: compare size
                    let inner = self.matches(a, b, compare)?;
                    Some(self.insert_type(Type::ConstArray(size_a, inner)))
                }

                (Type::Int, Type::Int)
                | (Type::Effect, Type::Effect)
                | (Type::DataType(TypeConstraints::None), Type::DataType(TypeConstraints::None))
                | (Type::UInt, Type::UInt)
                | (Type::USize, Type::USize)
                | (Type::UPtr, Type::UPtr)
                | (Type::U8, Type::U8)
                | (Type::Str, Type::Str)
                | (Type::Bool, Type::Bool)
                | (Type::None, Type::None)
                | (Type::Never, Type::Never) => Some(a),

                (&Type::Handler(idx), &Type::Handler(idx2)) if idx == idx2 => Some(a),
                (&Type::LazyHandler(_, idx), &Type::LazyHandler(_, idx2)) if idx == idx2 => Some(a),

                _ => None,
            }
        })
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

    ctx.insert_type(Type::Unknown(TYPE_DATATYPE));
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
                    assoc_types: VecMap::new(), // TODO
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
