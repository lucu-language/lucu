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
    Effect, EffectIdent, FunIdx, FunSign, GenericIdx, GenericParams, GenericVal, Generics, Handler,
    HandlerIdx, SemIR, Type, TypeConstraints, TypeIdx,
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
const TYPE_TYPE_UNCONSTRAINED: TypeIdx = TypeIdx(3);
const TYPE_EFFECT: TypeIdx = TypeIdx(4);
const TYPE_SELF: TypeIdx = TypeIdx(5);
const TYPE_USIZE: TypeIdx = TypeIdx(6);

struct FmtType<'a>(&'a SemIR, TypeIdx);

impl fmt::Display for FmtType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'")?;
        self.1.display(self.0, f)?;
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
    ) -> TypeIdx {
        match fail {
            ast::FailType::Never => TYPE_NEVER,
            ast::FailType::None => TYPE_NONE,
            ast::FailType::Some(ty) => {
                self.analyze_type(scope, ty, generics, generic_handler, Self::no_handler)
            }
        }
    }
    fn translate_generics(
        &mut self,
        ty: TypeIdx,
        generic_params: &GenericParams,
        generics: &Generics,
    ) -> TypeIdx {
        let translate = |ctx: &mut Self, idx: GenericIdx| {
            if idx.0 < generic_params.len() {
                generic_params[idx]
            } else {
                let idx = GenericIdx(idx.0 - generic_params.len() + generics.start());
                let ty = generics[idx];
                ctx.insert_type(Type::Generic(ty, idx))
            }
        };
        match self.ir.types[ty] {
            Type::Type(ref constraints) => match *constraints {
                TypeConstraints::None => ty,
                TypeConstraints::Handler(ref effect, fail) => {
                    let effect = match *effect {
                        GenericVal::Literal(ref ident) => {
                            let effect = ident.effect;
                            let start = ident.generic_params.start();
                            let params = Vec::from(ident.generic_params.clone());
                            let params = VecMapOffset::from_iter(
                                start,
                                params.into_iter().map(|ty| {
                                    self.translate_generics(ty, generic_params, generics)
                                }),
                            );
                            GenericVal::Literal(EffectIdent {
                                effect,
                                generic_params: params,
                            })
                        }
                        GenericVal::Generic(idx) => {
                            let ty = translate(self, idx);
                            match self.ir.types[ty] {
                                Type::Generic(_, idx) => GenericVal::Generic(idx),
                                _ => todo!(),
                            }
                        }
                    };
                    let fail = self.translate_generics(fail, generic_params, generics);
                    self.insert_type(Type::Type(TypeConstraints::Handler(effect, fail)))
                }
            },
            Type::FunOutput {
                ty,
                fun,
                generic_params: ref params,
            } => {
                let start = params.start();
                let params = Vec::from(params.clone());
                let params = VecMapOffset::from_iter(
                    start,
                    params
                        .into_iter()
                        .map(|ty| self.translate_generics(ty, generic_params, generics)),
                );

                let ty = self.translate_generics(ty, generic_params, generics);
                let fun = match fun {
                    super::FunIdent::Top(_) => fun,
                    super::FunIdent::Effect(handler, eff, idx) => {
                        let handler = self.translate_generics(handler, generic_params, generics);
                        super::FunIdent::Effect(handler, eff, idx)
                    }
                };

                self.insert_type(Type::FunOutput {
                    ty,
                    fun,
                    generic_params: params,
                })
            }
            Type::Generic(_, idx) => translate(self, idx),
            Type::Pointer(inner) => {
                let inner = self.translate_generics(inner, generic_params, generics);
                self.insert_type(Type::Pointer(inner))
            }
            Type::Const(inner) => {
                let inner = self.translate_generics(inner, generic_params, generics);
                self.insert_type(Type::Const(inner))
            }
            Type::ConstArray(size, inner) => {
                let size = match size {
                    GenericVal::Literal(_) => size,
                    GenericVal::Generic(idx) => {
                        let ty = translate(self, idx);
                        match self.ir.types[ty] {
                            Type::Generic(_, idx) => GenericVal::Generic(idx),
                            _ => todo!(),
                        }
                    }
                };
                let inner = self.translate_generics(inner, generic_params, generics);
                self.insert_type(Type::ConstArray(size, inner))
            }
            Type::Slice(inner) => {
                let inner = self.translate_generics(inner, generic_params, generics);
                self.insert_type(Type::Slice(inner))
            }

            Type::Handler(_)
            | Type::HandlerSelf
            | Type::Effect
            | Type::Int
            | Type::UInt
            | Type::USize
            | Type::UPtr
            | Type::U8
            | Type::Str
            | Type::Bool
            | Type::None
            | Type::Never
            | Type::Unknown => ty,
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
        handler_output: impl FnOnce(&mut Self, &mut Generics, TypeIdx, ast::TypeIdx) -> TypeIdx,
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
                                Self::no_handler,
                            )
                        })
                        .collect(),
                    None => Vec::new(),
                };
                let fail = self.analyze_fail(scope, fail, generics.as_deref_mut(), generic_handler);
                let effect = match self.analyze_effect(scope, &id.ident) {
                    Some(effect) => effect,
                    None => return TYPE_UNKNOWN,
                };

                // create handler type
                let handler_ty = self.insert_type(Type::Type(TypeConstraints::Handler(
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
            T::Generic(id) => {
                match self.analyze_generic(scope, id, TYPE_TYPE_UNCONSTRAINED, generics) {
                    Some(idx) => self.insert_type(Type::Generic(TYPE_TYPE_UNCONSTRAINED, idx)),
                    None => TYPE_UNKNOWN,
                }
            }
            T::GenericHandler(id, fail) => {
                let fail = self.analyze_fail(scope, fail, generics.as_deref_mut(), generic_handler);

                let effect =
                    match self.analyze_generic(scope, id, TYPE_EFFECT, generics.as_deref_mut()) {
                        Some(idx) => GenericVal::Generic(idx),
                        None => return TYPE_UNKNOWN,
                    };

                // create handler type
                let handler_ty =
                    self.insert_type(Type::Type(TypeConstraints::Handler(effect, fail)));
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
                let inner =
                    self.analyze_type(scope, ty, generics, generic_handler, Self::no_handler);
                self.insert_type(Type::Pointer(inner))
            }
            T::Const(ty) => {
                let inner =
                    self.analyze_type(scope, ty, generics, generic_handler, Self::no_handler);
                self.insert_type(Type::Const(inner))
            }
            T::ConstArray(size, ty) => {
                let inner = self.analyze_type(
                    scope,
                    ty,
                    generics.as_deref_mut(),
                    generic_handler,
                    Self::no_handler,
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
                let inner =
                    self.analyze_type(scope, ty, generics, generic_handler, Self::no_handler);
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
        name: String,
        ident: FunIdent,
        fun: &ast::FunSign,
    ) -> FunSign {
        scope.child(|scope| {
            let mut generics = Generics::new(parent_generics);
            let mut params = Vec::new();

            // base params
            for param in fun.inputs.values() {
                let ty =
                    self.analyze_type(scope, param.ty, Some(&mut generics), true, Self::no_handler);
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
                                Self::no_handler,
                            )
                        })
                        .collect(),
                    None => Vec::new(),
                };
                match self.analyze_effect(scope, &id.ident) {
                    Some(effect) => {
                        let handler_ty = self.insert_type(Type::Type(TypeConstraints::Handler(
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
            if matches!(ident, FunIdent::Effect(..)) {
                params.push(TYPE_SELF);
            }

            // return type
            let return_type = match fun.output {
                Some(ty) => self.analyze_type(
                    scope,
                    ty,
                    Some(&mut generics),
                    false,
                    |ctx, generics, ty, _| {
                        let fun = match ident {
                            FunIdent::Top(idx) => super::FunIdent::Top(idx),
                            FunIdent::Effect(eff, idx) => {
                                super::FunIdent::Effect(TYPE_SELF, eff, idx)
                            }
                        };
                        let effect_generics_len = match ident {
                            FunIdent::Top(_) => 0,
                            FunIdent::Effect(idx, _) => ctx.ir.effects[idx].generics.len(),
                        };
                        let generic_params = generics
                            .iter(GenericIdx)
                            .map(|(idx, &ty)| ctx.insert_type(Type::Generic(ty, idx)))
                            .collect::<Vec<_>>();
                        ctx.insert_type(Type::FunOutput {
                            ty,
                            fun,
                            generic_params: Generics::from_iter(
                                effect_generics_len,
                                generic_params,
                            ),
                        })
                    },
                ),
                None => TYPE_NONE,
            };

            FunSign {
                name,
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
        generics: &Generics,
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
            let translated = self.translate_generics(b, generic_params, generics);
            if !translated.can_move_to(a, &self.ir) {
                return false;
            }
        }

        let translated = self.translate_generics(return_type, generic_params, generics);
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
                        self.analyze_type(scope, ty, Some(&mut generics), true, Self::no_handler)
                    })
                    .collect(),
                None => Vec::new(),
            };
            let fail = self.analyze_fail(scope, fail, Some(&mut generics), false);
            let effect = self.analyze_effect(scope, &id.ident)?.literal().copied()?;

            let generic_params = Generics::from_iter(0, params);

            // check functions
            let mut funs: VecMap<EffFunIdx, FunSign> = std::iter::repeat_with(FunSign::default)
                .take(self.ast.effects[effect].functions.len())
                .collect();
            for function in functions {
                // analyze signature
                let name = &self.ast.idents[function.decl.name];
                let matching = self.ast.effects[effect]
                    .functions
                    .iter(EffFunIdx)
                    .find(|(_, decl)| self.ast.idents[decl.name].0.eq(&name.0));

                let Some((idx, _)) = matching else {
                    self.errors.push(name.with(Error::UnknownEffectFun(
                        Some(self.ast.idents[self.ast.effects[effect].name].empty()),
                        Some(self.ast.idents[id.ident.ident].empty()),
                    )));
                    continue;
                };

                let sign = self.analyze_sign(
                    scope,
                    generics.len(),
                    name.0.clone(),
                    FunIdent::Effect(effect, idx),
                    &function.decl.sign,
                );

                if !self.sign_matches(
                    &sign,
                    FunIdent::Effect(effect, idx),
                    &generic_params,
                    &sign.generics,
                ) {
                    self.errors.push(name.with(Error::SignatureMismatch(
                        self.ast.idents[self.ast.effects[effect].name].empty(),
                        self.ast.idents[self.ast.effects[effect].functions[idx].name].empty(),
                    )));
                    continue;
                }

                funs[idx] = sign;

                // analyze function
                // TODO
            }

            // check for missing functions
            let missing = self.ast.effects[effect]
                .functions
                .values()
                .filter_map(|decl| {
                    let name = &self.ast.idents[decl.name];
                    if functions
                        .iter()
                        .any(|f| self.ast.idents[f.decl.name].0.eq(&name.0))
                    {
                        None
                    } else {
                        Some(name.empty())
                    }
                })
                .collect::<Vec<_>>();

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

                captures: Vec::new(),
                funs,
            });
            self.ir.effects[effect].implied.push(handler);

            Some(())
        });
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
        },
        ast,
        errors,
        packages: VecMap::filled(ast.packages.len(), Scope::default()),
    };

    ctx.insert_type(Type::Unknown);
    ctx.insert_type(Type::None);
    ctx.insert_type(Type::Never);
    ctx.insert_type(Type::Type(TypeConstraints::None));
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
                        .map(|ty| ctx.analyze_type(scope, ty, None, true, SemCtx::no_handler))
                        .unwrap_or(TYPE_TYPE_UNCONSTRAINED);
                    let idx = generics.push(GenericIdx, ty);

                    let name = ast.idents[param.name].0.clone();
                    scope.top().generics.insert(name, (ty, idx));
                }
                let generics_len = generics.len();
                ctx.ir.effects[i] = Effect {
                    name: ast.idents[effect.name].0.clone(),
                    generics,
                    funs: VecMap::new(),
                    implied: Vec::new(),
                };

                // add functions to scope
                for (fi, decl) in effect.functions.iter(EffFunIdx) {
                    let sign = ctx.analyze_sign(
                        scope,
                        generics_len,
                        ast.idents[decl.name].0.clone(),
                        FunIdent::Effect(i, fi),
                        &decl.sign,
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
            });
        }

        for (i, fun) in package
            .functions
            .iter()
            .copied()
            .map(|i| (i, &ast.functions[i]))
        {
            // add function to scope
            let sign = ctx.analyze_sign(
                &mut scope,
                0,
                ast.idents[fun.decl.name].0.clone(),
                FunIdent::Top(i),
                &fun.decl.sign,
            );
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
