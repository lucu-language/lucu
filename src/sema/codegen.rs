use std::collections::HashMap;

use crate::{
    ast::{self, EffFunIdx, EffIdx, Expression, Ident, PackageIdx, AST},
    error::{Error, Errors},
    vecmap::{VecMap, VecMapOffset, VecSet},
    Target,
};

use super::{
    Effect, EffectIdent, FunIdx, FunSign, GenericIdx, GenericVal, Generics, Handler, HandlerIdx,
    SemIR, Type, TypeConstraints, TypeIdx,
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

struct ScopeStack {
    scopes: Vec<Scope>,
    package: PackageIdx,
}

#[derive(Default, Clone)]
struct Scope {
    funs: HashMap<String, FunIdent>,
    effects: HashMap<String, GenericVal<EffIdx>>,
    types: HashMap<String, TypeIdx>,
    generics: HashMap<String, GenericIdx>,
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
    fn get_generic(&self, ctx: &SemCtx, name: &str) -> Option<GenericIdx> {
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

impl SemCtx<'_> {
    fn no_handler(&mut self, _: &mut Generics, _: TypeIdx) -> TypeIdx {
        // TODO: error
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
    fn analyze_type(
        &mut self,
        scope: &mut ScopeStack,
        ty: ast::TypeIdx,
        mut generics: Option<&mut Generics>,
        generic_handler: bool,
        handler_output: impl FnOnce(&mut Self, &mut Generics, TypeIdx) -> TypeIdx,
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
                        self.insert_type(Type::Generic(idx))
                    }
                    None => handler_output(
                        self,
                        generics.unwrap_or(&mut VecMapOffset::new(0)),
                        handler_ty,
                    ),
                }
            }
            T::Generic(id) => {
                let name = &self.ast.idents[id];
                match scope.get_generic(self, &name.0) {
                    Some(idx) => {
                        // TODO: check if generic is type
                        self.insert_type(Type::Generic(idx))
                    }
                    None => match generics {
                        Some(generics) => {
                            let idx = generics.push(GenericIdx, TYPE_TYPE_UNCONSTRAINED);
                            scope.top().generics.insert(name.0.clone(), idx);
                            self.insert_type(Type::Generic(idx))
                        }
                        None => {
                            // TODO: custom error
                            self.errors.push(name.with(Error::UnknownType));
                            TYPE_UNKNOWN
                        }
                    },
                }
            }
            T::GenericHandler(id, fail) => {
                let fail = self.analyze_fail(scope, fail, generics.as_deref_mut(), generic_handler);

                let name = &self.ast.idents[id];
                let effect = match scope.get_generic(self, &name.0) {
                    Some(idx) => {
                        // TODO: check if generic is effect
                        GenericVal::Generic(idx)
                    }
                    None => match generics.as_deref_mut() {
                        Some(generics) => {
                            let idx = generics.push(GenericIdx, TYPE_EFFECT);
                            scope.top().generics.insert(name.0.clone(), idx);
                            GenericVal::Generic(idx)
                        }
                        None => {
                            // TODO: custom error
                            self.errors.push(name.with(Error::UnknownEffect));
                            return TYPE_UNKNOWN;
                        }
                    },
                };

                // create handler type
                let handler_ty =
                    self.insert_type(Type::Type(TypeConstraints::Handler(effect, fail)));
                match generics.as_deref_mut().filter(|_| generic_handler) {
                    Some(generics) => {
                        let idx = generics.push(GenericIdx, handler_ty);
                        self.insert_type(Type::Generic(idx))
                    }
                    None => handler_output(
                        self,
                        generics.unwrap_or(&mut VecMapOffset::new(0)),
                        handler_ty,
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
                        let name = &self.ast.idents[id];
                        match generics {
                            Some(generics) => {
                                let idx = generics.push(GenericIdx, TYPE_TYPE_UNCONSTRAINED);
                                GenericVal::Generic(idx)
                            }
                            None => {
                                // TODO: custom error
                                self.errors.push(name.with(Error::UnknownType));
                                return TYPE_UNKNOWN;
                            }
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
    ) -> FunSign {
        let fun = match ident {
            FunIdent::Top(idx) => &self.ast.functions[idx].decl.sign,
            FunIdent::Effect(eff, idx) => &self.ast.effects[eff].functions[idx].sign,
        };

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
                        params.push(self.insert_type(Type::Generic(idx)));
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
                Some(ty) => {
                    self.analyze_type(scope, ty, Some(&mut generics), false, |ir, generics, ty| {
                        let fun = match ident {
                            FunIdent::Top(idx) => super::FunIdent::Top(idx),
                            FunIdent::Effect(eff, idx) => {
                                super::FunIdent::Effect(TYPE_SELF, eff, idx)
                            }
                        };
                        let generic_params = generics
                            .keys(GenericIdx)
                            .map(|idx| ir.insert_type(Type::Generic(idx)))
                            .collect::<Vec<_>>();
                        ir.insert_type(Type::FunOutput {
                            ty,
                            fun,
                            generic_params: Generics::from_iter(generics.start(), generic_params),
                        })
                    })
                }
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

            // check functions
            // TODO

            // add implied handler to effect
            let handler = self.push_handler(Handler {
                debug_name: format!("H{}", self.ir.handlers.len()),
                generics,

                effect,
                generic_params: Generics::from_iter(0, params),
                fail,

                captures: Vec::new(),
                funs: VecMap::new(),
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
            entry: FunIdx(0),

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
        // TODO: error on conflict (or overloads?)
        for (i, effect) in package
            .effects
            .iter()
            .copied()
            .map(|idx| (idx, &ast.effects[idx]))
        {
            // add effect to scope
            let name = ast.idents[effect.name].0.clone();
            ctx.packages[idx]
                .effects
                .insert(name, GenericVal::Literal(i));
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
                    scope.top().generics.insert(name, idx);
                }
                let generics = generics;

                // add functions to scope
                let mut funs = VecMap::new();
                for (fi, decl) in effect.functions.iter(EffFunIdx) {
                    let sign = ctx.analyze_sign(
                        scope,
                        generics.len(),
                        ast.idents[decl.name].0.clone(),
                        FunIdent::Effect(i, fi),
                    );
                    funs.push_value(sign);

                    let name = ast.idents[decl.name].0.clone();
                    ctx.packages[idx].funs.insert(name, FunIdent::Effect(i, fi));
                }
                ctx.ir.effects[i] = Effect {
                    name: ast.idents[effect.name].0.clone(),
                    generics,
                    funs,
                    implied: Vec::new(),
                };
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
            );
            ctx.ir.fun_sign[i] = sign;

            let name = &ast.idents[fun.decl.name].0;
            ctx.packages[idx]
                .funs
                .insert(name.clone(), FunIdent::Top(i));

            // check if main
            if idx == ast.main && name == "main" {
                ctx.ir.entry = i;
                // TODO: error on double
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
