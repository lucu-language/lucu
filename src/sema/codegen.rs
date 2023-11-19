use std::collections::HashMap;

use crate::{
    ast::{self, EffFunIdx, EffIdx, Expression, Ident, PackageIdx, AST},
    error::{Error, Errors},
    vecmap::{VecMap, VecSet},
    Target,
};

use super::{
    Effect, EffectIdent, FunIdx, FunSign, GenericIdx, GenericVal, Generics, Handler, HandlerIdx,
    HandlerIdxRef, ImpliedHandler, SemIR, Type, TypeIdx,
};

struct SemCtx<'a> {
    ir: SemIR,
    ast: &'a AST,
    errors: &'a mut Errors,
    packages: VecMap<PackageIdx, Scope>,
}

#[derive(Clone, Copy)]
enum FunIdent {
    Function(FunIdx),
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
const TYPE_TYPE: TypeIdx = TypeIdx(3);
const TYPE_EFFECT: TypeIdx = TypeIdx(4);

impl SemCtx<'_> {
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        self.ir.types.insert(TypeIdx, ty).clone()
    }
    fn push_handler(&mut self, handler: Handler) -> HandlerIdx {
        self.ir.handlers.push(HandlerIdx, handler)
    }
    fn push_handler_ref(&mut self) -> HandlerIdxRef {
        let idx = self.ir.handler_refs.len();
        self.ir.handler_refs.push(None);
        HandlerIdxRef::Ref(idx)
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
            ast::FailType::Some(ty) => self.analyze_type(scope, ty, generics, generic_handler),
        }
    }
    fn analyze_type(
        &mut self,
        scope: &mut ScopeStack,
        ty: ast::TypeIdx,
        mut generics: Option<&mut Generics>,
        generic_handler: bool,
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
                            self.analyze_type(scope, ty, generics.as_deref_mut(), generic_handler)
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
                let effect_inst =
                    self.insert_type(Type::EffectInstance(effect.map(|&effect| EffectIdent {
                        effect,
                        generic_params: params.into(),
                    })));
                match generics.filter(|_| generic_handler) {
                    Some(generics) => {
                        let idx = generics.push(GenericIdx, effect_inst);
                        let handler = GenericVal::Generic(idx);
                        self.insert_type(Type::Handler {
                            effect: effect_inst,
                            fail,
                            handler,
                        })
                    }
                    None => {
                        let handler = GenericVal::Literal(self.push_handler_ref());
                        self.insert_type(Type::Handler {
                            effect: effect_inst,
                            fail,
                            handler,
                        })
                    }
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
                            let idx = generics.push(GenericIdx, TYPE_TYPE);
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

                let effect_inst = self.insert_type(Type::EffectInstance(effect));
                match generics.filter(|_| generic_handler) {
                    Some(generics) => {
                        let idx = generics.push(GenericIdx, effect_inst);
                        let handler = GenericVal::Generic(idx);
                        self.insert_type(Type::Handler {
                            effect: effect_inst,
                            fail,
                            handler,
                        })
                    }
                    None => {
                        let handler = GenericVal::Literal(self.push_handler_ref());
                        self.insert_type(Type::Handler {
                            effect: effect_inst,
                            fail,
                            handler,
                        })
                    }
                }
            }
            T::Pointer(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler);
                self.insert_type(Type::Pointer(inner))
            }
            T::Const(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler);
                self.insert_type(Type::Const(inner))
            }
            T::ConstArray(size, ty) => {
                let inner = self.analyze_type(scope, ty, generics.as_deref_mut(), generic_handler);
                let size = match self.ast.exprs[size].0 {
                    Expression::Int(i) => GenericVal::Literal(i),
                    Expression::Ident(id) => {
                        let name = &self.ast.idents[id];
                        match generics {
                            Some(generics) => {
                                let idx = generics.push(GenericIdx, TYPE_TYPE);
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
                let inner = self.analyze_type(scope, ty, generics, generic_handler);
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
        mut generics: Generics,
        name: String,
        fun: &ast::FunSign,
        parent: Option<EffectIdent>,
    ) -> FunSign {
        scope.child(|scope| {
            let mut params = Vec::new();

            // base params
            for param in fun.inputs.values() {
                let ty = self.analyze_type(scope, param.ty, Some(&mut generics), true);
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
                        .map(|ty| self.analyze_type(scope, ty, Some(&mut generics), true))
                        .collect(),
                    None => Vec::new(),
                };
                match self.analyze_effect(scope, &id.ident) {
                    Some(effect) => {
                        let handler_ty =
                            self.insert_type(Type::EffectInstance(effect.map(|&effect| {
                                EffectIdent {
                                    effect,
                                    generic_params: effect_params.into(),
                                }
                            })));
                        let idx = generics.push(GenericIdx, handler_ty);
                        params.push(self.insert_type(Type::BoundHandler {
                            effect: handler_ty,
                            handler: GenericVal::Generic(idx),
                        }));
                    }
                    None => {}
                }
            }

            // parent handler
            if let Some(parent) = parent {
                let instance = self.insert_type(Type::EffectInstance(GenericVal::Literal(parent)));
                let ty = self.insert_type(Type::BoundHandler {
                    effect: instance,
                    handler: GenericVal::Literal(HandlerIdxRef::Me),
                });
                params.push(ty);
            }

            // return type
            let return_type = match fun.output {
                Some(ty) => self.analyze_type(scope, ty, Some(&mut generics), false),
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
                    .map(|ty| self.analyze_type(scope, ty, Some(&mut generics), true))
                    .collect(),
                None => Vec::new(),
            };
            let fail = self.analyze_fail(scope, fail, Some(&mut generics), false);
            let effect = self.analyze_effect(scope, &id.ident)?.literal().copied()?;

            // check functions
            // TODO

            // add implied handler to effect
            let handler = self.push_handler(Handler {
                captures: TYPE_NONE,
                funs: VecMap::new(),
            });
            let handler = ImpliedHandler {
                generics,

                generic_params: params.into(),
                fail,
                handler,
            };
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
            handler_refs: Vec::new(),
        },
        ast,
        errors,
        packages: VecMap::filled(ast.packages.len(), Scope::default()),
    };

    ctx.insert_type(Type::Unknown);
    ctx.insert_type(Type::None);
    ctx.insert_type(Type::Never);
    ctx.insert_type(Type::Type);
    ctx.insert_type(Type::Effect);

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
    insert("never", Type::Never);

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
                        .map(|ty| ctx.analyze_type(scope, ty, None, true))
                        .unwrap_or(TYPE_TYPE);
                    let idx = generics.push(GenericIdx, ty);

                    let name = ast.idents[param.name].0.clone();
                    scope.top().generics.insert(name, idx);
                }

                // add functions to scope
                let mut funs = VecMap::new();
                for (fi, decl) in effect.functions.iter(EffFunIdx) {
                    let parent = EffectIdent {
                        effect: i,
                        generic_params: generics
                            .keys(GenericIdx)
                            .map(|idx| ctx.insert_type(Type::Generic(idx)))
                            .collect(),
                    };
                    let sign = ctx.analyze_sign(
                        scope,
                        generics.clone(),
                        ast.idents[decl.name].0.clone(),
                        &decl.sign,
                        Some(parent),
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
                Generics::default(),
                ast.idents[fun.decl.name].0.clone(),
                &fun.decl.sign,
                None,
            );
            ctx.ir.fun_sign[i] = sign;

            let name = &ast.idents[fun.decl.name].0;
            ctx.packages[idx]
                .funs
                .insert(name.clone(), FunIdent::Function(i));

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
