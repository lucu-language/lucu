use std::collections::HashMap;

use crate::{
    ast::{self, EffFunIdx, EffIdx, Expression, Ident, PackageIdx, AST},
    error::{Error, Errors},
    vecmap::{VecMap, VecSet},
    Target,
};

use super::{
    Effect, FunIdx, FunSign, GenericIdx, GenericVal, Generics, Handler, HandlerIdx, SemIR, Type,
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
}

const TYPE_UNKNOWN: TypeIdx = TypeIdx(0);
const TYPE_NONE: TypeIdx = TypeIdx(1);
const TYPE_NEVER: TypeIdx = TypeIdx(2);

impl SemCtx<'_> {
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        self.ir.types.insert(TypeIdx, ty).clone()
    }
    fn push_handler(&mut self, handler: Handler) -> HandlerIdx {
        self.ir.handlers.push(HandlerIdx, handler)
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
            T::Path(id) => scope.try_type(self, id),
            T::Handler(id, fail) => {
                let fail = match fail {
                    ast::FailType::Never => TYPE_NEVER,
                    ast::FailType::None => TYPE_NONE,
                    ast::FailType::Some(ty) => {
                        self.analyze_type(scope, ty, generics.as_deref_mut(), generic_handler)
                    }
                };

                let effect = match scope.try_effect(self, id) {
                    Some(effect) => effect,
                    None => return TYPE_UNKNOWN,
                };

                match generics.filter(|_| generic_handler) {
                    Some(generics) => {
                        let idx = generics.handler.push(GenericIdx, effect);
                        let handler = GenericVal::Generic(idx);
                        self.insert_type(Type::Handler {
                            effect,
                            fail,
                            handler,
                        })
                    }
                    None => self.insert_type(Type::HandlerHint { effect, fail }),
                }
            }
            T::Generic(id) => {
                let name = &self.ast.idents[id];
                match scope.get_type(self, &name.0) {
                    Some(ty) => ty,
                    None => match generics {
                        Some(generics) => {
                            let idx = generics.ty.push(GenericIdx, ());
                            let ty = self.insert_type(Type::Generic(idx));
                            scope.top().types.insert(name.0.clone(), ty);
                            ty
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
                let fail = match fail {
                    ast::FailType::Never => TYPE_NEVER,
                    ast::FailType::None => TYPE_NONE,
                    ast::FailType::Some(ty) => {
                        self.analyze_type(scope, ty, generics.as_deref_mut(), generic_handler)
                    }
                };

                let name = &self.ast.idents[id];
                let effect = match scope.get_effect(self, &name.0) {
                    Some(effect) => effect,
                    None => match generics.as_deref_mut() {
                        Some(generics) => {
                            let idx = generics.effect.push(GenericIdx, ());
                            let effect = GenericVal::Generic(idx);
                            scope.top().effects.insert(name.0.clone(), effect);
                            effect
                        }
                        None => {
                            // TODO: custom error
                            self.errors.push(name.with(Error::UnknownEffect));
                            return TYPE_UNKNOWN;
                        }
                    },
                };

                match generics.filter(|_| generic_handler) {
                    Some(generics) => {
                        let idx = generics.handler.push(GenericIdx, effect);
                        let handler = GenericVal::Generic(idx);
                        self.insert_type(Type::Handler {
                            effect,
                            fail,
                            handler,
                        })
                    }
                    None => self.insert_type(Type::HandlerHint { effect, fail }),
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
                let inner = self.analyze_type(scope, ty, generics, generic_handler);
                self.insert_type(Type::ConstArray(GenericVal::Literal(size), inner))
            }
            T::Slice(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler);
                self.insert_type(Type::Slice(inner))
            }
        }
    }
    fn analyze_sign(
        &mut self,
        scope: &mut ScopeStack,
        fun: &ast::FunSign,
        parent: Option<EffIdx>,
    ) -> FunSign {
        scope.child(|scope| {
            let mut generics = Generics::default();
            let mut params = Vec::new();

            // base params
            for param in fun.inputs.values() {
                let ty = self.analyze_type(scope, param.ty, Some(&mut generics), true);
                params.push(ty);
            }

            // bound handlers
            for &effect in fun.effects.iter() {
                let Some(effect) = (match effect.package {
                    Some(id) => scope.try_package_effect(self, id, effect.effect),
                    None => scope.try_effect(self, effect.effect),
                }) else {
                    continue;
                };

                let idx = generics.handler.push(GenericIdx, effect);
                params.push(self.insert_type(Type::BoundHandler {
                    effect,
                    handler: GenericVal::Generic(idx),
                }));
            }

            // parent handler
            if let Some(i) = parent {
                let effect = GenericVal::Literal(i);
                let idx = generics.handler.push(GenericIdx, effect);
                let handler = GenericVal::Generic(idx);
                let ty = self.insert_type(Type::BoundHandler { effect, handler });
                params.push(ty);
            }

            // return type
            let return_type = match fun.output {
                Some(ty) => self.analyze_type(scope, ty, Some(&mut generics), false),
                None => TYPE_NONE,
            };

            FunSign {
                generics,
                params,
                return_type,
            }
        })
    }
}

pub fn analyze(ast: &AST, errors: &mut Errors, target: &Target) -> SemIR {
    let mut ctx = SemCtx {
        ir: SemIR {
            effects: VecMap::filled(ast.effects.len(), Effect::default()),
            fun_sign: VecMap::filled(ast.functions.len(), FunSign::default()),
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
        for &implied in package.implied.iter() {
            let effect = match &ast.exprs[implied].0 {
                Expression::Handler(ast::Handler::Full { effect, .. }) => effect,
                _ => panic!(),
            };
            let name = &ast.idents[effect.effect].0;
            if let Some(effect) = ctx.packages[idx].effects.get(name).copied() {
                // ctx.packages[idx].implied.insert(effect);
            } else {
                // TODO: error
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
            // add functions to scope
            let mut funs = VecMap::new();
            for (fi, decl) in effect.functions.iter(EffFunIdx) {
                let sign = ctx.analyze_sign(&mut scope, &decl.sign, Some(i));
                funs.push_value(sign);

                let name = ast.idents[decl.name].0.clone();
                ctx.packages[idx].funs.insert(name, FunIdent::Effect(i, fi));
            }
            ctx.ir.effects[i] = Effect { funs };
        }

        for (i, fun) in package
            .functions
            .iter()
            .copied()
            .map(|i| (i, &ast.functions[i]))
        {
            // add function to scope
            let sign = ctx.analyze_sign(&mut scope, &fun.decl.sign, None);
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

    ctx.ir
}
