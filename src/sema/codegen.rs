use std::{collections::HashMap, rc::Rc};

use either::Either;

use crate::{
    ast::{
        self, Ast, AttributeValue, BinOp, EffFunIdx, EffIdx, ExprIdx, Expression, Ident,
        PackageIdx, ParamIdx, UnOp,
    },
    error::{get_lines, Error, Errors, FileIdx, Range, Ranged},
    sema::{HandlerIdent, Instruction},
    vecmap::{VecMap, VecSet},
    Target,
};

use super::{
    get_param, Block, BlockIdx, Capability, Effect, EffectIdent, FmtType, Foreign, FunIdent,
    FunIdx, FunImpl, FunSign, Generic, GenericIdx, GenericParams, GenericVal, Generics, Handler,
    HandlerIdx, HandlerType, InstrIdx, IntSize, Lazy, LazyIdx, LazyValue, Param, ReturnType, SemIR,
    Struct, Type, TypeIdx, Value,
};

impl FunIdent {
    fn ident(self, ctx: &SemCtx) -> Ident {
        match self {
            FunIdent::Top(idx) => ctx.ast.functions[idx].decl.name,
            FunIdent::Effect(eff, idx) => ctx.ast.effects[eff].functions[idx].name,
        }
    }
}

struct SemCtx<'a> {
    ir: SemIR,
    ast: &'a Ast,
    errors: &'a mut Errors,
    packages: VecMap<PackageIdx, Scope>,
    srcloc: HandlerIdx,
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

    effect_stack: Vec<(TypeIdx, GenericVal<EffectIdent>, Value, Option<BlockIdx>)>,
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
                TYPE_ERROR
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
            return TYPE_ERROR;
        };
        let name = &ctx.ast.idents[id];
        match ctx.packages[package].types.get(&name.0).copied() {
            Some(eff) => eff,
            None => {
                ctx.errors
                    .push(name.with(Error::UnknownPackageType(ctx.ast.idents[pkg].empty())));
                TYPE_ERROR
            }
        }
    }
    fn try_package_fun(&self, ctx: &mut SemCtx, pkg: Ident, id: Ident) -> Option<FunIdent> {
        let Some(package) = self.try_package(ctx, pkg) else {
            return None;
        };
        let name = &ctx.ast.idents[id];
        match ctx.packages[package].funs.get(&name.0).copied() {
            Some(fun) => Some(fun),
            None => {
                ctx.errors
                    .push(name.with(Error::UnknownPackageFunction(ctx.ast.idents[pkg].empty())));
                None
            }
        }
    }
}

const TYPE_ERROR: TypeIdx = TypeIdx(0);
const TYPE_NONE: TypeIdx = TypeIdx(1);
const TYPE_NEVER: TypeIdx = TypeIdx(2);
const TYPE_DATATYPE: TypeIdx = TypeIdx(3);
const TYPE_EFFECT: TypeIdx = TypeIdx(4);
const TYPE_USIZE: TypeIdx = TypeIdx(5);
const TYPE_BOOL: TypeIdx = TypeIdx(6);
const TYPE_INT: TypeIdx = TypeIdx(7);
const TYPE_STR: TypeIdx = TypeIdx(8);
const TYPE_CHAR: TypeIdx = TypeIdx(9);
const TYPE_U8: TypeIdx = TypeIdx(10);
const TYPE_UPTR: TypeIdx = TypeIdx(11);

impl SemCtx<'_> {
    fn get_preamble_effect(&self, name: &str) -> EffIdx {
        *self.packages[self.ast.preamble]
            .effects
            .get(name)
            .expect("missing preamble function")
            .literal()
            .unwrap()
    }
    fn get_preamble_handler(&mut self, name: &str) -> &mut Handler {
        let idx = self.get_preamble_effect(name);
        let handler = *self.ir.effects[idx]
            .implied
            .get(0)
            .expect("missing preamble implied");
        &mut self.ir.handlers[handler]
    }
    fn get_preamble_sign(&self, name: &str) -> &FunSign {
        match *self.packages[self.ast.preamble]
            .funs
            .get(name)
            .expect("missing preamble function")
        {
            FunIdent::Top(idx) => &self.ir.fun_sign[idx],
            FunIdent::Effect(eff, idx) => {
                let handler = *self.ir.effects[eff]
                    .implied
                    .get(0)
                    .expect("missing preamble implied");
                &self.ir.handlers[handler].funs[idx].0
            }
        }
    }
    fn get_preamble_fun(&mut self, name: &str) -> &mut FunImpl {
        match *self.packages[self.ast.preamble]
            .funs
            .get(name)
            .expect("missing preamble function")
        {
            FunIdent::Top(idx) => &mut self.ir.fun_impl[idx],
            FunIdent::Effect(eff, idx) => {
                let handler = *self.ir.effects[eff]
                    .implied
                    .get(0)
                    .expect("missing preamble implied");
                &mut self.ir.handlers[handler].funs[idx].1
            }
        }
    }
    fn define_preamble_fun(&mut self, name: &str, f: impl FnOnce(&mut Self, &mut FunCtx)) {
        let mut fun_ctx = FunCtx {
            scope: &mut ScopeStack::new(self.ast.preamble),
            yeetable: None,
            yeetable_def: None,
            yeetable_ret: None,
            blocks: vec![Block::default()].into(),
            block: BlockIdx(0),
            capture_boundary: (true, 0),
            captures: &mut Vec::new(),
        };
        f(self, &mut fun_ctx);
        self.get_preamble_fun(name).blocks = fun_ctx.blocks;
    }
    fn params_from_generics(&mut self, generics: &[Generic]) -> GenericParams {
        generics
            .iter()
            .map(|&g| (g.idx, self.insert_type(Type::Generic(g))))
            .collect()
    }
    fn lazy_handler(
        &mut self,
        _: &mut Generics,
        typeof_handler: TypeIdx,
        _: ast::TypeIdx,
    ) -> TypeIdx {
        let idx = self.ir.lazy_handlers.push(LazyIdx, LazyValue::None);
        self.insert_type(Type::Handler(Lazy {
            idx,
            typeof_handler,
        }))
    }
    fn no_handler(&mut self, _: &mut Generics, _: TypeIdx, ty: ast::TypeIdx) -> TypeIdx {
        self.errors
            .push(self.ast.types[ty].with(Error::NotEnoughInfo));
        TYPE_ERROR
    }
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        *self.ir.types.insert(TypeIdx, ty)
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
            ast::FailType::Some(ty) => {
                self.analyze_type(scope, ty, generics, generic_handler, handler_output)
            }
        }
    }
    fn translate_generics(
        &mut self,
        ty: TypeIdx,
        generic_params: &GenericParams,
        translate_lazy: bool,
    ) -> Option<TypeIdx> {
        Some(match self.ir.types[ty] {
            Type::Handler(lazy) => {
                let typeof_handler =
                    self.translate_generics(lazy.typeof_handler, generic_params, translate_lazy)?;

                if translate_lazy {
                    let idx = self.ir.lazy_handlers.push(
                        LazyIdx,
                        LazyValue::Refer(lazy.idx, Some(generic_params.clone())),
                    );
                    self.insert_type(Type::Handler(Lazy {
                        idx,
                        typeof_handler,
                    }))
                } else {
                    let idx = self.ir.lazy_handlers.push(LazyIdx, LazyValue::None);
                    self.insert_type(Type::Handler(Lazy {
                        idx,
                        typeof_handler,
                    }))
                }
            }
            Type::Effect(ref ident) => {
                let ie = ident.effect;

                let params = ident.generic_params.clone();
                let params = params
                    .into_iter()
                    .map(|(idx, ty)| {
                        Some((
                            idx,
                            self.translate_generics(ty, generic_params, translate_lazy)?,
                        ))
                    })
                    .collect::<Option<Vec<_>>>()?;

                self.insert_type(Type::Effect(EffectIdent {
                    effect: ie,
                    generic_params: params,
                }))
            }
            Type::HandlerType(ref effect_type) => {
                let eft = effect_type.fail_type;

                let effect = match effect_type.effect {
                    GenericVal::Literal(ref ident) => {
                        let ie = ident.effect;

                        let params = ident.generic_params.clone();
                        let params = params
                            .into_iter()
                            .map(|(idx, ty)| {
                                Some((
                                    idx,
                                    self.translate_generics(ty, generic_params, translate_lazy)?,
                                ))
                            })
                            .collect::<Option<Vec<_>>>()?;
                        GenericVal::Literal(EffectIdent {
                            effect: ie,
                            generic_params: params,
                        })
                    }
                    GenericVal::Generic(idx) => match get_param(generic_params, idx) {
                        Some(ty) => match self.ir.types[ty] {
                            Type::Effect(ref ident) => GenericVal::Literal(ident.clone()),
                            Type::Generic(generic) => GenericVal::Generic(generic.idx),
                            _ => unreachable!(),
                        },
                        None => None?,
                    },
                };
                let fail_type = self.translate_generics(eft, generic_params, translate_lazy)?;
                self.insert_type(Type::HandlerType(HandlerType { effect, fail_type }))
            }
            Type::Generic(generic) => match get_param(generic_params, generic.idx) {
                Some(genty) => genty,
                None => None?,
            },
            Type::Pointer(isconst, inner) => {
                let inner = self.translate_generics(inner, generic_params, translate_lazy)?;
                self.insert_type(Type::Pointer(isconst, inner))
            }
            Type::MaybePointer(isconst, inner) => {
                let inner = self.translate_generics(inner, generic_params, translate_lazy)?;
                self.insert_type(Type::MaybePointer(isconst, inner))
            }
            Type::ConstArray(size, inner) => {
                let size = match size {
                    GenericVal::Literal(_) => size,
                    GenericVal::Generic(idx) => match get_param(generic_params, idx) {
                        Some(ty) => match self.ir.types[ty] {
                            Type::Generic(generic) => GenericVal::Generic(generic.idx),
                            Type::CompileTime(Value::ConstantInt(TYPE_USIZE, false, size)) => {
                                GenericVal::Literal(size)
                            }
                            _ => unreachable!(),
                        },
                        None => None?,
                    },
                };
                let inner = self.translate_generics(inner, generic_params, translate_lazy)?;
                self.insert_type(Type::ConstArray(size, inner))
            }
            Type::Slice(isconst, inner) => {
                let inner = self.translate_generics(inner, generic_params, translate_lazy)?;
                self.insert_type(Type::Slice(isconst, inner))
            }

            Type::EffectType
            | Type::DataType
            | Type::Struct(_)
            | Type::Integer(_, _)
            | Type::CompileTime(_)
            | Type::Str
            | Type::Char
            | Type::Bool
            | Type::None
            | Type::Error
            | Type::Never => ty,
        })
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
                self.check_move(
                    generic.typeof_ty,
                    typeof_generic,
                    TypeRange {
                        loc: name.empty(),
                        def: None,
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
            T::Error => TYPE_ERROR,
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
                let fail_type = self.analyze_fail(
                    scope,
                    fail,
                    generics.as_deref_mut(),
                    generic_handler,
                    handler_output,
                );
                let effect = match self.analyze_effect(scope, &id.ident) {
                    Some(effect) => effect,
                    None => return TYPE_ERROR,
                }
                .0;

                // create handler type
                let typeof_handler = self.insert_type(Type::HandlerType(HandlerType {
                    effect: effect.map(|&effect| EffectIdent {
                        effect,
                        // TODO: error on length mismatch
                        generic_params: self.ir.effects[effect]
                            .generics
                            .iter()
                            .map(|g| g.idx)
                            .zip(params)
                            .collect(),
                    }),
                    fail_type,
                }));

                match generics.as_deref_mut().filter(|_| generic_handler) {
                    Some(generics) => {
                        let len = self.ir.generic_names.len();
                        let idx = self.ir.generic_names.push(GenericIdx, format!("`_{}", len));

                        let value = Generic {
                            idx,
                            typeof_ty: typeof_handler,
                        };
                        generics.push(value);

                        let lazy = self
                            .ir
                            .lazy_handlers
                            .push(LazyIdx, LazyValue::Some(GenericVal::Generic(value.idx)));
                        self.insert_type(Type::Handler(Lazy {
                            idx: lazy,
                            typeof_handler,
                        }))
                    }
                    None => handler_output(
                        self,
                        generics.unwrap_or(&mut Vec::new()),
                        typeof_handler,
                        ty,
                    ),
                }
            }
            T::Generic(id) => match self.analyze_generic(scope, id, TYPE_DATATYPE, generics) {
                Some(generic) => self.insert_type(Type::Generic(generic)),
                None => TYPE_ERROR,
            },
            T::GenericHandler(id, fail) => {
                let fail_type = self.analyze_fail(
                    scope,
                    fail,
                    generics.as_deref_mut(),
                    generic_handler,
                    handler_output,
                );

                let effect =
                    match self.analyze_generic(scope, id, TYPE_EFFECT, generics.as_deref_mut()) {
                        Some(generic) => GenericVal::Generic(generic.idx),
                        None => return TYPE_ERROR,
                    };

                // create handler type
                let typeof_handler =
                    self.insert_type(Type::HandlerType(HandlerType { effect, fail_type }));
                match generics.as_deref_mut().filter(|_| generic_handler) {
                    Some(generics) => {
                        let len = self.ir.generic_names.len();
                        let idx = self.ir.generic_names.push(GenericIdx, format!("`_{}", len));

                        let value = Generic {
                            idx,
                            typeof_ty: typeof_handler,
                        };
                        generics.push(value);

                        let lazy = self
                            .ir
                            .lazy_handlers
                            .push(LazyIdx, LazyValue::Some(GenericVal::Generic(value.idx)));
                        self.insert_type(Type::Handler(Lazy {
                            idx: lazy,
                            typeof_handler,
                        }))
                    }
                    None => handler_output(
                        self,
                        generics.unwrap_or(&mut Vec::new()),
                        typeof_handler,
                        ty,
                    ),
                }
            }
            T::Maybe(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                match self.ir.types[inner] {
                    Type::Pointer(isconst, inner) => {
                        self.insert_type(Type::MaybePointer(isconst, inner))
                    }
                    _ => todo!(),
                }
            }
            T::Pointer(isconst, ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Pointer(isconst, inner))
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
                            None => return TYPE_ERROR,
                        }
                    }
                    _ => todo!(),
                };
                self.insert_type(Type::ConstArray(size, inner))
            }
            T::Slice(isconst, ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Slice(isconst, inner))
            }
        }
    }
    fn analyze_effect(
        &mut self,
        scope: &mut ScopeStack,
        effect: &ast::PackagedIdent,
    ) -> Option<Ranged<GenericVal<EffIdx>>> {
        let def = self.ast.idents[effect.ident].empty();
        match effect.package {
            Some(id) => scope
                .try_package_effect(self, id, effect.ident)
                .map(|t| def.with(t)),
            None => scope.try_effect(self, effect.ident).map(|t| def.with(t)),
        }
    }
    fn analyze_decl(&mut self, decl: &ast::FunDecl, sign: &FunSign, fun: FunIdent) {
        // check if capability
        for attr in decl
            .attributes
            .iter()
            .filter(|a| self.ast.idents[a.name].0.eq("capability"))
        {
            let os = attr
                .settings
                .iter()
                .find(|&&(i, _)| self.ast.idents[i].0.eq("os"))
                .map(|o| match &o.1 {
                    AttributeValue::String(s) => s.0.clone(),
                    AttributeValue::Type(_) => todo!("give error"),
                });

            let arch = attr
                .settings
                .iter()
                .find(|&&(i, _)| self.ast.idents[i].0.eq("arch"))
                .map(|o| match &o.1 {
                    AttributeValue::String(s) => s.0.clone(),
                    AttributeValue::Type(_) => todo!("give error"),
                });

            if !sign.params.is_empty() {
                todo!("give error");
            }

            match self.ir.types[sign.return_type.ty] {
                Type::Handler(lazy) => match &self.ir.types[lazy.typeof_handler] {
                    Type::HandlerType(ty) => {
                        if ty.fail_type != TYPE_NEVER {
                            todo!("give error");
                        }
                        match &ty.effect {
                            GenericVal::Literal(effect) => self.ir.effects[effect.effect]
                                .capabilities
                                .push(Capability {
                                    fun,
                                    generic_params: effect.generic_params.clone(),
                                    os,
                                    arch,
                                }),
                            GenericVal::Generic(_) => todo!("give error"),
                        }
                    }
                    Type::Error => {}
                    _ => todo!("give error"),
                },
                Type::Error => {}
                _ => todo!("give error"),
            }
        }
    }
    fn analyze_sign(
        &mut self,
        scope: &mut ScopeStack,
        name: Ident,
        effect: Option<(EffectIdent, Option<EffFunIdx>)>,
        fun: &ast::FunSign,
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
                    let generic = self
                        .analyze_generic(scope, param.name, ty, Some(&mut generics))
                        .unwrap();
                    params.push_value(Param {
                        name_def: self.ast.idents[param.name].empty(),
                        name: self.ast.idents[param.name].0.clone(),
                        type_def: self.ast.types[param.ty].empty(),
                        ty,
                        mutable: param.mutable,
                        const_generic: Some(generic.idx),
                    });
                } else {
                    params.push_value(Param {
                        name_def: self.ast.idents[param.name].empty(),
                        name: self.ast.idents[param.name].0.clone(),
                        type_def: self.ast.types[param.ty].empty(),
                        ty,
                        mutable: param.mutable,
                        const_generic: None,
                    });
                }
            }

            // return type
            let return_type = match fun.output {
                Some(ty) => self.analyze_type(
                    scope,
                    ty,
                    Some(&mut generics),
                    false,
                    &mut Self::lazy_handler,
                ),
                None => TYPE_NONE,
            };

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
                if let Some(effect) = self.analyze_effect(scope, &id.ident) {
                    let len = self.ir.generic_names.len();
                    let idx = self.ir.generic_names.push(GenericIdx, format!("`_{}", len));

                    let value = Generic {
                        idx,
                        typeof_ty: TYPE_DATATYPE,
                    };
                    generics.push(value);
                    let ty = self.insert_type(Type::Generic(value));

                    handler_params.push(effect.map(|effect| {
                        (
                            ty,
                            match effect {
                                GenericVal::Literal(effect) => {
                                    // TODO: check parameter count
                                    GenericVal::Literal(EffectIdent {
                                        effect,
                                        generic_params: self.ir.effects[effect]
                                            .generics
                                            .iter()
                                            .map(|generic| generic.idx)
                                            .zip(effect_params)
                                            .collect(),
                                    })
                                }
                                GenericVal::Generic(idx) => {
                                    // TODO: params must be empty
                                    GenericVal::Generic(idx)
                                }
                            },
                        )
                    }))
                }
            }

            // parent handler
            if let Some((effect, fun)) = effect {
                let len = self.ir.generic_names.len();
                let idx = self.ir.generic_names.push(GenericIdx, format!("`_{}", len));

                let value = Generic {
                    idx,
                    typeof_ty: TYPE_DATATYPE,
                };
                generics.push(value);
                let ty = self.insert_type(Type::Generic(value));

                let def = self.ast.idents[self.ast.effects[effect.effect].name].empty();
                handler_params.push(def.with((ty, GenericVal::Literal(effect))));

                if let Some(fun) = fun {
                    if let Type::Handler(lazy) = self.ir.types[return_type] {
                        let generic_idx = self
                            .ir
                            .lazy_handlers
                            .push(LazyIdx, LazyValue::Some(GenericVal::Generic(idx)));
                        let ps = self.params_from_generics(&generics);
                        self.ir.lazy_handlers[lazy.idx] =
                            LazyValue::EffectFunOutput(generic_idx, fun, ps);
                    }
                }
            }

            FunSign {
                def: Some(name.empty()),
                name: name.0.clone(),
                generics,
                params,
                effect_stack: handler_params,
                return_type: ReturnType {
                    type_def: fun.output.map(|ty| self.ast.types[ty].empty()),
                    ty: return_type,
                },
            }
        })
    }
    fn check_sign(&mut self, a: FunSign, b: FunIdent, gparams: &GenericParams) -> FunSign {
        let b = match b {
            FunIdent::Top(idx) => &self.ir.fun_sign[idx],
            FunIdent::Effect(eff, idx) => &self.ir.effects[eff].funs[idx],
        };

        let generics = b.generics.clone();
        let params = b.params.clone();
        let return_type = b.return_type.ty;
        let effect_stack = b.effect_stack.clone();

        if a.params.len() != b.params.len() {
            self.errors
                .push(b.def.unwrap().with(Error::ParameterMismatch(
                    Some(a.def.unwrap()),
                    a.params.len(),
                    b.params.len(),
                )));
            return a;
        }

        let mut generic_params = self.params_from_generics(&generics);
        generic_params.extend(gparams.iter().cloned());

        let generics = generics
            .into_iter()
            .map(|g| Generic {
                idx: g.idx,
                typeof_ty: self
                    .translate_generics(g.typeof_ty, &generic_params, true)
                    .unwrap(),
            })
            .collect();
        let params = a
            .params
            .iter(ParamIdx)
            .map(|(idx, param)| {
                let effect_param = &params[idx];
                let translated = self
                    .translate_generics(effect_param.ty, &generic_params, true)
                    .unwrap();
                self.check_move(
                    translated,
                    param.ty,
                    TypeRange {
                        loc: params[idx].type_def,
                        def: Some(param.type_def),
                    },
                );

                Param {
                    ty: translated,
                    mutable: effect_param.mutable,
                    const_generic: effect_param.const_generic,
                    ..param.clone()
                }
            })
            .collect();
        let return_type = self
            .translate_generics(return_type, &generic_params, false)
            .unwrap();
        let effect_stack = effect_stack
            .into_iter()
            .map(|e| {
                e.map(|e| {
                    let ty = self.translate_generics(e.0, &generic_params, true).unwrap();
                    let id = match e.1 {
                        GenericVal::Literal(id) => id,
                        GenericVal::Generic(idx) => {
                            match &self.ir.types[get_param(&generic_params, idx).unwrap()] {
                                Type::Effect(id) => id.clone(),
                                _ => unreachable!(),
                            }
                        }
                    };
                    let eff = id.effect;
                    let eff_params = id
                        .generic_params
                        .into_iter()
                        .map(|(idx, ty)| {
                            (
                                idx,
                                self.translate_generics(ty, &generic_params, true).unwrap(),
                            )
                        })
                        .collect();
                    (
                        ty,
                        GenericVal::Literal(EffectIdent {
                            effect: eff,
                            generic_params: eff_params,
                        }),
                    )
                })
            })
            .collect();

        // FIXME: check generics
        // FIXME: check effect_stack
        // FIXME: check output

        FunSign {
            def: a.def,
            name: a.name,
            generics,
            params,
            effect_stack,
            return_type: ReturnType {
                type_def: a.return_type.type_def,
                ty: return_type,
            },
        }
    }
    fn analyze_implied(&mut self, scope: &mut ScopeStack, implied: &ast::Handler) {
        scope.child(|scope| {
            let mut generics = Generics::default();

            let (id, fail, functions, moved) = match *implied {
                ast::Handler::Full {
                    ref effect,
                    fail_type,
                    ref functions,
                    moved,
                } => (effect, fail_type, functions, moved),
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
            let effect = self
                .analyze_effect(scope, &id.ident)?
                .0
                .literal()
                .copied()?;

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
                    Some((
                        EffectIdent {
                            effect,
                            generic_params: generic_params.clone(),
                        },
                        None,
                    )),
                    &function.decl.sign,
                );

                match matching {
                    Some((idx, _)) => {
                        // translate sign
                        let sign =
                            self.check_sign(sign, FunIdent::Effect(effect, idx), &generic_params);

                        // analyze function
                        let imp = self.generate_function(
                            Either::Right(&sign),
                            function.body,
                            scope,
                            Some(fail),
                            None,
                            &mut Vec::new(),
                            moved,
                        );

                        funs[idx] = (sign, imp)
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
            for (idx, (sign, _)) in funs.iter(EffFunIdx) {
                let name = self.ast.idents[self.ast.effects[effect].functions[idx].name].empty();

                // check if missing
                if sign.def.is_none() {
                    missing.push(name);
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

                captures: Vec::new(),
                funs,
            });
            self.ir.effects[effect].implied.push(handler);

            Some(())
        });
    }
    fn supertype(&mut self, a: TypeIdx, b: TypeIdx, loc: TypeRange) -> TypeIdx {
        match self.test_supertype(a, b) {
            Some(c) => c,
            None => {
                self.errors.push(loc.loc.with(Error::TypeMismatch(
                    loc.def,
                    format!("{}", FmtType(&self.ir, a)),
                    format!("{}", FmtType(&self.ir, b)),
                )));
                TYPE_ERROR
            }
        }
    }
    fn test_supertype(&mut self, a: TypeIdx, b: TypeIdx) -> Option<TypeIdx> {
        if self.test_move(a, b) {
            Some(b)
        } else if self.test_move(b, a) {
            Some(a)
        } else {
            None
        }
    }
    fn infer_generics(&mut self, params: &mut GenericParams, from: TypeIdx, to: TypeIdx) {
        if from == to {
            return;
        }
        let infer_generic = move |params: &mut GenericParams, idx: GenericIdx, val: TypeIdx| {
            if get_param(params, idx).is_none() {
                params.push((idx, val));
            }
        };
        match (&self.ir.types[from], &self.ir.types[to]) {
            (_, Type::Generic(generic)) => {
                infer_generic(params, generic.idx, from);
            }
            (Type::Handler(inner), Type::Handler(to)) => {
                if let LazyValue::Some(GenericVal::Generic(idx)) = self.ir.lazy_handlers[to.idx] {
                    infer_generic(params, idx, from);
                }
                self.infer_generics(params, inner.typeof_handler, to.typeof_handler);
            }
            (Type::HandlerType(from), Type::HandlerType(to)) => {
                let from_fail = from.fail_type;
                let to_fail = to.fail_type;
                match (&from.effect, &to.effect) {
                    (GenericVal::Literal(effect), &GenericVal::Generic(idx)) => {
                        let val = self.insert_type(Type::Effect(effect.clone()));
                        infer_generic(params, idx, val);
                    }
                    (GenericVal::Literal(from), GenericVal::Literal(to))
                        if from.effect == to.effect =>
                    {
                        for (from, to) in from
                            .generic_params
                            .iter()
                            .map(|&(_, ty)| ty)
                            .zip(to.generic_params.iter().map(|&(_, ty)| ty))
                            .collect::<Vec<_>>()
                        {
                            self.infer_generics(params, from, to);
                        }
                    }
                    (&GenericVal::Generic(from), &GenericVal::Generic(to)) => {
                        let val = self.insert_type(Type::Generic(Generic {
                            idx: from,
                            typeof_ty: TYPE_EFFECT,
                        }));
                        infer_generic(params, to, val);
                    }
                    _ => {}
                }
                self.infer_generics(params, from_fail, to_fail);
            }
            (Type::Effect(from), Type::Effect(to)) if from.effect == to.effect => {
                for (from, to) in from
                    .generic_params
                    .iter()
                    .map(|&(_, ty)| ty)
                    .zip(to.generic_params.iter().map(|&(_, ty)| ty))
                    .collect::<Vec<_>>()
                {
                    self.infer_generics(params, from, to);
                }
            }
            (
                &Type::Pointer(_, from) | &Type::MaybePointer(_, from),
                &Type::Pointer(_, to) | &Type::MaybePointer(_, to),
            ) => {
                self.infer_generics(params, from, to);
            }
            (&Type::Slice(_, from), &Type::Slice(_, to)) => {
                self.infer_generics(params, from, to);
            }
            (&Type::ConstArray(sfrom, from), &Type::ConstArray(sto, to)) => {
                match (sfrom, sto) {
                    (GenericVal::Literal(size), GenericVal::Generic(idx)) => {
                        let val = self.insert_type(Type::CompileTime(Value::ConstantInt(
                            TYPE_USIZE, false, size,
                        )));
                        infer_generic(params, idx, val);
                    }
                    (GenericVal::Generic(from), GenericVal::Generic(to)) => {
                        let val = self.insert_type(Type::Generic(Generic {
                            idx: from,
                            typeof_ty: TYPE_USIZE,
                        }));
                        infer_generic(params, to, val);
                    }
                    _ => {}
                }
                self.infer_generics(params, from, to);
            }
            _ => {}
        }
    }
    fn check_move(&mut self, a: TypeIdx, b: TypeIdx, loc: TypeRange) {
        if !self.test_move(a, b) {
            self.errors.push(loc.loc.with(Error::TypeMismatch(
                loc.def,
                format!("{}", FmtType(&self.ir, b)),
                format!("{}", FmtType(&self.ir, a)),
            )));
        }
    }
    fn test_move(&mut self, from: TypeIdx, to: TypeIdx) -> bool {
        if from == to {
            return true;
        }
        match (&self.ir.types[from], &self.ir.types[to]) {
            (Type::Never, _) => true,

            (Type::Error, _) => true,
            (_, Type::Error) => true,

            (&Type::Pointer(a, from), &Type::Pointer(b, to) | &Type::MaybePointer(b, to)) => {
                a <= b && self.test_move(from, to)
            }
            (&Type::MaybePointer(a, from), &Type::MaybePointer(b, to)) => {
                a <= b && self.test_move(from, to)
            }
            (&Type::Slice(a, from), &Type::Slice(b, to)) => a <= b && self.test_move(from, to),

            (Type::HandlerType(from), Type::HandlerType(to)) => {
                from.effect == to.effect && self.test_move(from.fail_type, to.fail_type)
            }

            (&Type::Handler(from), &Type::Handler(to)) => {
                if self.test_move(from.typeof_handler, to.typeof_handler) {
                    if let value @ LazyValue::None = &mut self.ir.lazy_handlers[from.idx] {
                        *value = LazyValue::Refer(to.idx, None);
                        true
                    } else if let value @ LazyValue::None = &mut self.ir.lazy_handlers[to.idx] {
                        *value = LazyValue::Refer(from.idx, None);
                        true
                    } else {
                        false
                    }
                } else {
                    // incorrect meta-type
                    false
                }
            }

            _ => false,
        }
    }
    fn generate_function(
        &mut self,
        sign: Either<FunIdx, &FunSign>,
        body: ExprIdx,
        scope: &mut ScopeStack,
        yeetable: Option<TypeIdx>,
        yeetable_def: Option<Range>,
        captures: &mut Vec<Either<String, GenericVal<EffectIdent>>>,
        moved: bool,
    ) -> FunImpl {
        scope.child(|scope| {
            let ir_sign = match sign {
                Either::Left(idx) => &self.ir.fun_sign[idx],
                Either::Right(sign) => sign,
            };

            let mut taken = ir_sign.effect_stack.len();
            if sign.is_right() {
                taken -= 1;
            }

            scope.top().effect_stack = ir_sign
                .effect_stack
                .iter()
                .enumerate()
                .map(|(i, ident)| {
                    (
                        ident.0 .0,
                        ident.0 .1.clone(),
                        Value::Deref(Box::new(Value::EffectParam(i)), false),
                        None,
                    )
                })
                .take(taken)
                .collect();

            let mut blocks = VecMap::new();
            let block = blocks.push(BlockIdx, Block::default());
            let mut fun_ctx = FunCtx {
                capture_boundary: (moved, scope.scopes.len() - 1),
                captures,

                scope,
                blocks,
                block,
                yeetable,
                yeetable_def,
                yeetable_ret: None,
            };

            for (idx, param) in ir_sign.params.iter(ParamIdx) {
                if param.mutable {
                    let value = fun_ctx
                        .push_deref(false, Instruction::Reference(Value::Param(idx), param.ty));
                    fun_ctx.define(
                        param.name.clone(),
                        Variable {
                            value,
                            ty: param.ty,
                            mutable: true,
                        },
                    );
                } else if let Some(idx) = param.const_generic {
                    fun_ctx.define(
                        param.name.clone(),
                        Variable {
                            value: Value::ConstantGeneric(idx),
                            ty: param.ty,
                            mutable: false,
                        },
                    );
                } else {
                    fun_ctx.define(
                        param.name.clone(),
                        Variable {
                            value: Value::Param(idx),
                            ty: param.ty,
                            mutable: false,
                        },
                    );
                }
            }
            for generic in ir_sign.generics.iter().copied() {
                fun_ctx
                    .scope
                    .top()
                    .generics
                    .insert(self.ir.generic_names[generic.idx].clone(), generic);
            }

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
    // returns the pointer value along with const? from the pointer type
    fn check_expr_address(
        &mut self,
        ctx: &mut FunCtx,
        expr: ExprIdx,
        expected: TypeIdx,
        expected_def: Option<Range>,
    ) -> Option<(Value, bool)> {
        let val = self.check_expr(ctx, expr, expected, expected_def)?;
        match val {
            Value::Deref(val, isconst) => Some((*val, isconst)),
            _ => {
                todo!("give error")
            }
        }
    }
    // returns the pointer value along with const?, inner from the pointer type
    fn synth_expr_address(
        &mut self,
        ctx: &mut FunCtx,
        expr: ExprIdx,
    ) -> Option<(Value, bool, TypeIdx)> {
        let (val, ty) = self.synth_expr(ctx, expr)?;
        match val {
            Value::Deref(val, isconst) => Some((*val, isconst, ty)),
            _ => {
                todo!("give error")
            }
        }
    }
    fn check_expr(
        &mut self,
        ctx: &mut FunCtx,
        expr: ExprIdx,
        expected: TypeIdx,
        expected_def: Option<Range>,
    ) -> Option<Value> {
        let error_loc = TypeRange {
            loc: self.ast.exprs[expr].empty(),
            def: expected_def,
        };

        use Expression as E;
        match (&self.ast.exprs[expr].0, &self.ir.types[expected]) {
            (E::Body(body), _) => ctx.child(|ctx| {
                for expr in body.main.iter().copied() {
                    self.check_expr(ctx, expr, TYPE_NONE, None)?;
                }
                body.last
                    .map(|expr| self.check_expr(ctx, expr, expected, expected_def))
                    .unwrap_or_else(|| {
                        self.check_move(TYPE_NONE, expected, error_loc);
                        Some(Value::ConstantNone)
                    })
            }),
            (&E::IfElseUnwrap(mptr, ref yes, no), _) => {
                let (mptr, mptr_ty) = self.synth_expr(ctx, mptr)?;

                let uptr = ctx.push(Instruction::Cast(mptr.clone(), TYPE_UPTR));
                let cond = ctx.push(Instruction::Equals(uptr, Value::ConstantZero(TYPE_UPTR)));

                if yes.inputs.len() != 1 {
                    panic!("give error");
                }
                let ptr_ty = match self.ir.types[mptr_ty] {
                    Type::MaybePointer(isconst, inner) => {
                        self.insert_type(Type::Pointer(isconst, inner))
                    }
                    _ => panic!("give error"),
                };

                ctx.branch(
                    self,
                    cond,
                    |me, ctx| match no {
                        Some(no) => me
                            .check_expr(ctx, no, expected, expected_def)
                            .map(|val| (val, expected, expected_def)),
                        None => Some((Value::ConstantNone, TYPE_NONE, None)),
                    },
                    |me, ctx| {
                        let ident = yes.inputs.values().copied().next().unwrap();
                        let ident = self.ast.idents[ident].0.clone();
                        ctx.define(
                            ident,
                            Variable {
                                value: mptr,
                                ty: ptr_ty,
                                mutable: false,
                            },
                        );
                        me.check_expr(ctx, yes.body, expected, expected_def)
                            .map(|val| (val, expected, expected_def))
                    },
                )
                .map(|(val, _)| val)
            }
            (&E::IfElse(cond, yes, no), _) => {
                let cond = self.check_expr(ctx, cond, TYPE_BOOL, None)?;
                ctx.branch(
                    self,
                    cond,
                    |me, ctx| {
                        me.check_expr(ctx, yes, expected, expected_def)
                            .map(|val| (val, expected, None))
                    },
                    |me, ctx| match no {
                        Some(no) => me
                            .check_expr(ctx, no, expected, expected_def)
                            .map(|val| (val, expected, None)),
                        None => {
                            me.check_move(TYPE_NONE, expected, error_loc);
                            Some((Value::ConstantNone, expected, None))
                        }
                    },
                )
                .map(|(val, _)| val)
            }
            (E::Array(exprs), &Type::Slice(_, elem)) => {
                let elems = exprs
                    .iter()
                    .copied()
                    .map(|expr| self.check_expr(ctx, expr, elem, expected_def))
                    .collect::<Option<Rc<[_]>>>()?;
                let len = elems.len() as u64;

                let arr_ty = self.insert_type(Type::ConstArray(GenericVal::Literal(len), elem));
                let arr = Value::ConstantAggregate(arr_ty, elems);
                let ptr = ctx.push(Instruction::Reference(arr, arr_ty));
                let slice = Value::ConstantAggregate(
                    expected,
                    vec![ptr, Value::ConstantInt(TYPE_USIZE, false, len)].into(),
                );
                Some(slice)
            }
            (E::Array(exprs), &Type::ConstArray(GenericVal::Literal(n), elem))
                if n == exprs.len() as u64 =>
            {
                let elems = exprs
                    .iter()
                    .copied()
                    .map(|expr| self.check_expr(ctx, expr, elem, expected_def))
                    .collect::<Option<Rc<[_]>>>()?;
                Some(Value::ConstantAggregate(expected, elems))
            }
            (E::Uninit, _) => {
                // TODO: test if allowed
                Some(Value::ConstantUninit(expected))
            }
            (E::Int(0), _) => {
                // TODO: test if allowed
                Some(Value::ConstantZero(expected))
            }
            (&E::Int(n), &Type::Integer(_signed, _size)) => {
                // TODO: test if fits
                Some(Value::ConstantInt(expected, false, n))
            }
            (E::Character(str), &Type::Integer(_signed, _size)) => {
                // TODO: test if fits, test if single char
                let c = str.chars().next().unwrap();
                let c = u64::from(c);
                Some(Value::ConstantInt(expected, false, c))
            }
            (E::String(str), &Type::Slice(_, elem)) if elem == TYPE_U8 => {
                Some(Value::ConstantString(expected, str.as_bytes().into()))
            }
            (&E::UnOp(inner, UnOp::Cast), _) => {
                // TODO: test if allowed
                let (value, _ty) = self.synth_expr(ctx, inner)?;
                let instr = ctx.blocks[ctx.block]
                    .instructions
                    .push(InstrIdx, Instruction::Cast(value.clone(), expected));

                let reg = Value::Reg(ctx.block, Some(instr));
                Some(reg)
            }
            (&E::With(handler_expr, body), _) => ctx.child(|ctx| {
                let (handler, handler_ty) = self.synth_expr(ctx, handler_expr)?;

                if handler_ty != TYPE_ERROR {
                    let Type::Handler(lazy) = self.ir.types[handler_ty] else {
                        unreachable!()
                    };
                    let Type::HandlerType(ref ty) = self.ir.types[lazy.typeof_handler] else {
                        unreachable!()
                    };

                    let fail = ty.fail_type;
                    let generic_val = ty.effect.clone();

                    let handler_ref =
                        ctx.push_deref(false, Instruction::Reference(handler, handler_ty));
                    ctx.scope.top().effect_stack.push((
                        handler_ty,
                        generic_val,
                        handler_ref,
                        ctx.yeetable_ret,
                    ));

                    if let Some(yeetable) = ctx.yeetable {
                        self.check_move(
                            fail,
                            yeetable,
                            TypeRange {
                                loc: self.ast.exprs[handler_expr].empty(),
                                def: ctx.yeetable_def,
                            },
                        );
                    } else {
                        ctx.yeetable = Some(fail);
                    }
                }

                self.check_expr(ctx, body, expected, expected_def)
            }),
            (&E::Try(body), _) => ctx.child(|ctx| {
                let end = ctx.blocks.push(
                    BlockIdx,
                    Block {
                        instructions: VecMap::new(),
                        value: None,
                    },
                );

                let old_yeet = ctx.yeetable;
                let old_def = ctx.yeetable_def;
                let old_ret = ctx.yeetable_ret;

                ctx.yeetable = Some(expected);
                ctx.yeetable_def = expected_def;
                ctx.yeetable_ret = Some(end);

                let body_check = self.check_expr(ctx, body, expected, expected_def);
                if body_check.is_none() {
                    ctx.push(Instruction::Unreachable);
                }

                if matches!(self.ir.types[expected], Type::Handler(_)) {
                    self.errors
                        .push(self.ast.exprs[body].with(Error::TryReturnsHandler));
                }

                let last = ctx.jump_to(end);
                ctx.blocks[end].value = Some((
                    expected,
                    body_check.into_iter().map(|value| (value, last)).collect(),
                ));

                ctx.yeetable = old_yeet;
                ctx.yeetable_def = old_def;
                ctx.yeetable_ret = old_ret;
                Some(Value::Reg(end, None))
            }),
            (&E::Call(callee, ref args), _) => {
                // TODO: currently we assume func is an Ident expr or Effect Member expr
                let Some(fun) = (match self.ast.exprs[callee].0 {
                    E::Member(package, ident) => match self.ast.exprs[package].0 {
                        E::Ident(package) => ctx.scope.try_package_fun(self, package, ident),
                        _ => todo!(),
                    },
                    E::Ident(ident) => ctx.scope.try_function(self, ident),
                    _ => todo!(),
                }) else {
                    return Some(Value::ConstantError);
                };

                let sign = &fun.sign(&self.ir);
                if sign.params.len() != args.len() {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::ParameterMismatch(
                            None,
                            sign.params.len(),
                            args.len(),
                        )));
                }

                // get return type
                let mut generic_params = GenericParams::new();
                let ret = sign.return_type.ty;
                self.infer_generics(&mut generic_params, expected, ret);

                // get params and infer generic params
                let sign = &fun.sign(&self.ir);
                let args = args
                    .iter()
                    .copied()
                    .zip(
                        sign.params
                            .values()
                            .map(|p| (p.ty, p.type_def, p.const_generic))
                            .collect::<Vec<_>>(),
                    )
                    .map(|(arg, (param_ty, param_def, const_generic))| {
                        let val = match self.translate_generics(param_ty, &generic_params, false) {
                            Some(from) => {
                                let val = self.check_expr(ctx, arg, from, Some(param_def))?;
                                self.infer_generics(&mut generic_params, from, param_ty);
                                val
                            }
                            None => {
                                let (val, from) = self.synth_expr(ctx, arg)?;
                                self.infer_generics(&mut generic_params, from, param_ty);

                                if from != TYPE_ERROR
                                    && !self
                                        .translate_generics(param_ty, &generic_params, false)
                                        .is_some_and(|to| self.test_move(from, to))
                                {
                                    self.errors
                                        .push(self.ast.exprs[arg].with(Error::TypeMismatch(
                                            Some(param_def),
                                            format!("{}", FmtType(&self.ir, param_ty)),
                                            format!("{}", FmtType(&self.ir, from)),
                                        )))
                                }

                                val
                            }
                        };
                        if let Some(const_generic) = const_generic {
                            if val.is_constant() {
                                generic_params.push((
                                    const_generic,
                                    self.insert_type(Type::CompileTime(val.clone())),
                                ))
                            } else {
                                todo!("give error: not constant")
                            }
                        }
                        Some(val)
                    })
                    .collect::<Option<Vec<_>>>()?;

                // get effects
                let mut not_enough_info = false;
                let mut effects = Vec::new();
                let mut handled = ctx.all_handled();
                for effect in 0..fun.sign(&self.ir).effect_stack.len() {
                    // get effect ident
                    let ef = &fun.sign(&self.ir).effect_stack[effect].0;
                    let gen = ef.0;

                    let ident = match ef.1 {
                        GenericVal::Literal(ref ident) => GenericVal::Literal(ident.clone()),
                        GenericVal::Generic(idx) => match get_param(&generic_params, idx) {
                            Some(ty) => match self.ir.types[ty] {
                                Type::Effect(ref ident) => GenericVal::Literal(ident.clone()),
                                Type::Generic(generic) => GenericVal::Generic(generic.idx),
                                Type::Error => continue,
                                _ => unreachable!(),
                            },
                            None => {
                                not_enough_info = true;
                                continue;
                            }
                        },
                    };
                    let ident = match ident {
                        GenericVal::Literal(ident) => {
                            let Some(translated) = ident
                                .generic_params
                                .iter()
                                .copied()
                                .map(|(idx, ty)| {
                                    Some((
                                        idx,
                                        self.translate_generics(ty, &generic_params, false)?,
                                    ))
                                })
                                .collect::<Option<Vec<_>>>()
                            else {
                                continue;
                            };
                            GenericVal::Literal(EffectIdent {
                                effect: ident.effect,
                                generic_params: translated,
                            })
                        }
                        ident => ident,
                    };

                    // find matching effect in stack
                    match ctx.get_effect(self, &ident, error_loc.loc) {
                        Some((ty, idx, _)) => {
                            if matches!(idx, Value::ConstantHandler(_, _)) {
                                // implied handler
                                if let Some(block) = ctx.yeetable_ret {
                                    handled.push((ty, block));
                                }
                            }

                            self.infer_generics(&mut generic_params, ty, gen);
                            effects.push(idx);
                        }
                        None => {
                            // error
                            let def = fun.sign(&self.ir).effect_stack[effect].empty();
                            self.errors
                                .push(self.ast.exprs[expr].with(Error::UnresolvedEffect(def)));
                        }
                    }
                }

                // make sure we got all generics inferred
                let sign = &fun.sign(&self.ir);
                generic_params.sort_unstable_by_key(|(idx, _)| idx.0);
                if !generic_params
                    .iter()
                    .map(|&(idx, _)| idx)
                    .eq(fun.generic_indices(&self.ir))
                {
                    // FIXME: fix this (infer using effect stack)
                    println!(
                        "this occurs when an effect param doesn't appear in its function {}",
                        sign.name
                    );
                }

                if expected != TYPE_ERROR
                    && !self
                        .translate_generics(ret, &generic_params, true)
                        .is_some_and(|from| self.test_move(from, expected))
                {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::TypeMismatch(
                            None,
                            format!("{}", FmtType(&self.ir, expected)),
                            format!("{}", FmtType(&self.ir, ret)),
                        )))
                }

                if not_enough_info {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                }

                let val = ctx.push(Instruction::Call(
                    fun,
                    generic_params,
                    args,
                    effects,
                    handled,
                ));
                if ret == TYPE_NEVER {
                    None
                } else {
                    Some(val)
                }
            }
            (E::Handler(ast::Handler::Lambda(lambda)), &Type::Handler(lazy)) => {
                ctx.child(|ctx| {
                    let ty = match self.ir.types[lazy.typeof_handler] {
                        Type::HandlerType(ref ty) => ty,
                        Type::Generic(_) => todo!("give error"),
                        _ => unreachable!(),
                    };
                    let fail = ty.fail_type;
                    let eff = match ty.effect {
                        GenericVal::Literal(ref effect) => effect.clone(),
                        GenericVal::Generic(_) => todo!("give error"),
                    };

                    // check function
                    let ast = &self.ast.effects[eff.effect];
                    if ast.functions.len() != 1 {
                        todo!("give error");
                    }

                    let fun = &ast.functions[EffFunIdx(0)];
                    if fun.sign.inputs.len() != lambda.inputs.len() {
                        todo!("give error");
                    }

                    // analyze signature
                    let mut sign = self.ir.effects[eff.effect].funs[EffFunIdx(0)].clone();

                    let mut generic_params = eff.generic_params.clone();
                    generic_params.extend(self.params_from_generics(&sign.generics));

                    for (param, ident) in sign
                        .params
                        .values_mut()
                        .zip(lambda.inputs.values().copied())
                    {
                        // rename params to lambda names
                        param.name_def = self.ast.idents[ident].empty();
                        param.name = self.ast.idents[ident].0.clone();

                        param.ty = self
                            .translate_generics(param.ty, &generic_params, true)
                            .unwrap();
                    }
                    sign.effect_stack = sign
                        .effect_stack
                        .iter()
                        .map(|e| {
                            e.as_ref().map(|(ty, id)| {
                                let ty =
                                    self.translate_generics(*ty, &generic_params, true).unwrap();
                                let id = match id {
                                    GenericVal::Literal(id) => {
                                        let effect = id.effect;
                                        let generic_params = id
                                            .generic_params
                                            .iter()
                                            .map(|&(idx, ty)| {
                                                (
                                                    idx,
                                                    self.translate_generics(
                                                        ty,
                                                        &generic_params,
                                                        true,
                                                    )
                                                    .unwrap(),
                                                )
                                            })
                                            .collect();
                                        GenericVal::Literal(EffectIdent {
                                            effect,
                                            generic_params,
                                        })
                                    }
                                    GenericVal::Generic(idx) => {
                                        match self.ir.types
                                            [get_param(&generic_params, *idx).unwrap()]
                                        {
                                            Type::Effect(ref id) => GenericVal::Literal(id.clone()),
                                            Type::Generic(g) => GenericVal::Generic(g.idx),
                                            _ => unreachable!(),
                                        }
                                    }
                                };
                                (ty, id)
                            })
                        })
                        .collect();
                    sign.return_type.ty = self
                        .translate_generics(sign.return_type.ty, &generic_params, true)
                        .unwrap();

                    // analyze function
                    let mut captures = Vec::new();
                    let imp = self.generate_function(
                        Either::Right(&sign),
                        lambda.body,
                        ctx.scope,
                        Some(fail),
                        None,
                        &mut captures,
                        lambda.moved,
                    );

                    // create handler
                    let generics = ctx.all_generics();
                    let generic_params = self.params_from_generics(&generics);

                    let capture_types = captures
                        .iter()
                        .map(|s| match s {
                            Either::Left(s) => ctx.get_capture(self, s, lambda.moved).unwrap().ty,
                            Either::Right(s) => {
                                let ty = ctx.get_effect(self, s, error_loc.loc).unwrap().0;
                                self.insert_type(Type::Pointer(false, ty))
                            }
                        })
                        .collect();
                    let handler = self.push_handler(Handler {
                        debug_name: format!("H{}", self.ir.handlers.len()),
                        generics,

                        effect: eff.effect,
                        generic_params: eff.generic_params,
                        fail,

                        captures: capture_types,
                        funs: vec![(sign, imp)].into(),
                    });

                    let idx = self.ir.lazy_handlers.push(
                        LazyIdx,
                        LazyValue::Some(GenericVal::Literal(HandlerIdent {
                            handler,
                            generic_params,
                            fail_type: fail,
                        })),
                    );
                    let ty = self.insert_type(Type::Handler(Lazy {
                        idx,
                        typeof_handler: lazy.typeof_handler,
                    }));
                    self.check_move(ty, expected, error_loc);

                    Some(Value::ConstantHandler(
                        ty,
                        captures
                            .iter()
                            .map(|s| match s {
                                Either::Left(s) => {
                                    ctx.get_capture(self, s, lambda.moved).unwrap().value
                                }
                                Either::Right(s) => {
                                    let (ty, val, _) =
                                        ctx.get_effect(self, s, error_loc.loc).unwrap();
                                    match val {
                                        Value::Deref(val, _) => *val,
                                        _ => {
                                            let ty = self.insert_type(Type::Pointer(false, ty));
                                            ctx.push(Instruction::Reference(val, ty))
                                        }
                                    }
                                }
                            })
                            .collect(),
                    ))
                })
            }
            (
                &E::BinOp(
                    left,
                    op @ (BinOp::Divide | BinOp::Multiply | BinOp::Subtract | BinOp::Add),
                    right,
                ),
                _,
            ) => {
                let left = self.check_expr(ctx, left, expected, expected_def)?;
                let right = self.check_expr(ctx, right, expected, expected_def)?;

                let res = ctx.push(match op {
                    BinOp::Divide => Instruction::Div(expected, left, right),
                    BinOp::Multiply => Instruction::Mul(expected, left, right),
                    BinOp::Subtract => Instruction::Sub(expected, left, right),
                    BinOp::Add => Instruction::Add(expected, left, right),
                    _ => unreachable!(),
                });

                Some(res)
            }

            _ => {
                let (found, found_ty) = self.synth_expr(ctx, expr)?;
                self.check_move(found_ty, expected, error_loc);
                Some(found)
            }
        }
    }
    fn synth_expr(&mut self, ctx: &mut FunCtx, expr: ExprIdx) -> Option<(Value, TypeIdx)> {
        use Expression as E;
        match self.ast.exprs[expr].0 {
            E::SizeOf(ty) => {
                let ty = self.analyze_type(ctx.scope, ty, None, false, &mut Self::no_handler);
                Some((Value::ConstantSizeOf(ty), TYPE_USIZE))
            }
            E::AlignOf(ty) => {
                let ty = self.analyze_type(ctx.scope, ty, None, false, &mut Self::no_handler);
                Some((Value::ConstantAlignOf(ty), TYPE_U8))
            }
            E::Body(ref body) => ctx.child(|ctx| {
                for expr in body.main.iter().copied() {
                    self.check_expr(ctx, expr, TYPE_NONE, None)?;
                }
                body.last
                    .map(|expr| self.synth_expr(ctx, expr))
                    .unwrap_or(Some((Value::ConstantNone, TYPE_NONE)))
            }),
            E::Loop(inner) => {
                // LLVM fix: entry block must not have predecessors
                if ctx.block == BlockIdx(0) {
                    ctx.jump();
                }

                let old = ctx.jump();
                self.synth_expr(ctx, inner)?;
                ctx.push(Instruction::Jump(old));
                None
            }
            E::IfElseUnwrap(mptr, ref yes, no) => {
                let (mptr, mptr_ty) = self.synth_expr(ctx, mptr)?;

                let uptr = ctx.push(Instruction::Cast(mptr.clone(), TYPE_UPTR));
                let cond = ctx.push(Instruction::Equals(uptr, Value::ConstantZero(TYPE_UPTR)));

                if yes.inputs.len() != 1 {
                    panic!("give error");
                }
                let ptr_ty = match self.ir.types[mptr_ty] {
                    Type::MaybePointer(isconst, inner) => {
                        self.insert_type(Type::Pointer(isconst, inner))
                    }
                    _ => panic!("give error"),
                };

                ctx.branch(
                    self,
                    cond,
                    |me, ctx| match no {
                        Some(no) => me
                            .synth_expr(ctx, no)
                            .map(|(val, ty)| (val, ty, Some(self.ast.exprs[no].empty()))),
                        None => Some((Value::ConstantNone, TYPE_NONE, None)),
                    },
                    |me, ctx| {
                        let ident = yes.inputs.values().copied().next().unwrap();
                        let ident = self.ast.idents[ident].0.clone();
                        ctx.define(
                            ident,
                            Variable {
                                value: mptr,
                                ty: ptr_ty,
                                mutable: false,
                            },
                        );
                        me.synth_expr(ctx, yes.body)
                            .map(|(val, ty)| (val, ty, Some(self.ast.exprs[yes.body].empty())))
                    },
                )
            }
            E::IfElse(cond, yes, no) => {
                let cond = self.check_expr(ctx, cond, TYPE_BOOL, None)?;
                ctx.branch(
                    self,
                    cond,
                    |me, ctx| {
                        me.synth_expr(ctx, yes)
                            .map(|(val, ty)| (val, ty, Some(self.ast.exprs[yes].empty())))
                    },
                    |me, ctx| match no {
                        Some(no) => me
                            .synth_expr(ctx, no)
                            .map(|(val, ty)| (val, ty, Some(self.ast.exprs[no].empty()))),
                        None => Some((Value::ConstantNone, TYPE_NONE, None)),
                    },
                )
            }
            E::With(handler_expr, body) => ctx.child(|ctx| {
                let (handler, handler_ty) = self.synth_expr(ctx, handler_expr)?;

                if handler_ty != TYPE_ERROR {
                    let Type::Handler(lazy) = self.ir.types[handler_ty] else {
                        unreachable!()
                    };
                    let Type::HandlerType(ref ty) = self.ir.types[lazy.typeof_handler] else {
                        unreachable!()
                    };

                    let fail = ty.fail_type;
                    let generic_val = ty.effect.clone();

                    let handler_ref =
                        ctx.push_deref(false, Instruction::Reference(handler, handler_ty));
                    ctx.scope.top().effect_stack.push((
                        handler_ty,
                        generic_val,
                        handler_ref,
                        ctx.yeetable_ret,
                    ));

                    if let Some(yeetable) = ctx.yeetable {
                        self.check_move(
                            fail,
                            yeetable,
                            TypeRange {
                                loc: self.ast.exprs[handler_expr].empty(),
                                def: ctx.yeetable_def,
                            },
                        );
                    } else {
                        ctx.yeetable = Some(fail);
                    }
                };

                self.synth_expr(ctx, body)
            }),
            E::Try(body) => ctx.child(|ctx| {
                let end = ctx.blocks.push(
                    BlockIdx,
                    Block {
                        instructions: VecMap::new(),
                        value: None,
                    },
                );

                let old_yeet = ctx.yeetable;
                let old_def = ctx.yeetable_def;
                let old_ret = ctx.yeetable_ret;

                ctx.yeetable = None;
                ctx.yeetable_def = None;
                ctx.yeetable_ret = Some(end);

                let body_synth = self.synth_expr(ctx, body);
                if body_synth.is_none() {
                    ctx.push(Instruction::Unreachable);
                }

                let ty = body_synth
                    .as_ref()
                    .map(|&(_, ty)| ty)
                    .or(ctx.yeetable)
                    .unwrap();
                if matches!(self.ir.types[ty], Type::Handler(_)) {
                    self.errors
                        .push(self.ast.exprs[body].with(Error::TryReturnsHandler));
                }

                if let Some(yeet_ty) = ctx.yeetable {
                    self.check_move(
                        yeet_ty,
                        ty,
                        TypeRange {
                            loc: self.ast.exprs[body].empty(),
                            def: None,
                        },
                    );
                }

                let last = ctx.jump_to(end);
                ctx.blocks[end].value = Some((
                    ty,
                    body_synth
                        .into_iter()
                        .map(|(value, _)| (value, last))
                        .collect(),
                ));

                ctx.yeetable = old_yeet;
                ctx.yeetable_def = old_def;
                ctx.yeetable_ret = old_ret;
                Some((Value::Reg(end, None), ty))
            }),
            E::Handler(ref handler) => match handler {
                ast::Handler::Full {
                    effect,
                    fail_type,
                    functions,
                    moved,
                } => {
                    ctx.child(|ctx| {
                        let eff = {
                            let effidx = match effect.ident.package {
                                Some(pkg) => {
                                    ctx.scope.try_package_effect(self, pkg, effect.ident.ident)
                                }
                                None => ctx.scope.try_effect(self, effect.ident.ident),
                            };
                            let effidx = match effidx {
                                Some(GenericVal::Literal(idx)) => idx,
                                Some(GenericVal::Generic(_)) => todo!("give error"),
                                None => return Some((Value::ConstantError, TYPE_ERROR)),
                            };

                            let params = match effect.params {
                                Some(ref params) => params
                                    .iter()
                                    .copied()
                                    .map(|ty| {
                                        self.analyze_type(
                                            ctx.scope,
                                            ty,
                                            None,
                                            false,
                                            &mut Self::no_handler,
                                        )
                                    })
                                    .collect(),
                                None => Vec::new(),
                            };
                            let generic_params = self.ir.effects[effidx]
                                .generics
                                .iter()
                                .map(|generic| generic.idx)
                                .zip(params)
                                .collect::<Vec<_>>();

                            EffectIdent {
                                effect: effidx,
                                generic_params,
                            }
                        };
                        let fail = self.analyze_fail(
                            ctx.scope,
                            *fail_type,
                            None,
                            false,
                            &mut Self::no_handler,
                        );

                        // check functions
                        let mut captures = Vec::new();
                        let mut funs: VecMap<EffFunIdx, (FunSign, FunImpl)> =
                            std::iter::repeat_with(Default::default)
                                .take(self.ast.effects[eff.effect].functions.len())
                                .collect();
                        for function in functions {
                            // analyze signature
                            let name = &self.ast.idents[function.decl.name];
                            let matching = self.ast.effects[eff.effect]
                                .functions
                                .iter(EffFunIdx)
                                .find(|(_, decl)| self.ast.idents[decl.name].0.eq(&name.0));

                            let sign = self.analyze_sign(
                                ctx.scope,
                                function.decl.name,
                                Some((
                                    EffectIdent {
                                        effect: eff.effect,
                                        generic_params: eff.generic_params.clone(),
                                    },
                                    None,
                                )),
                                &function.decl.sign,
                            );

                            match matching {
                                Some((idx, _)) => {
                                    // translate sign
                                    let sign = self.check_sign(
                                        sign,
                                        FunIdent::Effect(eff.effect, idx),
                                        &eff.generic_params,
                                    );

                                    // analyze function
                                    let imp = self.generate_function(
                                        Either::Right(&sign),
                                        function.body,
                                        ctx.scope,
                                        Some(fail),
                                        None,
                                        &mut captures,
                                        *moved,
                                    );

                                    funs[idx] = (sign, imp)
                                }
                                None => {
                                    self.errors.push(
                                        name.with(Error::UnknownEffectFun(
                                            Some(
                                                self.ast.idents[self.ast.effects[eff.effect].name]
                                                    .empty(),
                                            ),
                                            Some(self.ast.idents[effect.ident.ident].empty()),
                                        )),
                                    );
                                }
                            }
                        }

                        // check if signatures match
                        let mut missing = Vec::new();
                        for (idx, (sign, _)) in funs.iter(EffFunIdx) {
                            let name = self.ast.idents
                                [self.ast.effects[eff.effect].functions[idx].name]
                                .empty();

                            // check if missing
                            if sign.def.is_none() {
                                missing.push(name);
                            }
                        }
                        if !missing.is_empty() {
                            self.errors.push(self.ast.idents[effect.ident.ident].with(
                                Error::UnimplementedMethods(
                                    self.ast.idents[self.ast.effects[eff.effect].name].empty(),
                                    missing,
                                ),
                            ));
                        }

                        // create handler
                        let generics = ctx.all_generics();
                        let generic_params = self.params_from_generics(&generics);

                        let capture_types = captures
                            .iter()
                            .map(|s| match s {
                                Either::Left(s) => ctx.get_capture(self, s, *moved).unwrap().ty,
                                Either::Right(s) => {
                                    let ty = ctx
                                        .get_effect(self, s, self.ast.exprs[expr].empty())
                                        .unwrap()
                                        .0;
                                    self.insert_type(Type::Pointer(false, ty))
                                }
                            })
                            .collect();
                        let handler = self.push_handler(Handler {
                            debug_name: format!("H{}", self.ir.handlers.len()),
                            generics,

                            effect: eff.effect,
                            generic_params: eff.generic_params.clone(),
                            fail,

                            captures: capture_types,
                            funs,
                        });

                        let idx = self.ir.lazy_handlers.push(
                            LazyIdx,
                            LazyValue::Some(GenericVal::Literal(HandlerIdent {
                                handler,
                                generic_params,
                                fail_type: fail,
                            })),
                        );
                        let metaty = self.insert_type(Type::HandlerType(HandlerType {
                            effect: GenericVal::Literal(EffectIdent {
                                effect: eff.effect,
                                generic_params: eff.generic_params,
                            }),
                            fail_type: fail,
                        }));
                        let ty = self.insert_type(Type::Handler(Lazy {
                            idx,
                            typeof_handler: metaty,
                        }));
                        Some((
                            Value::ConstantHandler(
                                ty,
                                captures
                                    .iter()
                                    .map(|s| match s {
                                        Either::Left(s) => {
                                            ctx.get_capture(self, s, *moved).unwrap().value
                                        }
                                        Either::Right(s) => {
                                            let (ty, val, _) = ctx
                                                .get_effect(self, s, self.ast.exprs[expr].empty())
                                                .unwrap();
                                            match val {
                                                Value::Deref(val, _) => *val,
                                                _ => {
                                                    let ty =
                                                        self.insert_type(Type::Pointer(false, ty));
                                                    ctx.push(Instruction::Reference(val, ty))
                                                }
                                            }
                                        }
                                    })
                                    .collect(),
                            ),
                            ty,
                        ))
                    })
                }
                ast::Handler::Lambda(_) => {
                    // lambdas require type information
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                    Some((Value::ConstantError, TYPE_ERROR))
                }
            },
            E::DotCall(handler_expr, ref args) => {
                let (handler, handler_ty) = self.synth_expr(ctx, handler_expr)?;
                let metaty = match self.ir.types[handler_ty] {
                    Type::Handler(l) => l.typeof_handler,
                    _ => panic!("give error"),
                };
                let (effect, fail_type) = match &self.ir.types[metaty] {
                    Type::HandlerType(t) => (t.effect.literal().expect("give error"), t.fail_type),
                    _ => unreachable!(),
                };

                if self.ir.effects[effect.effect].funs.len() != 1 {
                    panic!("give error");
                }
                let fun = FunIdent::Effect(effect.effect, EffFunIdx(0));

                let sign = fun.sign(&self.ir);
                if sign.params.len() != args.len() {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::ParameterMismatch(
                            None,
                            sign.params.len(),
                            args.len(),
                        )));
                }

                // get params and infer generic params
                let mut generic_params = effect.generic_params.clone();
                let args = args
                    .iter()
                    .copied()
                    .zip(
                        sign.params
                            .values()
                            .map(|p| (p.ty, p.type_def, p.const_generic))
                            .collect::<Vec<_>>(),
                    )
                    .map(|(arg, (param_ty, param_def, const_generic))| {
                        let val = match self.translate_generics(param_ty, &generic_params, false) {
                            Some(from) => {
                                let val = self.check_expr(ctx, arg, from, Some(param_def))?;
                                self.infer_generics(&mut generic_params, from, param_ty);
                                val
                            }
                            None => {
                                let (val, from) = self.synth_expr(ctx, arg)?;
                                self.infer_generics(&mut generic_params, from, param_ty);

                                if from != TYPE_ERROR
                                    && !self
                                        .translate_generics(param_ty, &generic_params, false)
                                        .is_some_and(|to| self.test_move(from, to))
                                {
                                    self.errors
                                        .push(self.ast.exprs[arg].with(Error::TypeMismatch(
                                            Some(param_def),
                                            format!("{}", FmtType(&self.ir, param_ty)),
                                            format!("{}", FmtType(&self.ir, from)),
                                        )))
                                }

                                val
                            }
                        };
                        if let Some(const_generic) = const_generic {
                            if val.is_constant() {
                                generic_params.push((
                                    const_generic,
                                    self.insert_type(Type::CompileTime(val.clone())),
                                ))
                            } else {
                                todo!("give error: not constant")
                            }
                        }
                        Some(val)
                    })
                    .collect::<Option<Vec<_>>>()?;

                // get effects
                let mut not_enough_info = false;
                let mut effects = Vec::new();
                let mut handled = ctx.all_handled();
                for effect in 0..fun.sign(&self.ir).effect_stack.len() - 1 {
                    // get effect ident
                    let ef = &fun.sign(&self.ir).effect_stack[effect].0;
                    let gen = ef.0;

                    let ident = match ef.1 {
                        GenericVal::Literal(ref ident) => GenericVal::Literal(ident.clone()),
                        GenericVal::Generic(idx) => match get_param(&generic_params, idx) {
                            Some(ty) => match self.ir.types[ty] {
                                Type::Effect(ref ident) => GenericVal::Literal(ident.clone()),
                                Type::Generic(generic) => GenericVal::Generic(generic.idx),
                                Type::Error => continue,
                                _ => unreachable!(),
                            },
                            None => {
                                not_enough_info = true;
                                continue;
                            }
                        },
                    };
                    let ident = match ident {
                        GenericVal::Literal(ident) => {
                            let Some(translated) = ident
                                .generic_params
                                .iter()
                                .copied()
                                .map(|(idx, ty)| {
                                    Some((
                                        idx,
                                        self.translate_generics(ty, &generic_params, false)?,
                                    ))
                                })
                                .collect::<Option<Vec<_>>>()
                            else {
                                continue;
                            };
                            GenericVal::Literal(EffectIdent {
                                effect: ident.effect,
                                generic_params: translated,
                            })
                        }
                        ident => ident,
                    };

                    // find matching effect in stack
                    match ctx.get_effect(self, &ident, self.ast.exprs[expr].empty()) {
                        Some((ty, idx, _)) => {
                            if matches!(idx, Value::ConstantHandler(_, _)) {
                                // implied handler
                                if let Some(block) = ctx.yeetable_ret {
                                    handled.push((ty, block));
                                }
                            }

                            self.infer_generics(&mut generic_params, ty, gen);
                            effects.push(idx);
                        }
                        None => {
                            // error
                            let def = fun.sign(&self.ir).effect_stack[effect].empty();
                            self.errors
                                .push(self.ast.exprs[expr].with(Error::UnresolvedEffect(def)));
                        }
                    }
                }
                self.infer_generics(
                    &mut generic_params,
                    handler_ty,
                    fun.sign(&self.ir).effect_stack.last().unwrap().0 .0,
                );
                effects.push(handler);
                if let Some(block) = ctx.yeetable_ret {
                    handled.push((handler_ty, block));
                }

                // make sure we got all generics inferred
                let sign = &fun.sign(&self.ir);
                generic_params.sort_unstable_by_key(|(idx, _)| idx.0);
                if !generic_params
                    .iter()
                    .map(|&(idx, _)| idx)
                    .eq(fun.generic_indices(&self.ir))
                {
                    // FIXME: fix this (infer using effect stack)
                    println!(
                        "this occurs when an effect param doesn't appear in its function {}",
                        sign.name
                    );
                }

                // get return type
                let sign = &fun.sign(&self.ir);
                let return_type =
                    match self.translate_generics(sign.return_type.ty, &generic_params, true) {
                        Some(ty) => ty,
                        None => {
                            not_enough_info = true;
                            TYPE_ERROR
                        }
                    };

                if not_enough_info {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                }

                if fail_type != TYPE_NEVER {
                    match ctx.yeetable {
                        Some(fail) => self.check_move(
                            fail_type,
                            fail,
                            TypeRange {
                                loc: self.ast.exprs[handler_expr].empty(),
                                def: ctx.yeetable_def,
                            },
                        ),
                        None => ctx.yeetable = Some(fail_type),
                    }
                }

                let val = ctx.push(Instruction::Call(
                    fun,
                    generic_params,
                    args,
                    effects,
                    handled,
                ));
                if return_type == TYPE_NEVER {
                    None
                } else {
                    Some((val, return_type))
                }
            }
            E::Call(callee, ref args) => {
                // TODO: currently we assume func is an Ident expr or Effect Member expr
                let Some(fun) = (match self.ast.exprs[callee].0 {
                    E::Member(package, ident) => match self.ast.exprs[package].0 {
                        E::Ident(package) => ctx.scope.try_package_fun(self, package, ident),
                        _ => todo!(),
                    },
                    E::Ident(ident) => ctx.scope.try_function(self, ident),
                    _ => todo!(),
                }) else {
                    return Some((Value::ConstantError, TYPE_ERROR));
                };

                let sign = &fun.sign(&self.ir);
                if sign.params.len() != args.len() {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::ParameterMismatch(
                            None,
                            sign.params.len(),
                            args.len(),
                        )));
                }

                // get params and infer generic params
                let mut generic_params = GenericParams::new();
                let args = args
                    .iter()
                    .copied()
                    .zip(
                        sign.params
                            .values()
                            .map(|p| (p.ty, p.type_def, p.const_generic))
                            .collect::<Vec<_>>(),
                    )
                    .map(|(arg, (param_ty, param_def, const_generic))| {
                        let val = match self.translate_generics(param_ty, &generic_params, false) {
                            Some(from) => {
                                let val = self.check_expr(ctx, arg, from, Some(param_def))?;
                                self.infer_generics(&mut generic_params, from, param_ty);
                                val
                            }
                            None => {
                                let (val, from) = self.synth_expr(ctx, arg)?;
                                self.infer_generics(&mut generic_params, from, param_ty);

                                if from != TYPE_ERROR
                                    && !self
                                        .translate_generics(param_ty, &generic_params, false)
                                        .is_some_and(|to| self.test_move(from, to))
                                {
                                    self.errors
                                        .push(self.ast.exprs[arg].with(Error::TypeMismatch(
                                            Some(param_def),
                                            format!("{}", FmtType(&self.ir, param_ty)),
                                            format!("{}", FmtType(&self.ir, from)),
                                        )))
                                }

                                val
                            }
                        };
                        if let Some(const_generic) = const_generic {
                            if val.is_constant() {
                                generic_params.push((
                                    const_generic,
                                    self.insert_type(Type::CompileTime(val.clone())),
                                ))
                            } else {
                                todo!("give error: not constant")
                            }
                        }
                        Some(val)
                    })
                    .collect::<Option<Vec<_>>>()?;

                // get effects
                let mut not_enough_info = false;
                let mut effects = Vec::new();
                let mut handled = ctx.all_handled();
                for effect in 0..fun.sign(&self.ir).effect_stack.len() {
                    // get effect ident
                    let ef = &fun.sign(&self.ir).effect_stack[effect].0;
                    let gen = ef.0;

                    let ident = match ef.1 {
                        GenericVal::Literal(ref ident) => GenericVal::Literal(ident.clone()),
                        GenericVal::Generic(idx) => match get_param(&generic_params, idx) {
                            Some(ty) => match self.ir.types[ty] {
                                Type::Effect(ref ident) => GenericVal::Literal(ident.clone()),
                                Type::Generic(generic) => GenericVal::Generic(generic.idx),
                                Type::Error => continue,
                                _ => unreachable!(),
                            },
                            None => {
                                not_enough_info = true;
                                continue;
                            }
                        },
                    };
                    let ident = match ident {
                        GenericVal::Literal(ident) => {
                            let Some(translated) = ident
                                .generic_params
                                .iter()
                                .copied()
                                .map(|(idx, ty)| {
                                    Some((
                                        idx,
                                        self.translate_generics(ty, &generic_params, false)?,
                                    ))
                                })
                                .collect::<Option<Vec<_>>>()
                            else {
                                continue;
                            };
                            GenericVal::Literal(EffectIdent {
                                effect: ident.effect,
                                generic_params: translated,
                            })
                        }
                        ident => ident,
                    };

                    // find matching effect in stack
                    match ctx.get_effect(self, &ident, self.ast.exprs[expr].empty()) {
                        Some((ty, idx, _)) => {
                            if matches!(idx, Value::ConstantHandler(_, _)) {
                                // implied handler
                                if let Some(block) = ctx.yeetable_ret {
                                    handled.push((ty, block));
                                }
                            }

                            self.infer_generics(&mut generic_params, ty, gen);
                            effects.push(idx);
                        }
                        None => {
                            // error
                            let def = fun.sign(&self.ir).effect_stack[effect].empty();
                            self.errors
                                .push(self.ast.exprs[expr].with(Error::UnresolvedEffect(def)));
                        }
                    }
                }

                // make sure we got all generics inferred
                let sign = &fun.sign(&self.ir);
                generic_params.sort_unstable_by_key(|(idx, _)| idx.0);
                if !generic_params
                    .iter()
                    .map(|&(idx, _)| idx)
                    .eq(fun.generic_indices(&self.ir))
                {
                    // FIXME: fix this (infer using effect stack)
                    println!(
                        "this occurs when an effect param doesn't appear in its function {}",
                        sign.name
                    );
                }

                // get return type
                let sign = &fun.sign(&self.ir);
                let return_type =
                    match self.translate_generics(sign.return_type.ty, &generic_params, true) {
                        Some(ty) => ty,
                        None => {
                            not_enough_info = true;
                            TYPE_ERROR
                        }
                    };

                if not_enough_info {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                }

                let val = ctx.push(Instruction::Call(
                    fun,
                    generic_params,
                    args,
                    effects,
                    handled,
                ));
                if return_type == TYPE_NEVER {
                    None
                } else {
                    Some((val, return_type))
                }
            }

            E::BinOp(left, BinOp::Assign, right) => {
                let (ptr, isconst, ty) = self.synth_expr_address(ctx, left)?;
                if isconst {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::AssignImmutable(None)));
                    return Some((Value::ConstantNone, TYPE_NONE));
                }

                let right = self.check_expr(ctx, right, ty, None)?;
                ctx.push(Instruction::Store(ptr, right));

                Some((Value::ConstantNone, TYPE_NONE))
            }
            E::BinOp(left, BinOp::Index, right) => {
                let (left, left_ty) = self.synth_expr(ctx, left)?;
                let (ptr, isconst, elem_ty) = match self.ir.types[left_ty] {
                    Type::Slice(isconst, elem) => (
                        ctx.push(Instruction::Member(left, 0, left_ty)),
                        isconst,
                        elem,
                    ),
                    Type::ConstArray(_, elem) => match left {
                        Value::Deref(left, isconst) => (*left, isconst, elem),
                        _ => (ctx.push(Instruction::Reference(left, left_ty)), false, elem),
                    },
                    Type::Error => {
                        return Some((Value::ConstantError, TYPE_ERROR));
                    }
                    _ => todo!("give error"),
                };

                if let E::BinOp(rleft, BinOp::Range, rright) = self.ast.exprs[right].0 {
                    let rleft = self.check_expr(ctx, rleft, TYPE_USIZE, None)?;
                    let rright = self.check_expr(ctx, rright, TYPE_USIZE, None)?;

                    let ptr = ctx.push(Instruction::AdjacentPtr(ptr, rleft.clone(), elem_ty));
                    let len = ctx.push(Instruction::Sub(TYPE_USIZE, rright, rleft));

                    let slice_ty = self.insert_type(Type::Slice(isconst, elem_ty));
                    let slice = Value::ConstantAggregate(slice_ty, vec![ptr, len].into());
                    Some((slice, slice_ty))
                } else {
                    let right = self.check_expr(ctx, right, TYPE_USIZE, None)?;
                    let elem =
                        ctx.push_deref(isconst, Instruction::AdjacentPtr(ptr, right, elem_ty));
                    Some((elem, elem_ty))
                }
            }
            E::BinOp(_, BinOp::Range, _) => {
                todo!("give error")
            }
            E::BinOp(left, op, right) => {
                // TODO: check if int
                let (left, left_ty) = self.synth_expr(ctx, left)?;
                let right = self.check_expr(ctx, right, left_ty, None)?;

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
                    BinOp::Divide => Instruction::Div(out, left, right),
                    BinOp::Multiply => Instruction::Mul(out, left, right),
                    BinOp::Subtract => Instruction::Sub(out, left, right),
                    BinOp::Add => Instruction::Add(out, left, right),
                });

                Some((res, out))
            }
            E::UnOp(inner, UnOp::PostIncrement) => {
                let (ptr, isconst, ty) = self.synth_expr_address(ctx, inner)?;
                if isconst {
                    todo!("give error")
                }

                let loaded = ctx.push(Instruction::Load(ty, ptr.clone()));
                let incremented = ctx.push(Instruction::Add(
                    ty,
                    loaded.clone(),
                    Value::ConstantInt(ty, false, 1),
                ));
                ctx.push(Instruction::Store(ptr, incremented));
                Some((loaded, ty))
            }
            E::UnOp(inner, UnOp::Reference) => {
                let (ptr, isconst, ty) = self.synth_expr_address(ctx, inner)?;
                let ptr_ty = self.insert_type(Type::Pointer(isconst, ty));
                Some((ptr, ptr_ty))
            }
            E::UnOp(_, UnOp::Cast) => {
                self.errors
                    .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                Some((Value::ConstantError, TYPE_ERROR))
            }
            E::Yeet(inner) => {
                match ctx.yeetable {
                    Some(yeet_ty) => {
                        // existing yeetable def
                        if yeet_ty == TYPE_NEVER {
                            self.errors
                                .push(self.ast.exprs[expr].with(Error::UnresolvedTry));
                        } else {
                            let value = match inner {
                                Some(inner) => {
                                    self.check_expr(ctx, inner, yeet_ty, ctx.yeetable_def)?
                                }
                                None => {
                                    self.check_move(
                                        TYPE_NONE,
                                        yeet_ty,
                                        TypeRange {
                                            loc: self.ast.exprs[expr].empty(),
                                            def: ctx.yeetable_def,
                                        },
                                    );
                                    Value::ConstantNone
                                }
                            };
                            ctx.blocks[ctx.block]
                                .instructions
                                .push_value(Instruction::Yeet(value, ctx.yeetable_ret));
                        }
                    }
                    None => {
                        // set yeetable
                        let value = match inner {
                            Some(inner) => {
                                let (val, ty) = self.synth_expr(ctx, inner)?;
                                ctx.yeetable = Some(ty);
                                val
                            }
                            None => {
                                ctx.yeetable = Some(TYPE_NONE);
                                Value::ConstantNone
                            }
                        };
                        ctx.blocks[ctx.block]
                            .instructions
                            .push_value(Instruction::Yeet(value, ctx.yeetable_ret));
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

                if mutable {
                    let ptr = ctx.push_deref(false, Instruction::Reference(value, ty));
                    ctx.define(
                        name,
                        Variable {
                            value: ptr,
                            ty,
                            mutable,
                        },
                    );
                } else {
                    ctx.define(name, Variable { value, ty, mutable });
                }

                Some((Value::ConstantNone, TYPE_NONE))
            }
            E::Array(ref exprs) => {
                let mut iter = exprs.iter().copied();
                match iter.next() {
                    Some(first) => {
                        let (val, ty) = self.synth_expr(ctx, first)?;
                        let elems = std::iter::once(Some(val))
                            .chain(iter.map(|expr| self.check_expr(ctx, expr, ty, None)))
                            .collect::<Option<Rc<[_]>>>()?;
                        let arr_ty = self.insert_type(Type::ConstArray(
                            GenericVal::Literal(elems.len() as u64),
                            ty,
                        ));
                        Some((Value::ConstantAggregate(arr_ty, elems), arr_ty))
                    }
                    None => {
                        self.errors
                            .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                        Some((Value::ConstantError, TYPE_ERROR))
                    }
                }
            }
            E::String(ref str) => Some((
                Value::ConstantString(TYPE_STR, str.as_bytes().into()),
                TYPE_STR,
            )),
            E::Character(ref str) => {
                // TODO: test if fits, test if single char (otherwise test if rune)
                let c = str.chars().next().unwrap();
                let c = u64::from(c);
                Some((Value::ConstantInt(TYPE_CHAR, false, c), TYPE_CHAR))
            }
            E::Ident(id) => {
                let name = &self.ast.idents[id].0;
                match ctx.get_value(self, name) {
                    Some(var) => Some((var.value, var.ty)),
                    None => {
                        self.errors
                            .push(self.ast.idents[id].with(Error::UnknownValue));
                        Some((Value::ConstantError, TYPE_ERROR))
                    }
                }
            }
            E::Int(n) => Some((Value::ConstantInt(TYPE_INT, false, n), TYPE_INT)),
            E::Uninit => {
                self.errors
                    .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                Some((Value::ConstantError, TYPE_ERROR))
            }
            E::As(left, ty) => {
                let expected =
                    self.analyze_type(ctx.scope, ty, None, false, &mut Self::lazy_handler);
                Some((
                    self.check_expr(ctx, left, expected, Some(self.ast.types[ty].empty()))?,
                    expected,
                ))
            }
            E::Do(right) => {
                self.synth_expr(ctx, right)?;
                Some((Value::ConstantNone, TYPE_NONE))
            }
            E::Error => Some((Value::ConstantError, TYPE_ERROR)),
            E::Member(left, right) => {
                let (mut struc, mut ty) = self.synth_expr(ctx, left)?;

                // allow member access to dereference pointers
                while let Type::Pointer(isconst, inner) = self.ir.types[ty] {
                    struc = Value::Deref(Box::new(struc), isconst);
                    ty = inner;
                }

                let idx = match self.ir.types[ty] {
                    Type::Struct(idx) => idx,
                    _ => {
                        panic!("give error");
                    }
                };

                let name = self.ast.idents[right].0.as_str();
                let elem = self.ir.structs[idx]
                    .elems
                    .iter()
                    .position(|(elem, _)| elem.eq(name));

                let Some(elem) = elem else {
                    panic!("give error");
                };

                let val = match struc {
                    Value::Deref(ptr, isconst) => {
                        ctx.push_deref(isconst, Instruction::ElementPtr(*ptr, elem as u32, ty))
                    }
                    _ => ctx.push(Instruction::Member(struc, elem as u32, ty)),
                };
                let ty = self.ir.structs[idx].elems[elem].1;
                Some((val, ty))
            }
        }
    }
    fn get_capability(
        &mut self,
        target: &Target,
        ctx: &mut FunCtx,
        cache: &mut HashMap<EffectIdent, (TypeIdx, Value)>,
        id: EffectIdent,
    ) -> Option<(TypeIdx, Value)> {
        if let Some(val) = cache.get(&id) {
            return Some(val.clone());
        };

        // get matching capability
        let mut capabilities = self.ir.effects[id.effect]
            .capabilities
            .clone()
            .into_iter()
            .filter_map(|cap| {
                if cap.os.is_some_and(|os| !os.eq(target.lucu_os().as_str())) {
                    None?
                }
                if cap.arch.is_some_and(|arch| {
                    !((arch.eq("wasm") && target.lucu_arch().is_wasm())
                        || arch.eq(target.lucu_arch().as_str()))
                }) {
                    None?
                }

                let mut params = Vec::new();
                for (target, output) in id.generic_params.iter().zip(cap.generic_params.iter()) {
                    self.infer_generics(&mut params, target.1, output.1);
                }
                for (target, output) in id.generic_params.iter().zip(cap.generic_params.iter()) {
                    if !self
                        .translate_generics(output.1, &params, true)
                        .is_some_and(|ty| ty != target.1)
                    {
                        None?
                    }
                }

                Some((cap.fun, params))
            });

        let (capability, mut params) = capabilities.next()?;
        if capabilities.next().is_some() {
            None?
        }

        // get capability handler stack
        let stack = capability
            .sign(&self.ir)
            .effect_stack
            .clone()
            .into_iter()
            .map(|ident| {
                let gen = ident.0 .0;

                let ident = ident.0 .1.literal().unwrap();
                let generic_params = ident
                    .generic_params
                    .iter()
                    .copied()
                    .map(|(idx, ty)| (idx, self.translate_generics(ty, &params, true).unwrap()))
                    .collect::<Vec<_>>();

                let capability = self.get_capability(
                    target,
                    ctx,
                    cache,
                    EffectIdent {
                        effect: ident.effect,
                        generic_params,
                    },
                )?;
                self.infer_generics(&mut params, capability.0, gen);
                Some(capability.1)
            })
            .collect::<Option<Vec<_>>>()?;

        assert!(capability.sign(&self.ir).params.is_empty());
        assert!(params.len() == capability.generic_indices(&self.ir).count());

        let type_idx = capability.sign(&self.ir).return_type.ty;
        let type_idx = self.translate_generics(type_idx, &params, true).unwrap();
        let val = ctx.push(Instruction::Call(
            capability,
            params,
            Vec::new(),
            stack,
            Vec::new(),
        ));
        let val = ctx.push_deref(false, Instruction::Reference(val, type_idx));

        cache.insert(id, (type_idx, val.clone()));
        Some((type_idx, val))
    }
}

struct FunCtx<'a> {
    scope: &'a mut ScopeStack,

    yeetable: Option<TypeIdx>,
    yeetable_def: Option<Range>,
    yeetable_ret: Option<BlockIdx>,

    blocks: VecMap<BlockIdx, Block>,
    block: BlockIdx,

    capture_boundary: (bool, usize),
    captures: &'a mut Vec<Either<String, GenericVal<EffectIdent>>>,
}

impl FunCtx<'_> {
    fn child<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push();
        let t = f(self);
        self.scope.pop();
        t
    }
    fn push(&mut self, instr: Instruction) -> Value {
        let idx = self.blocks[self.block].instructions.push(InstrIdx, instr);
        Value::Reg(self.block, Some(idx))
    }
    fn push_deref(&mut self, isconst: bool, instr: Instruction) -> Value {
        Value::Deref(Box::new(self.push(instr)), isconst)
    }
    fn all_generics(&self) -> Generics {
        let mut generics = Vec::new();
        for scope in self.scope.scopes.iter() {
            generics.extend(scope.generics.values().cloned());
        }
        generics.sort_unstable_by_key(|generic| generic.idx.0);
        generics
    }
    fn all_handled(&self) -> Vec<(TypeIdx, BlockIdx)> {
        let mut handled = Vec::new();
        for scope in self.scope.scopes.iter().skip(self.capture_boundary.1) {
            handled.extend(
                scope
                    .effect_stack
                    .iter()
                    .filter_map(|&(ty, _, _, block)| Some((ty, block?))),
            )
        }
        handled
    }
    fn get_value(&mut self, ctx: &SemCtx, name: &str) -> Option<Variable> {
        let mut iter = self.scope.scopes.iter().enumerate().rev().chain([
            (usize::MAX, &ctx.packages[self.scope.package]),
            (usize::MAX, &ctx.packages[ctx.ast.preamble]),
        ]);
        iter.find_map(|(n, s)| {
            let val = s.values.get(name).cloned()?;
            if n < self.capture_boundary.1 && (val.mutable || !val.value.is_constant()) {
                let idx = match self.captures.iter().position(|candidate| {
                    candidate
                        .as_ref()
                        .left()
                        .is_some_and(|candidate| name.eq(candidate))
                }) {
                    Some(idx) => idx,
                    None => {
                        let idx = self.captures.len();
                        self.captures.push(Either::Left(name.into()));
                        idx
                    }
                };
                if val.mutable && !self.capture_boundary.0 {
                    // capture by reference
                    Some(Variable {
                        value: Value::Deref(
                            Box::new(Value::Deref(Box::new(Value::Capture(idx)), true)),
                            false,
                        ),
                        ..val
                    })
                } else {
                    // capture by value
                    Some(Variable {
                        value: Value::Deref(Box::new(Value::Capture(idx)), !val.mutable),
                        ..val
                    })
                }
            } else {
                Some(val)
            }
        })
    }
    fn get_capture(&mut self, ctx: &mut SemCtx, name: &str, moved: bool) -> Option<Variable> {
        self.get_value(ctx, name).map(|v| {
            if v.mutable && !moved {
                // capture by reference
                match v.value {
                    Value::Deref(b, isconst) => {
                        let ptr_ty = ctx.insert_type(Type::Pointer(isconst, v.ty));
                        Variable {
                            value: *b,
                            mutable: false,
                            ty: ptr_ty,
                        }
                    }
                    _ => unreachable!(),
                }
            } else {
                // capture by value
                v
            }
        })
    }
    fn get_effect(
        &mut self,
        ctx: &mut SemCtx,
        ident: &GenericVal<EffectIdent>,
        loc: Range,
    ) -> Option<(TypeIdx, Value, Option<BlockIdx>)> {
        // find matching effect in stack
        for (n, s) in self.scope.scopes.iter().enumerate().rev() {
            for &(ty, ref candidate, ref value, block) in s.effect_stack.iter().rev() {
                if ident.eq(candidate) {
                    return if n < self.capture_boundary.1 {
                        let idx = match self.captures.iter().position(|candidate| {
                            candidate
                                .as_ref()
                                .right()
                                .is_some_and(|candidate| ident.eq(candidate))
                        }) {
                            Some(idx) => idx,
                            None => {
                                let idx = self.captures.len();
                                self.captures.push(Either::Right(ident.clone()));
                                idx
                            }
                        };
                        Some((
                            ty,
                            Value::Deref(
                                Box::new(Value::Deref(Box::new(Value::Capture(idx)), true)),
                                false,
                            ),
                            None,
                        ))
                    } else {
                        Some((ty, value.clone(), block))
                    };
                }
            }
        }

        // find matching implied
        match ident {
            GenericVal::Literal(ident) => {
                ctx.ir.effects[ident.effect]
                    .implied
                    .clone()
                    .into_iter()
                    .find_map(|idx| {
                        let mut generic_params = GenericParams::new();

                        // check if matches yeetable
                        let fail = ctx.ir.handlers[idx].fail;
                        if let Some(yeetable) = self.yeetable {
                            ctx.infer_generics(&mut generic_params, yeetable, fail);
                            if !ctx
                                .translate_generics(fail, &generic_params, false)
                                .is_some_and(|ty| ctx.test_move(ty, yeetable))
                            {
                                return None;
                            }
                        } else if fail != TYPE_NEVER {
                            // if yeetable is unknown, assume never
                            return None;
                        }

                        // infer implied generics
                        for (candidate, target) in ctx.ir.handlers[idx]
                            .generic_params
                            .clone()
                            .into_iter()
                            .zip(ident.generic_params.iter())
                        {
                            ctx.infer_generics(&mut generic_params, target.1, candidate.1);
                            if !ctx
                                .translate_generics(candidate.1, &generic_params, false)
                                .is_some_and(|ty| ty == target.1)
                            {
                                return None;
                            }
                        }

                        // make sure we got all generics inferred
                        generic_params.sort_unstable_by_key(|(idx, _)| idx.0);
                        if !generic_params
                            .iter()
                            .map(|&(idx, _)| idx)
                            .eq(ctx.ir.handlers[idx]
                                .generics
                                .iter()
                                .map(|generic| generic.idx))
                        {
                            return None;
                        }

                        let metaty = ctx.insert_type(Type::HandlerType(HandlerType {
                            effect: GenericVal::Literal(ident.clone()),
                            fail_type: fail,
                        }));
                        let lazy = ctx.ir.lazy_handlers.push(
                            LazyIdx,
                            LazyValue::Some(GenericVal::Literal(HandlerIdent {
                                handler: idx,
                                generic_params: generic_params.clone(),
                                fail_type: fail,
                            })),
                        );
                        let ty = ctx.insert_type(Type::Handler(Lazy {
                            idx: lazy,
                            typeof_handler: metaty,
                        }));

                        if idx == ctx.srcloc {
                            let (start, _end) = get_lines(&ctx.errors.files[loc.3].content, loc);
                            let srcloc = [Value::ConstantString(
                                TYPE_STR,
                                format!(
                                    "{}:{}:{}",
                                    ctx.errors.files[loc.3].name,
                                    start.line + 1,
                                    start.column + 1
                                )
                                .into_bytes()
                                .into(),
                            )];
                            Some((
                                ty,
                                Value::ConstantHandler(ty, Rc::new(srcloc)),
                                self.yeetable_ret,
                            ))
                        } else {
                            Some((
                                ty,
                                Value::ConstantHandler(ty, Rc::new([])),
                                self.yeetable_ret,
                            ))
                        }
                    })
            }
            _ => None,
        }
    }
    fn define(&mut self, name: String, var: Variable) {
        self.scope.top().values.insert(name, var);
    }
    fn jump(&mut self) -> BlockIdx {
        let block = self.blocks.push(
            BlockIdx,
            Block {
                instructions: VecMap::new(),
                value: None,
            },
        );
        self.jump_to(block)
    }
    fn jump_to(&mut self, block: BlockIdx) -> BlockIdx {
        self.push(Instruction::Jump(block));

        let old = self.block;
        self.block = block;
        old
    }
    fn branch(
        &mut self,
        ctx: &mut SemCtx,
        cond: Value,
        yes: impl FnOnce(&mut SemCtx, &mut Self) -> Option<(Value, TypeIdx, Option<Range>)>,
        no: impl FnOnce(&mut SemCtx, &mut Self) -> Option<(Value, TypeIdx, Option<Range>)>,
    ) -> Option<(Value, TypeIdx)> {
        let yes_block = self.blocks.push(
            BlockIdx,
            Block {
                instructions: VecMap::new(),
                value: None,
            },
        );
        let no_block = self.blocks.push(
            BlockIdx,
            Block {
                instructions: VecMap::new(),
                value: None,
            },
        );

        self.push(Instruction::Branch(cond, yes_block, no_block));

        self.block = yes_block;
        let yes = yes(ctx, self);
        let yes_block = self.block;

        self.block = no_block;
        let no = no(ctx, self);
        let no_block = self.block;

        let end_block = self.blocks.push(
            BlockIdx,
            Block {
                instructions: VecMap::new(),
                value: None,
            },
        );

        self.block = yes_block;
        let (yval, yty, yloc) = match yes {
            Some((a, b, c)) => {
                self.push(Instruction::Jump(end_block));
                (a, b, c)
            }
            None => {
                self.push(Instruction::Unreachable);
                (Value::ConstantError, TYPE_NEVER, None)
            }
        };

        self.block = no_block;
        let (nval, nty, nloc) = match no {
            Some((a, b, c)) => {
                self.push(Instruction::Jump(end_block));
                (a, b, c)
            }
            None => {
                self.push(Instruction::Unreachable);
                (Value::ConstantError, TYPE_NEVER, None)
            }
        };

        self.block = end_block;
        let common = ctx.supertype(
            yty,
            nty,
            TypeRange {
                loc: nloc.or(yloc).unwrap_or(Ranged((), 0, 0, FileIdx(0))),
                def: nloc.and(yloc),
            },
        );

        let mut phi = Vec::new();
        if yty != TYPE_NEVER {
            phi.push((yval.clone(), yes_block));
        }
        if nty != TYPE_NEVER {
            phi.push((nval.clone(), no_block));
        }

        if phi.is_empty() {
            None
        } else if let [(val, _)] = phi.as_slice() {
            Some((val.clone(), common))
        } else {
            match (yval, nval) {
                (Value::ConstantNone, Value::ConstantNone) => Some((Value::ConstantNone, common)),
                _ => {
                    self.blocks[self.block].value = Some((common, phi));
                    Some((Value::Reg(self.block, None), common))
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
struct TypeRange {
    loc: Range,
    def: Option<Range>,
}

pub fn analyze(ast: &Ast, errors: &mut Errors, target: &Target) -> SemIR {
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
            structs: std::iter::repeat_with(Struct::default)
                .take(ast.structs.len())
                .collect(),

            types: VecSet::new(),
            handlers: VecMap::new(),
            lazy_handlers: VecMap::new(),

            generic_names: VecMap::new(),

            entry: FunIdx(0),
            foreign_handler: HandlerIdx(0),
        },
        ast,
        errors,
        packages: std::iter::repeat_with(Scope::default)
            .take(ast.packages.len())
            .collect(),
        srcloc: HandlerIdx(0),
    };

    ctx.insert_type(Type::Error);
    ctx.insert_type(Type::None);
    ctx.insert_type(Type::Never);
    ctx.insert_type(Type::DataType);
    ctx.insert_type(Type::EffectType);
    ctx.insert_type(Type::Integer(false, IntSize::Size));
    ctx.insert_type(Type::Bool);
    ctx.insert_type(Type::Integer(true, IntSize::Reg));
    ctx.insert_type(Type::Str);
    ctx.insert_type(Type::Char);
    ctx.insert_type(Type::Integer(false, IntSize::Bits(8)));
    ctx.insert_type(Type::Integer(false, IntSize::Ptr));

    let mut insert = |t: Type| {
        let ty = ctx.insert_type(t);
        let name = format!("{}", FmtType(&ctx.ir, ty));
        let name = String::from(&name[1..name.len() - 1]);
        let types = &mut ctx.packages[ast.preamble].types;
        types.insert(name, ty);
    };

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

    ctx.packages[ast.preamble]
        .types
        .insert("str".into(), TYPE_STR);

    ctx.packages[ast.preamble].values.insert(
        "true".into(),
        Variable {
            value: Value::ConstantBool(true),
            ty: TYPE_BOOL,
            mutable: false,
        },
    );
    ctx.packages[ast.preamble].values.insert(
        "false".into(),
        Variable {
            value: Value::ConstantBool(false),
            ty: TYPE_BOOL,
            mutable: false,
        },
    );

    // analyze struct names
    for (idx, package) in ast.packages.iter(PackageIdx) {
        for (i, struc) in package
            .structs
            .iter()
            .copied()
            .map(|idx| (idx, &ast.structs[idx]))
        {
            let name = &ast.idents[struc.name].0;
            ctx.ir.structs[i].name = name.clone();

            let ty = ctx.insert_type(Type::Struct(i));
            ctx.packages[idx].types.insert(name.clone(), ty);
        }
    }

    // analyze type aliases
    for (idx, package) in ast.packages.iter(PackageIdx) {
        let mut scope = ScopeStack::new(idx);
        for (id, ty) in package.aliases.iter().copied().map(|idx| ast.aliases[idx]) {
            let name = &ast.idents[id].0;
            let ty = ctx.analyze_type(&mut scope, ty, None, false, &mut SemCtx::no_handler);
            ctx.packages[idx].types.insert(name.clone(), ty);
        }
    }

    // analyze struct elems
    for (idx, package) in ast.packages.iter(PackageIdx) {
        let mut scope = ScopeStack::new(idx);
        for (i, struc) in package
            .structs
            .iter()
            .copied()
            .map(|idx| (idx, &ast.structs[idx]))
        {
            ctx.ir.structs[i].elems = struc
                .elems
                .iter()
                .map(|&(id, ty)| {
                    let name = ast.idents[id].0.clone();
                    let ty = ctx.analyze_type(&mut scope, ty, None, false, &mut SemCtx::no_handler);
                    (name, ty)
                })
                .collect();
        }
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
                    funs: VecMap::new(),
                    implied: Vec::new(),
                    capabilities: Vec::new(),
                    foreign: None,
                };

                // check if foreign
                if let Some(attr) = effect
                    .attributes
                    .iter()
                    .find(|a| ctx.ast.idents[a.name].0.eq("foreign"))
                {
                    let prefix = match attr
                        .settings
                        .iter()
                        .find(|&&(i, _)| ctx.ast.idents[i].0.eq("prefix"))
                    {
                        Some((_, AttributeValue::String(s))) => s.0.clone(),
                        Some((_, AttributeValue::Type(_))) => todo!("give error"),
                        None => String::new(),
                    };
                    ctx.ir.effects[i].foreign = Some(Foreign { prefix });
                }

                // add functions to scope
                for (fi, decl) in effect.functions.iter(EffFunIdx) {
                    let generic_params = ctx.ir.effects[i].generics.clone();
                    let generic_params = generic_params
                        .into_iter()
                        .map(|generic| (generic.idx, ctx.insert_type(Type::Generic(generic))))
                        .collect();
                    let sign = ctx.analyze_sign(
                        scope,
                        decl.name,
                        Some((
                            EffectIdent {
                                effect: i,
                                generic_params,
                            },
                            Some(fi),
                        )),
                        &decl.sign,
                    );
                    ctx.analyze_decl(decl, &sign, FunIdent::Effect(i, fi));
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
            let sign = ctx.analyze_sign(&mut scope, fun.decl.name, None, &fun.decl.sign);
            ctx.analyze_decl(&fun.decl, &sign, FunIdent::Top(i));
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
            }
        }
    }

    // analyze implied
    // FIXME: this doesn't allow implied handlers to use other implied handlers
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
    if ctx.errors.is_empty() {
        ctx.srcloc = ctx.ir.effects[*ctx.packages[ctx.ast.preamble]
            .effects
            .get("srcloc")
            .unwrap()
            .literal()
            .unwrap()]
        .implied[0];
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
            ctx.ir.fun_impl[i] = ctx.generate_function(
                Either::Left(i),
                fun.body,
                &mut scope,
                Some(TYPE_NEVER),
                None,
                &mut Vec::new(),
                true,
            );
        }
    }

    if ctx.errors.is_empty() {
        // define internal effects / functions
        ctx.define_preamble_fun("unreachable", |_, fun| {
            fun.push(Instruction::Unreachable);
        });
        ctx.define_preamble_fun("len", |ctx, fun| {
            let slice = Value::Param(ParamIdx(0));
            let slice_ty = ctx.get_preamble_sign("len").params[ParamIdx(0)].ty;
            let len = fun.push(Instruction::Member(slice, 1, slice_ty));
            fun.push(Instruction::Return(len));
        });
        ctx.define_preamble_fun("raw_slice", |ctx, fun| {
            let ptr = Value::Param(ParamIdx(0));
            let len = Value::Param(ParamIdx(1));
            let slice_ty = ctx.get_preamble_sign("raw_slice").return_type.ty;
            fun.push(Instruction::Return(Value::ConstantAggregate(
                slice_ty,
                vec![ptr, len].into(),
            )));
        });

        ctx.get_preamble_handler("srcloc").captures = vec![TYPE_STR];
        ctx.define_preamble_fun("source_location", |_, fun| {
            let capture = Value::Deref(Box::new(Value::Capture(0)), true);
            fun.push(Instruction::Return(capture));
        });

        let foreign = ctx.get_preamble_effect("foreign");
        let foreign_handler = ctx.push_handler(Handler {
            debug_name: "foreign_impl".into(),
            generics: Vec::new(),
            effect: foreign,
            generic_params: Vec::new(),
            fail: TYPE_NEVER,
            captures: Vec::new(),
            funs: vec![
                (
                    ctx.ir.effects[foreign].funs[EffFunIdx(0)].clone(),
                    FunImpl::default(),
                ),
                (
                    ctx.ir.effects[foreign].funs[EffFunIdx(1)].clone(),
                    FunImpl::default(),
                ),
                (
                    ctx.ir.effects[foreign].funs[EffFunIdx(2)].clone(),
                    FunImpl::default(),
                ),
            ]
            .into(),
        });
        ctx.ir.foreign_handler = foreign_handler;

        ctx.ir.effects[foreign].implied.push(foreign_handler);
        ctx.define_preamble_fun("impl_link", |ctx, fun| {
            let gen = &ctx.get_preamble_sign("impl_link").generics;
            let handler = fun.push(Instruction::LinkHandler(
                GenericVal::Generic(gen[1].idx),
                GenericVal::Generic(gen[0].idx),
            ));
            fun.push(Instruction::Return(handler));
        });
        ctx.define_preamble_fun("impl_asm", |ctx, fun| {
            let gen = &ctx.get_preamble_sign("impl_asm").generics;
            let handler = fun.push(Instruction::AsmHandler(
                GenericVal::Generic(gen[3].idx),
                GenericVal::Generic(gen[0].idx),
                GenericVal::Generic(gen[1].idx),
                GenericVal::Generic(gen[2].idx),
            ));
            fun.push(Instruction::Return(handler));
        });
        ctx.define_preamble_fun("syscall", |_, fun| {
            let ret = fun.push(Instruction::Syscall(
                Value::Param(ParamIdx(0)),
                Value::Param(ParamIdx(1)),
            ));
            fun.push(Instruction::Return(ret));
        });
        ctx.ir.effects[foreign].implied.clear();

        // Implement trace/trap_silent via os.process
        let mut cap_fun = FunCtx {
            scope: &mut ScopeStack::new(ctx.ast.preamble),
            yeetable: None,
            yeetable_def: None,
            yeetable_ret: None,
            blocks: vec![Block::default()].into(),
            block: BlockIdx(0),
            capture_boundary: (true, 0),
            captures: &mut Vec::new(),
        };

        let mut cache = HashMap::new();
        let metaty = ctx.insert_type(Type::HandlerType(HandlerType {
            effect: GenericVal::Literal(EffectIdent {
                effect: foreign,
                generic_params: Vec::new(),
            }),
            fail_type: TYPE_NEVER,
        }));
        let foreign_lazy = ctx.ir.lazy_handlers.push(
            LazyIdx,
            LazyValue::Some(GenericVal::Literal(HandlerIdent {
                handler: foreign_handler,
                generic_params: Vec::new(),
                fail_type: TYPE_NEVER,
            })),
        );
        let ty = ctx.insert_type(Type::Handler(Lazy {
            idx: foreign_lazy,
            typeof_handler: metaty,
        }));
        cache.insert(
            EffectIdent {
                effect: foreign,
                generic_params: Vec::new(),
            },
            (ty, Value::ConstantHandler(ty, Rc::new([]))),
        );

        let process_idx = ctx.packages[ctx.ast.system]
            .effects
            .get("process")
            .map(|s| *s.literal().unwrap());
        let process = process_idx.and_then(|idx| {
            Some((
                idx,
                ctx.get_capability(
                    target,
                    &mut cap_fun,
                    &mut cache,
                    EffectIdent {
                        effect: idx,
                        generic_params: Vec::new(),
                    },
                )?,
            ))
        });
        if let Some((idx, val)) = process.clone() {
            ctx.define_preamble_fun("trap_silent", |ctx, fun| {
                fun.blocks = cap_fun.blocks.clone();
                fun.block = cap_fun.block;

                let gen = ctx.ir.effects[idx].funs[EffFunIdx(0)].generics[0].idx;
                fun.push(Instruction::Call(
                    // os.abort
                    FunIdent::Effect(idx, EffFunIdx(0)),
                    vec![(gen, val.0)],
                    Vec::new(),
                    vec![val.1.clone()],
                    Vec::new(),
                ));
                fun.push(Instruction::Unreachable);
            });
            ctx.define_preamble_fun("trace", |ctx, fun| {
                fun.blocks = cap_fun.blocks.clone();
                fun.block = cap_fun.block;

                let gen = ctx.ir.effects[idx].funs[EffFunIdx(2)].generics[0].idx;
                let handler = fun.push(Instruction::Call(
                    // os.stdio
                    FunIdent::Effect(idx, EffFunIdx(2)),
                    vec![(gen, val.0)],
                    Vec::new(),
                    vec![val.1.clone()],
                    Vec::new(),
                ));
                let ty = ctx.ir.effects[idx].funs[EffFunIdx(2)].return_type.ty;
                let ty = ctx
                    .translate_generics(ty, &vec![(gen, val.0)], true)
                    .unwrap();
                let handler = fun.push_deref(false, Instruction::Reference(handler, ty));

                let io = ctx.ast.packages[ctx.ast.system].imports["io"];
                let print = ctx.packages[io].funs["print"];

                let gen = print.sign(&ctx.ir).generics[0].idx;
                fun.push(Instruction::Call(
                    // stdio.print
                    print,
                    vec![(gen, ty)],
                    vec![Value::Param(ParamIdx(0))],
                    vec![handler],
                    Vec::new(),
                ));
                fun.push(Instruction::Return(Value::ConstantNone));
            });
        }

        // Main function
        let main = ctx.packages[ctx.ast.main].funs.get("main").copied();
        match main {
            Some(main) => {
                let stack = main
                    .sign(&ctx.ir)
                    .effect_stack
                    .clone()
                    .into_iter()
                    .map(|ident| {
                        let ident = ident.0 .1.literal().unwrap();
                        ctx.get_capability(target, &mut cap_fun, &mut cache, ident.clone())
                    })
                    .collect::<Option<Vec<_>>>();

                match stack {
                    Some(stack) => {
                        let generics = &main.sign(&ctx.ir).generics;
                        cap_fun.push(Instruction::Call(
                            main,
                            generics
                                .iter()
                                .zip(stack.iter())
                                .map(|(gen, v)| (gen.idx, v.0))
                                .collect(),
                            Vec::new(),
                            stack.into_iter().map(|(_, val)| val).collect(),
                            Vec::new(),
                        ));
                    }
                    None => panic!("give error"),
                }
            }
            None => {
                panic!("give error");
            }
        }

        if let Some((idx, val)) = process {
            // os.exit
            let gen = ctx.ir.effects[idx].funs[EffFunIdx(2)].generics[0].idx;
            cap_fun.push(Instruction::Call(
                FunIdent::Effect(idx, EffFunIdx(1)),
                vec![(gen, val.0)],
                vec![Value::ConstantInt(TYPE_INT, false, 0)],
                vec![val.1],
                Vec::new(),
            ));
            cap_fun.push(Instruction::Unreachable);
        } else {
            cap_fun.push(Instruction::Return(Value::ConstantNone));
        }

        let start = ctx.ir.fun_sign.push(
            FunIdx,
            FunSign {
                def: None,
                name: "_start".into(),
                generics: Vec::new(),
                params: Vec::new().into(),
                effect_stack: Vec::new(),
                return_type: ReturnType {
                    type_def: None,
                    ty: TYPE_NONE,
                },
            },
        );
        ctx.ir.fun_impl.push_value(FunImpl {
            blocks: cap_fun.blocks,
        });
        ctx.ir.entry = start;

        // remove LazyValue::Refer
        let mut modified = true;
        while modified {
            modified = false;
            for idx in (0..ctx.ir.lazy_handlers.len()).map(LazyIdx) {
                if let LazyValue::Refer(refidx, ref params) = ctx.ir.lazy_handlers[idx] {
                    let params = params.clone();
                    let handler = match get_lazy_reg(&mut ctx, refidx, params) {
                        Some(value) => value,
                        None => continue,
                    };

                    ctx.ir.lazy_handlers[idx] = handler;
                    modified = true;
                }
            }
        }
        for value in ctx.ir.lazy_handlers.values_mut() {
            if matches!(value, LazyValue::Refer(_, _)) {
                *value = LazyValue::None;
            }
        }
    }

    ctx.ir
}

fn get_lazy_reg(
    ctx: &mut SemCtx<'_>,
    refidx: LazyIdx,
    params: Option<Vec<(GenericIdx, TypeIdx)>>,
) -> Option<LazyValue> {
    let handler = match ctx.ir.lazy_handlers[refidx] {
        LazyValue::Some(GenericVal::Literal(ref handler)) => {
            let handler = handler.clone();
            LazyValue::Some(GenericVal::Literal(match params {
                Some(params) => HandlerIdent {
                    handler: handler.handler,
                    generic_params: handler
                        .generic_params
                        .into_iter()
                        .map(|(idx, ty)| (idx, ctx.translate_generics(ty, &params, false).unwrap()))
                        .collect(),
                    fail_type: ctx
                        .translate_generics(handler.fail_type, &params, false)
                        .unwrap(),
                },
                None => handler,
            }))
        }
        LazyValue::Some(GenericVal::Generic(genericidx)) => match params {
            Some(params) => match ctx.ir.types[get_param(&params, genericidx).unwrap()] {
                Type::Handler(lazy) => ctx.ir.lazy_handlers[lazy.idx].clone(),
                Type::Generic(idx) => LazyValue::Some(GenericVal::Generic(idx.idx)),
                Type::Error => LazyValue::None,
                _ => unreachable!(),
            },
            None => LazyValue::Some(GenericVal::Generic(genericidx)),
        },
        LazyValue::EffectFunOutput(lazy, fun, ref ps) => match params {
            Some(params) => {
                let ps = ps
                    .clone()
                    .into_iter()
                    .map(|(idx, ty)| (idx, ctx.translate_generics(ty, &params, false).unwrap()))
                    .collect();
                let lazy = get_lazy_reg(ctx, lazy, Some(params))?;
                let lazy = ctx.ir.lazy_handlers.push(LazyIdx, lazy);
                LazyValue::EffectFunOutput(lazy, fun, ps)
            }
            None => LazyValue::EffectFunOutput(lazy, fun, ps.clone()),
        },
        _ => return None,
    };
    Some(handler)
}
