use std::{
    collections::HashMap,
    fmt::{self},
    rc::Rc,
};

use either::Either;

use crate::{
    ast::{
        self, BinOp, EffFunIdx, EffIdx, ExprIdx, Expression, Ident, PackageIdx, ParamIdx, UnOp, AST,
    },
    error::{Error, Errors, FileIdx, Range, Ranged},
    sema::Instruction,
    vecmap::{VecMap, VecSet},
    Target,
};

use super::{
    get_param, Block, BlockIdx, Effect, EffectIdent, EffectType, FunIdx, FunImpl, FunSign, Generic,
    GenericIdx, GenericParams, GenericVal, Generics, Handler, HandlerIdx, InstrIdx, IntSize, Lazy,
    LazyIdx, Param, ReturnType, SemIR, Type, TypeIdx, Value,
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
    fn get_value(&self, ctx: &SemCtx, name: &str) -> Option<Variable> {
        self.search(ctx, |s| s.values.get(name).cloned())
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
}

const TYPE_ERROR: TypeIdx = TypeIdx(0 << 2);
const TYPE_NONE: TypeIdx = TypeIdx(1 << 2);
const TYPE_NEVER: TypeIdx = TypeIdx(2 << 2);
const TYPE_DATATYPE: TypeIdx = TypeIdx(3 << 2);
const TYPE_EFFECT: TypeIdx = TypeIdx(4 << 2);
const TYPE_USIZE: TypeIdx = TypeIdx(5 << 2);
const TYPE_BOOL: TypeIdx = TypeIdx(6 << 2);
const TYPE_INT: TypeIdx = TypeIdx(7 << 2);
const TYPE_STR: TypeIdx = TypeIdx(8 << 2);
const TYPE_CHAR: TypeIdx = TypeIdx(9 << 2);
const TYPE_U8: TypeIdx = TypeIdx(10 << 2);

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
    fn lazy_handler(
        &mut self,
        _: &mut Generics,
        typeof_handler: TypeIdx,
        _: ast::TypeIdx,
    ) -> TypeIdx {
        let idx = self.ir.lazy_handlers.push(LazyIdx, None);
        self.insert_type(
            Type::Handler(Lazy {
                idx,
                typeof_handler,
            }),
            false,
            false,
        )
    }
    fn no_handler(&mut self, _: &mut Generics, _: TypeIdx, ty: ast::TypeIdx) -> TypeIdx {
        self.errors
            .push(self.ast.types[ty].with(Error::NotEnoughInfo));
        TYPE_ERROR
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
    fn translate_generics(&mut self, ty: TypeIdx, generic_params: &GenericParams) -> TypeIdx {
        let translate_generic =
            |ctx: &mut Self, generic: Generic| match get_param(generic_params, generic.idx) {
                Some(ty) => match ctx.ir.types[ty] {
                    Type::Generic(generic) => generic,
                    _ => todo!(),
                },
                None => generic,
            };
        match self.ir.types[ty] {
            Type::Handler(lazy) => {
                let typeof_handler = self.translate_generics(lazy.typeof_handler, generic_params);
                self.insert_type(
                    Type::Handler(Lazy {
                        idx: lazy.idx,
                        typeof_handler,
                    }),
                    ty.is_const(),
                    ty.is_lent(),
                )
            }
            Type::HandlerType(ref effect_type) => {
                let eft = effect_type.fail_type;

                let effect = match effect_type.effect {
                    GenericVal::Literal(ref ident) => {
                        let ie = ident.effect;

                        let params = ident.generic_params.clone();
                        let params = params
                            .into_iter()
                            .map(|(idx, ty)| (idx, self.translate_generics(ty, generic_params)))
                            .collect::<Vec<_>>();
                        GenericVal::Literal(EffectIdent {
                            effect: ie,
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
                let fail_type = self.translate_generics(eft, generic_params);
                self.insert_type(
                    Type::HandlerType(EffectType { effect, fail_type }),
                    ty.is_const(),
                    ty.is_lent(),
                )
            }
            Type::Generic(generic) => match get_param(generic_params, generic.idx) {
                Some(ty) => ty,
                None => ty,
            },
            Type::Pointer(inner) => {
                let inner = self.translate_generics(inner, generic_params);
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
                let inner = self.translate_generics(inner, generic_params);
                self.insert_type(Type::ConstArray(size, inner), ty.is_const(), ty.is_lent())
            }
            Type::Slice(inner) => {
                let inner = self.translate_generics(inner, generic_params);
                self.insert_type(Type::Slice(inner), ty.is_const(), ty.is_lent())
            }

            Type::Effect
            | Type::DataType
            | Type::Integer(_, _)
            | Type::Str
            | Type::Char
            | Type::Bool
            | Type::None
            | Type::Error
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
                };

                // create handler type
                let typeof_handler = self.insert_type(
                    Type::HandlerType(EffectType {
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
                    }),
                    false,
                    false,
                );

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
                            .push(LazyIdx, Some(Either::Left(GenericVal::Generic(value.idx))));
                        self.insert_type(
                            Type::Handler(Lazy {
                                idx: lazy,
                                typeof_handler,
                            }),
                            false,
                            false,
                        )
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
                Some(generic) => self.insert_type(Type::Generic(generic), false, false),
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
                let typeof_handler = self.insert_type(
                    Type::HandlerType(EffectType { effect, fail_type }),
                    false,
                    false,
                );
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
                            .push(LazyIdx, Some(Either::Left(GenericVal::Generic(value.idx))));
                        self.insert_type(
                            Type::Handler(Lazy {
                                idx: lazy,
                                typeof_handler,
                            }),
                            false,
                            false,
                        )
                    }
                    None => handler_output(
                        self,
                        generics.unwrap_or(&mut Vec::new()),
                        typeof_handler,
                        ty,
                    ),
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
                            None => return TYPE_ERROR,
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
        effect: Option<EffectIdent>,
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
                    let ty = match self.analyze_generic(scope, param.name, ty, Some(&mut generics))
                    {
                        Some(generic) => self.insert_type(Type::Generic(generic), false, false),
                        None => TYPE_ERROR,
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
                        match effect {
                            GenericVal::Literal(effect) => {
                                // TODO: check parameter count
                                handler_params.push(GenericVal::Literal(EffectIdent {
                                    effect,
                                    generic_params: self.ir.effects[effect]
                                        .generics
                                        .iter()
                                        .map(|generic| generic.idx)
                                        .zip(effect_params)
                                        .collect(),
                                }))
                            }
                            GenericVal::Generic(idx) => {
                                // TODO: params must be empty
                                handler_params.push(GenericVal::Generic(idx))
                            }
                        }
                    }
                    None => {}
                }
            }

            // parent handler
            if let Some(effect) = effect {
                handler_params.push(GenericVal::Literal(effect));
            }

            // return type
            let return_type = match fun.output {
                Some(ty) => self.analyze_type(
                    scope,
                    ty,
                    Some(&mut generics),
                    false,
                    &mut SemCtx::lazy_handler, // TODO
                ),
                None => TYPE_NONE,
            };

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
    fn check_sign(&mut self, a: &FunSign, b: FunIdent, generic_params: &GenericParams) {
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
            let translated = self.translate_generics(b.ty, generic_params);
            self.check_move(
                translated,
                a.ty,
                TypeRange {
                    loc: b.type_def,
                    def: Some(a.type_def),
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
                    Some(EffectIdent {
                        effect,
                        generic_params: generic_params.clone(),
                    }),
                    &function.decl.sign,
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
                    Some((idx, _)) => funs[idx] = (sign, imp),
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
                    continue;
                };

                // check sign mismatch
                self.check_sign(&sign, FunIdent::Effect(effect, idx), &generic_params);
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
    fn check_move(&mut self, a: TypeIdx, b: TypeIdx, loc: TypeRange) {
        if !self.test_move(a, b) {
            self.errors.push(loc.loc.with(Error::TypeMismatch(
                loc.def,
                format!("{}", FmtType(&self.ir, a)),
                format!("{}", FmtType(&self.ir, b)),
            )));
        }
    }
    fn test_move(&mut self, from: TypeIdx, to: TypeIdx) -> bool {
        if from == to {
            return true;
        }
        if (to.is_const() && !from.is_const()) || (to.is_lent() && !from.is_lent()) {
            let from = from.with(to.is_const(), to.is_lent());
            return self.test_move(from, to);
        }
        match (&self.ir.types[from], &self.ir.types[to]) {
            (Type::Never, _) => true,

            (Type::Error, _) => true,
            (_, Type::Error) => true,

            (Type::HandlerType(from), Type::HandlerType(to)) => {
                from.effect == to.effect && self.test_move(from.fail_type, to.fail_type)
            }

            (&Type::Handler(from), &Type::Handler(to)) => {
                if self.test_move(from.typeof_handler, to.typeof_handler) {
                    let from_last = self.ir.lazy_last(from.idx);
                    let to_last = self.ir.lazy_last(to.idx);
                    match (from_last, to_last) {
                        (_, None) => {
                            *self.ir.lazy_last_mut(to.idx) = Some(Either::Right(from.idx));
                            true
                        }
                        (None, _) => {
                            *self.ir.lazy_last_mut(from.idx) = Some(Either::Right(to.idx));
                            true
                        }
                        (Some(Either::Left(from)), Some(Either::Left(to))) if from == to => true,
                        _ => false,
                    }
                } else {
                    // incorrect meta-type
                    false
                }
            }

            _ => false,
        }
    }
    fn typeof_ty(&mut self, ty: TypeIdx) -> TypeIdx {
        match self.ir.types[ty] {
            Type::Generic(generic) => generic.typeof_ty,

            Type::Handler(_) => TYPE_DATATYPE,
            Type::Pointer(_) => TYPE_DATATYPE,
            Type::ConstArray(_, _) => TYPE_DATATYPE,
            Type::Slice(_) => TYPE_DATATYPE,
            Type::Integer(_, _) => TYPE_DATATYPE,
            Type::Str => TYPE_DATATYPE,
            Type::Char => TYPE_DATATYPE,
            Type::Bool => TYPE_DATATYPE,
            Type::None => TYPE_DATATYPE,

            Type::Never => TYPE_NEVER,
            Type::Error => TYPE_ERROR,

            Type::DataType => todo!(),
            Type::Effect => todo!(),
            Type::HandlerType(_) => todo!(),
        }
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

            let mut blocks = VecMap::new();
            let block = blocks.push(BlockIdx, Block::default());
            let mut fun_ctx = FunCtx {
                scope,
                blocks,
                block,
                yeetable,
                yeetable_def,
            };

            for (idx, param) in ir_sign.params.iter(ParamIdx) {
                if param.mutable {
                    let value = fun_ctx.push_ref(Instruction::Reference(Value::Param(idx)));
                    fun_ctx.define(
                        param.name.clone(),
                        Variable {
                            value,
                            ty: param.ty,
                            mutable: param.mutable,
                        },
                    );
                } else {
                    fun_ctx.define(
                        param.name.clone(),
                        Variable {
                            value: Value::Param(idx),
                            ty: param.ty,
                            mutable: param.mutable,
                        },
                    );
                }
            }
            for generic in ir_sign.generics.iter() {
                fun_ctx
                    .scope
                    .top()
                    .generics
                    .insert(self.ir.generic_names[generic.idx].clone(), generic.clone());
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
            (&E::Array(ref exprs), &Type::Slice(elem)) => {
                let elems = exprs
                    .iter()
                    .copied()
                    .map(|expr| self.check_expr(ctx, expr, elem, expected_def))
                    .collect::<Option<Rc<[_]>>>()?;
                let len = elems.len() as u64;

                let arr = Value::ConstantAggregate(elems);
                let ptr = ctx.push(Instruction::Reference(arr));
                let slice =
                    Value::ConstantAggregate(vec![ptr, Value::ConstantInt(false, len)].into());
                Some(slice)
            }
            (&E::Array(ref exprs), &Type::ConstArray(GenericVal::Literal(n), elem))
                if n == exprs.len() as u64 =>
            {
                let elems = exprs
                    .iter()
                    .copied()
                    .map(|expr| self.check_expr(ctx, expr, elem, expected_def))
                    .collect::<Option<Rc<[_]>>>()?;
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
                Some(Value::ConstantString(str.as_str().into()))
            }
            (&E::UnOp(inner, UnOp::Cast), _) => {
                // TODO: test if allowed
                let (value, ty) = self.synth_expr(ctx, inner)?;
                let instr = ctx.blocks[ctx.block]
                    .instructions
                    .push(InstrIdx, Instruction::Cast(value.clone(), expected));

                if matches!(value, Value::Reference(_, _)) {
                    Some(Value::Reference(ctx.block, Some(instr)))
                } else {
                    Some(Value::Reg(ctx.block, Some(instr)))
                }
            }
            _ => {
                let (found, found_ty) = self.synth_expr(ctx, expr)?;
                self.check_move(found_ty, expected, error_loc);
                Some(found)
            }
        }
    }
    fn assignable_expr(&mut self, ctx: &mut FunCtx, expr: ExprIdx) -> Option<(Value, TypeIdx)> {
        use Expression as E;
        match self.ast.exprs[expr].0 {
            E::BinOp(left, BinOp::Index, right) => {
                let right = self.check_expr(ctx, right, TYPE_USIZE, None)?;
                let (value, ty) = self.assignable_expr(ctx, left)?;

                let (ptr, elem_ty) = match self.ir.types[ty] {
                    Type::ConstArray(_, inner) => (value, inner),
                    Type::Slice(inner) => {
                        let slice = ctx.push(Instruction::Load(value));
                        let ptr = ctx.push(Instruction::Member(slice, 0));
                        (ptr, inner)
                    }
                    Type::Error => {
                        return Some((Value::ConstantError, TYPE_ERROR));
                    }
                    _ => todo!("give error"),
                };

                let elem = ctx.push_ref(Instruction::AdjacentPtr(ptr, right));
                Some((elem, elem_ty))
            }
            E::Ident(id) => {
                let name = &self.ast.idents[id].0;
                match ctx.get_value(self, name) {
                    Some(var) => {
                        if var.mutable {
                            // mutable variables must always be references
                            Some((var.value, var.ty))
                        } else {
                            todo!("give error")
                        }
                    }
                    None => {
                        self.errors
                            .push(self.ast.idents[id].with(Error::UnknownValue));
                        Some((Value::ConstantError, TYPE_ERROR))
                    }
                }
            }
            E::Error => Some((Value::ConstantError, TYPE_ERROR)),
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
                let old = ctx.jump();
                self.synth_expr(ctx, inner)?;
                ctx.push(Instruction::Jump(old));
                None
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

            E::TryWith(_, _) => {
                ctx.push(Instruction::Trap);
                Some((Value::ConstantError, TYPE_ERROR))
            }
            E::Handler(_) => {
                ctx.push(Instruction::Trap);
                Some((Value::ConstantError, TYPE_ERROR))
            }
            E::Call(_, _) => {
                ctx.push(Instruction::Trap);
                Some((Value::ConstantError, TYPE_ERROR))
            }

            E::BinOp(left, BinOp::Assign, right) => {
                let (value, ty) = self.assignable_expr(ctx, left)?;
                let right = self.check_expr(ctx, right, ty, None)?;
                ctx.push(Instruction::Store(value, right));

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
                    Type::Error => {
                        return Some((Value::ConstantError, TYPE_ERROR));
                    }
                    _ => todo!("give error"),
                };

                if let E::BinOp(rleft, BinOp::Range, rright) = self.ast.exprs[right].0 {
                    let rleft = self.check_expr(ctx, rleft, TYPE_USIZE, None)?;
                    let rright = self.check_expr(ctx, rright, TYPE_USIZE, None)?;

                    let ptr = ctx.push(Instruction::AdjacentPtr(ptr, rleft.clone()));
                    let len = ctx.push(Instruction::Sub(rright, rleft));

                    let slice = Value::ConstantAggregate(vec![ptr, len].into());
                    let slice_ty = self.insert_type(Type::Slice(elem_ty), false, true);
                    Some((slice, slice_ty))
                } else {
                    let right = self.check_expr(ctx, right, TYPE_USIZE, None)?;
                    let elem = ctx.push(Instruction::AdjacentPtr(ptr, right));
                    Some((elem, elem_ty))
                }
            }
            E::BinOp(_, BinOp::Range, _) => {
                todo!("give error")
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
            E::UnOp(inner, UnOp::PostIncrement) => {
                let (value, ty) = self.assignable_expr(ctx, inner)?;

                // TODO: check if integer type
                let loaded = ctx.push(Instruction::Load(value.clone()));
                let incremented = ctx.push(Instruction::Add(
                    loaded.clone(),
                    Value::ConstantInt(false, 1),
                ));
                ctx.push(Instruction::Store(value, incremented));

                Some((loaded, ty))
            }
            E::UnOp(inner, UnOp::Reference) => {
                // TODO: also make this work for non-mutable variables? (const pointer)

                let (value, ty) = self.assignable_expr(ctx, inner)?;
                match value {
                    Value::Reference(block, instr) => {
                        let ptr_ty = self.insert_type(Type::Pointer(ty), false, true);
                        Some((Value::Reg(block, instr), ptr_ty))
                    }
                    Value::ConstantError => Some((value, ty)),
                    _ => unreachable!(),
                }
            }
            E::UnOp(_, UnOp::Cast) => {
                self.errors
                    .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                Some((Value::ConstantUninit, TYPE_ERROR))
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

                if mutable {
                    let ptr = ctx.push_ref(Instruction::Reference(value));
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
                        Some((Value::ConstantUninit, TYPE_ERROR))
                    }
                }
            }
            E::String(ref str) => Some((Value::ConstantString(str.as_str().into()), TYPE_STR)),
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
                        Some((Value::ConstantError, TYPE_ERROR))
                    }
                }
            }
            E::Int(n) => Some((Value::ConstantInt(false, n), TYPE_INT)),
            E::Uninit => {
                self.errors
                    .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                Some((Value::ConstantUninit, TYPE_ERROR))
            }
            E::Error => Some((Value::ConstantError, TYPE_ERROR)),
            E::Member(_, _) => todo!(),
        }
    }
}

struct FunCtx<'a> {
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
    fn push(&mut self, instr: Instruction) -> Value {
        let idx = self.blocks[self.block].instructions.push(InstrIdx, instr);
        Value::Reg(self.block, Some(idx))
    }
    fn push_ref(&mut self, instr: Instruction) -> Value {
        let idx = self.blocks[self.block].instructions.push(InstrIdx, instr);
        Value::Reference(self.block, Some(idx))
    }
    fn get_value(&self, ctx: &SemCtx, name: &str) -> Option<Variable> {
        self.scope.get_value(ctx, name)
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
        let end_block = self.blocks.push(
            BlockIdx,
            Block {
                instructions: VecMap::new(),
                value: None,
            },
        );

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
        let (yval, yty, yloc) = match yes(ctx, self) {
            Some((a, b, c)) => {
                self.push(Instruction::Jump(end_block));
                (a, b, c)
            }
            None => (Value::ConstantError, TYPE_NEVER, None),
        };

        self.block = no_block;
        let (nval, nty, nloc) = match no(ctx, self) {
            Some((a, b, c)) => {
                self.push(Instruction::Jump(end_block));
                (a, b, c)
            }
            None => (Value::ConstantError, TYPE_NEVER, None),
        };

        self.block = end_block;
        let common = ctx.supertype(
            yty,
            nty,
            TypeRange {
                loc: nloc.or(yloc).unwrap_or(Ranged((), 0, 0, FileIdx(0))),
                def: nloc.and_then(|_| yloc),
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
                (Value::Reference(_, _), Value::Reference(_, _)) => {
                    self.blocks[self.block].value = Some(phi);
                    Some((Value::Reference(self.block, None), common))
                }
                _ => {
                    self.blocks[self.block].value = Some(phi);
                    Some((Value::Reg(self.block, None), common))
                }
            }
        }
    }
}

type ExprResult = Option<Value>;

#[derive(Clone)]
struct TypeRange {
    loc: Range,
    def: Option<Range>,
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
        },
        ast,
        errors,
        packages: std::iter::repeat_with(Scope::default)
            .take(ast.packages.len())
            .collect(),
    };

    ctx.insert_type(Type::Error, false, false);
    ctx.insert_type(Type::None, false, false);
    ctx.insert_type(Type::Never, false, false);
    ctx.insert_type(Type::DataType, false, false);
    ctx.insert_type(Type::Effect, false, false);
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
                    funs: VecMap::new(),
                    implied: Vec::new(),
                };

                // add functions to scope
                for (fi, decl) in effect.functions.iter(EffFunIdx) {
                    let generic_params = ctx.ir.effects[i].generics.clone();
                    let generic_params = generic_params
                        .into_iter()
                        .map(|generic| {
                            (
                                generic.idx,
                                ctx.insert_type(Type::Generic(generic), false, false),
                            )
                        })
                        .collect();
                    let sign = ctx.analyze_sign(
                        scope,
                        decl.name,
                        Some(EffectIdent {
                            effect: i,
                            generic_params,
                        }),
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
            let sign = ctx.analyze_sign(&mut scope, fun.decl.name, None, &fun.decl.sign);
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
