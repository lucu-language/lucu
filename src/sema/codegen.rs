use std::{
    collections::HashMap,
    fmt::{self},
    rc::Rc,
};

use either::Either;

use crate::{
    ast::{
        self, Ast, BinOp, EffFunIdx, EffIdx, ExprIdx, Expression, Ident, PackageIdx, ParamIdx, UnOp,
    },
    error::{Error, Errors, FileIdx, Range, Ranged},
    sema::{Capture, HandlerIdent, Instruction},
    vecmap::{VecMap, VecSet},
};

use super::{
    get_param, Block, BlockIdx, Effect, EffectIdent, FunIdent, FunIdx, FunImpl, FunSign, Generic,
    GenericIdx, GenericParams, GenericVal, Generics, Handler, HandlerIdx, HandlerType, InstrIdx,
    IntSize, Lazy, LazyIdx, LazyValue, Param, ReturnType, SemIR, Type, TypeIdx, Value,
};

impl FunIdent {
    fn ident(self, ctx: &SemCtx) -> Ident {
        match self {
            FunIdent::Top(idx) => ctx.ast.functions[idx].decl.name,
            FunIdent::Effect(eff, idx) => ctx.ast.effects[eff].functions[idx].name,
        }
    }
}

impl Value {
    fn inner_ptr(self) -> Value {
        match self {
            Value::Deref(value) => *value,
            Value::ConstantError => self,
            _ => unreachable!(),
        }
    }
}

struct SemCtx<'a> {
    ir: SemIR,
    ast: &'a Ast,
    errors: &'a mut Errors,
    packages: VecMap<PackageIdx, Scope>,
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

    effect_stack: Vec<(GenericVal<EffectIdent>, Value, Option<BlockIdx>)>,
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

const TYPE_ERROR: TypeIdx = TypeIdx(0 << 2);
const TYPE_NONE: TypeIdx = TypeIdx(1 << 2);
const TYPE_NEVER: TypeIdx = TypeIdx(2 << 2);
const TYPE_DATATYPE: TypeIdx = TypeIdx(3 << 2);
const TYPE_EFFECT: TypeIdx = TypeIdx(4 << 2);
const TYPE_USIZE: TypeIdx = TypeIdx(5 << 2);
const TYPE_BOOL: TypeIdx = TypeIdx(6 << 2);
const TYPE_INT: TypeIdx = TypeIdx(7 << 2);
const TYPE_STR: TypeIdx = TypeIdx((8 << 2) | 1); // const
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
    fn to_generic_params(&mut self, generics: &[Generic]) -> GenericParams {
        generics
            .iter()
            .map(|&g| (g.idx, self.insert_type(Type::Generic(g), false)))
            .collect()
    }
    fn child_ty(&self, elem: TypeIdx, parent: TypeIdx) -> TypeIdx {
        if self.is_copy(elem) {
            elem
        } else {
            elem.with_const(parent.is_const() || elem.is_const())
        }
    }
    fn lazy_handler(
        &mut self,
        _: &mut Generics,
        typeof_handler: TypeIdx,
        _: ast::TypeIdx,
    ) -> TypeIdx {
        let idx = self.ir.lazy_handlers.push(LazyIdx, LazyValue::None);
        self.insert_type(
            Type::Handler(Lazy {
                idx,
                typeof_handler,
            }),
            false,
        )
    }
    fn no_handler(&mut self, _: &mut Generics, _: TypeIdx, ty: ast::TypeIdx) -> TypeIdx {
        self.errors
            .push(self.ast.types[ty].with(Error::NotEnoughInfo));
        TYPE_ERROR
    }
    fn insert_type(&mut self, ty: Type, is_const: bool) -> TypeIdx {
        self.ir
            .types
            .insert(|idx| TypeIdx::new(idx, false), ty)
            .with_const(is_const)
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
                    self.insert_type(
                        Type::Handler(Lazy {
                            idx,
                            typeof_handler,
                        }),
                        ty.is_const(),
                    )
                } else {
                    let idx = self.ir.lazy_handlers.push(LazyIdx, LazyValue::None);
                    self.insert_type(
                        Type::Handler(Lazy {
                            idx,
                            typeof_handler,
                        }),
                        ty.is_const(),
                    )
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

                self.insert_type(
                    Type::Effect(EffectIdent {
                        effect: ie,
                        generic_params: params,
                    }),
                    ty.is_const(),
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
                self.insert_type(
                    Type::HandlerType(HandlerType { effect, fail_type }),
                    ty.is_const(),
                )
            }
            Type::Generic(generic) => match get_param(generic_params, generic.idx) {
                Some(ty) => ty,
                None => None?,
            },
            Type::Pointer(inner) => {
                let inner = self.translate_generics(inner, generic_params, translate_lazy)?;
                self.insert_type(Type::Pointer(inner), ty.is_const())
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
                self.insert_type(Type::ConstArray(size, inner), ty.is_const())
            }
            Type::Slice(inner) => {
                let inner = self.translate_generics(inner, generic_params, translate_lazy)?;
                self.insert_type(Type::Slice(inner), ty.is_const())
            }

            Type::EffectType
            | Type::DataType
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
                let typeof_handler = self.insert_type(
                    Type::HandlerType(HandlerType {
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
                            .push(LazyIdx, LazyValue::Some(GenericVal::Generic(value.idx)));
                        self.insert_type(
                            Type::Handler(Lazy {
                                idx: lazy,
                                typeof_handler,
                            }),
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
                Some(generic) => self.insert_type(Type::Generic(generic), false),
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
                    self.insert_type(Type::HandlerType(HandlerType { effect, fail_type }), false);
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
                        self.insert_type(
                            Type::Handler(Lazy {
                                idx: lazy,
                                typeof_handler,
                            }),
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
                self.insert_type(Type::Pointer(inner), false)
            }
            T::Const(ty) => self
                .analyze_type(scope, ty, generics, generic_handler, handler_output)
                .with_const(true),
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
                self.insert_type(Type::ConstArray(size, inner), false)
            }
            T::Slice(ty) => {
                let inner = self.analyze_type(scope, ty, generics, generic_handler, handler_output);
                self.insert_type(Type::Slice(inner), false)
            }
            T::ConstExpr(_) => todo!(),
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
                let ty = ty.with_const((!param.mutable && !self.is_copy(ty)) || ty.is_const());
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
                    handler_params.push(effect.map(|effect| match effect {
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
                    }))
                }
            }

            // parent handler
            if let Some(effect) = effect {
                let def = self.ast.idents[self.ast.effects[effect.effect].name].empty();
                handler_params.push(def.with(GenericVal::Literal(effect)));
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
            self.errors
                .push(b.def.unwrap().with(Error::ParameterMismatch(
                    Some(a.def.unwrap()),
                    a.params.len(),
                    b.params.len(),
                )));
            return;
        }

        for (a, b) in a.params.values().zip(Vec::from(params).into_iter()) {
            // FIXME: can fail to translate its own generics (which should be untranslated)
            let translated = self.translate_generics(b.ty, generic_params, true).unwrap();
            self.check_move(
                translated,
                a.ty,
                TypeRange {
                    loc: b.type_def,
                    def: Some(a.type_def),
                },
            );
        }

        // FIXME: check effect_stack

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
                    &mut Vec::new(),
                    &mut Vec::new(),
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
                self.check_sign(sign, FunIdent::Effect(effect, idx), &generic_params);
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

                value_captures: Vec::new(),
                effect_captures: Vec::new(),
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
                        let val = self.insert_type(Type::Effect(effect.clone()), false);
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
                        let val = self.insert_type(
                            Type::Generic(Generic {
                                idx: from,
                                typeof_ty: TYPE_EFFECT,
                            }),
                            false,
                        );
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
            (&Type::Pointer(from), &Type::Pointer(to)) => {
                self.infer_generics(params, from, to);
            }
            (&Type::Slice(from), &Type::Slice(to)) => {
                self.infer_generics(params, from, to);
            }
            (&Type::ConstArray(sfrom, from), &Type::ConstArray(sto, to)) => {
                match (sfrom, sto) {
                    (GenericVal::Literal(size), GenericVal::Generic(idx)) => {
                        let val = self.insert_type(
                            Type::CompileTime(Value::ConstantInt(TYPE_USIZE, false, size)),
                            false,
                        );
                        infer_generic(params, idx, val);
                    }
                    (GenericVal::Generic(from), GenericVal::Generic(to)) => {
                        let val = self.insert_type(
                            Type::Generic(Generic {
                                idx: from,
                                typeof_ty: TYPE_USIZE,
                            }),
                            false,
                        );
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
    fn is_copy(&self, a: TypeIdx) -> bool {
        match self.ir.types[a] {
            Type::Effect(_) => false,
            Type::Handler(_) => false,
            Type::EffectType => false,
            Type::DataType => false,
            Type::HandlerType(_) => false,
            Type::Generic(_) => false,
            Type::Pointer(_) => false,
            Type::ConstArray(_, _) => false,
            Type::Slice(_) => false,
            Type::Integer(_, _) => true,
            Type::Str => false,
            Type::Char => true,
            Type::Bool => true,
            Type::None => true,
            Type::Never => true,
            Type::Error => true,
            Type::CompileTime(_) => true,
        }
    }
    fn test_move(&mut self, from: TypeIdx, to: TypeIdx) -> bool {
        if from == to {
            return true;
        }
        if to.is_const() && !from.is_const() {
            let from = from.with_const(to.is_const());
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
        value_captures: &mut Vec<String>,
        effect_captures: &mut Vec<GenericVal<EffectIdent>>,
    ) -> FunImpl {
        scope.child(|scope| {
            let ir_sign = match sign {
                Either::Left(idx) => &self.ir.fun_sign[idx],
                Either::Right(sign) => sign,
            };

            scope.top().effect_stack = ir_sign
                .effect_stack
                .iter()
                .enumerate()
                .map(|(i, ident)| (ident.0.clone(), Value::EffectParam(i), None))
                .collect();

            let mut blocks = VecMap::new();
            let block = blocks.push(BlockIdx, Block::default());
            let mut fun_ctx = FunCtx {
                capture_boundary: scope.scopes.len() - 1,
                value_captures,
                effect_captures,

                scope,
                blocks,
                block,
                yeetable,
                yeetable_def,
                yeetable_ret: None,
            };

            for (idx, param) in ir_sign.params.iter(ParamIdx) {
                if param.mutable {
                    let value = fun_ctx.push_deref(Instruction::Reference(Value::Param(idx)));
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
            (E::Array(exprs), &Type::Slice(elem)) => {
                let elem = self.child_ty(elem, expected);
                let elems = exprs
                    .iter()
                    .copied()
                    .map(|expr| self.check_expr(ctx, expr, elem, expected_def))
                    .collect::<Option<Rc<[_]>>>()?;
                let len = elems.len() as u64;

                let arr = Value::ConstantAggregate(
                    self.insert_type(
                        Type::ConstArray(GenericVal::Literal(len), elem),
                        expected.is_const(),
                    ),
                    elems,
                );
                let ptr = ctx.push(Instruction::Reference(arr));
                let slice = Value::ConstantAggregate(
                    expected,
                    vec![ptr, Value::ConstantInt(TYPE_USIZE, false, len)].into(),
                );
                Some(slice)
            }
            (E::Array(exprs), &Type::ConstArray(GenericVal::Literal(n), elem))
                if n == exprs.len() as u64 =>
            {
                let elem = self.child_ty(elem, expected);
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
            (E::String(str), &Type::Slice(elem)) if elem == TYPE_U8 => {
                Some(Value::ConstantString(expected, str.as_bytes().into()))
            }
            (&E::UnOp(inner, UnOp::Cast), _) => {
                // TODO: test if allowed
                let (value, _ty) = self.synth_expr(ctx, inner)?;
                let instr = ctx.blocks[ctx.block]
                    .instructions
                    .push(InstrIdx, Instruction::Cast(value.clone(), expected));

                let reg = Value::Reg(ctx.block, Some(instr));
                if matches!(value, Value::Deref(_)) {
                    Some(Value::Deref(Box::new(reg)))
                } else {
                    Some(reg)
                }
            }
            (&E::TryWith(body, handler_expr), _) => ctx.child(|ctx| {
                let handler = match handler_expr {
                    Some(handler) => Some(self.synth_expr(ctx, handler)?),
                    None => None,
                };

                let end = ctx.blocks.push(
                    BlockIdx,
                    Block {
                        instructions: VecMap::new(),
                        value: None,
                    },
                );

                ctx.jump();
                let old_yeet = ctx.yeetable;
                let old_def = ctx.yeetable_def;
                let old_ret = ctx.yeetable_ret;

                ctx.yeetable = Some(expected);
                ctx.yeetable_def = expected_def;
                ctx.yeetable_ret = Some(end);
                if let Some((handler, ty)) = handler {
                    if ty != TYPE_ERROR {
                        let Type::Handler(lazy) = self.ir.types[ty] else {
                            unreachable!()
                        };
                        let Type::HandlerType(ref ty) = self.ir.types[lazy.typeof_handler] else {
                            unreachable!()
                        };

                        ctx.scope.top().effect_stack.push((
                            ty.effect.clone(),
                            handler,
                            ctx.yeetable_ret,
                        ));
                        self.check_move(
                            ty.fail_type,
                            expected,
                            TypeRange {
                                loc: self.ast.exprs[handler_expr.unwrap()].empty(),
                                def: expected_def,
                            },
                        );
                    }
                }

                let body_synth = self.synth_expr(ctx, body);

                if body_synth.is_none() && ctx.yeetable.is_none() {
                    ctx.yeetable = old_yeet;
                    ctx.yeetable_def = old_def;
                    ctx.yeetable_ret = old_ret;
                    None?;
                }

                let last = ctx.jump_to(end);
                ctx.blocks[end].value = Some(
                    body_synth
                        .into_iter()
                        .map(|(value, _)| (value, last))
                        .collect(),
                );

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

                if expected != TYPE_ERROR
                    && !self
                        .translate_generics(ret, &generic_params, false)
                        .is_some_and(|from| self.test_move(from, expected))
                {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::TypeMismatch(
                            None,
                            format!("{}", FmtType(&self.ir, expected)),
                            format!("{}", FmtType(&self.ir, ret)),
                        )))
                }

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
                                    self.insert_type(Type::CompileTime(val.clone()), false),
                                ))
                            } else {
                                todo!("give error: not constant")
                            }
                        }
                        Some(val)
                    })
                    .collect::<Option<Vec<_>>>()?;

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

                // get effects
                let mut not_enough_info = false;
                let mut effects = Vec::new();
                for effect in 0..fun.sign(&self.ir).effect_stack.len() {
                    // get effect ident
                    let ident = match fun.sign(&self.ir).effect_stack[effect].0 {
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
                                    Some((idx, self.translate_generics(ty, &generic_params, true)?))
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
                    match ctx.get_effect(self, ident) {
                        Some((idx, block)) => effects.push((idx, block)),
                        None => {
                            // error
                            let def = fun.sign(&self.ir).effect_stack[effect].empty();
                            self.errors
                                .push(self.ast.exprs[expr].with(Error::UnresolvedEffect(def)));
                        }
                    }
                }

                if not_enough_info {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                }

                let val = ctx.push(Instruction::Call(fun, generic_params, args, effects));
                Some(val)
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
                    for (param, ident) in sign
                        .params
                        .values_mut()
                        .zip(lambda.inputs.values().copied())
                    {
                        // rename params to lambda names
                        param.name_def = self.ast.idents[ident].empty();
                        param.name = self.ast.idents[ident].0.clone();

                        // FIXME: can fail to translate its own generics (which should be untranslated)
                        param.ty = self
                            .translate_generics(param.ty, &eff.generic_params, true)
                            .unwrap();
                    }
                    // FIXME: translate effect_stack

                    // FIXME: can fail to translate its own generics (which should be untranslated)
                    sign.return_type.ty = self
                        .translate_generics(sign.return_type.ty, &eff.generic_params, true)
                        .unwrap();

                    // analyze function
                    let mut value_captures = Vec::new();
                    let mut effect_captures = Vec::new();
                    let imp = self.generate_function(
                        Either::Right(&sign),
                        lambda.body,
                        ctx.scope,
                        Some(fail),
                        None,
                        &mut value_captures,
                        &mut effect_captures,
                    );

                    // create handler
                    let generics = ctx.all_generics();
                    let generic_params = self.to_generic_params(&generics);

                    let value_captures_types = value_captures
                        .iter()
                        .map(|s| Capture {
                            debug_name: s.into(),
                            ty: ctx.get_value(self, s).unwrap().ty,
                        })
                        .collect();
                    let handler = self.push_handler(Handler {
                        debug_name: format!("H{}", self.ir.handlers.len()),
                        generics,

                        effect: eff.effect,
                        generic_params: eff.generic_params,
                        fail,

                        value_captures: value_captures_types,
                        effect_captures: effect_captures.clone(),

                        funs: vec![(sign, imp)].into(),
                    });

                    let handler_ident = HandlerIdent {
                        handler,
                        generic_params,
                        fail_type: fail,
                    };
                    let idx = self.ir.lazy_handlers.push(
                        LazyIdx,
                        LazyValue::Some(GenericVal::Literal(handler_ident.clone())),
                    );
                    let ty = self.insert_type(
                        Type::Handler(Lazy {
                            idx,
                            typeof_handler: lazy.typeof_handler,
                        }),
                        false,
                    );
                    self.check_move(ty, expected, error_loc);

                    Some(Value::ConstantHandler(
                        handler_ident,
                        value_captures
                            .into_iter()
                            .map(|s| ctx.get_value(self, &s).unwrap().value)
                            .collect(),
                        effect_captures
                            .into_iter()
                            .map(|s| ctx.get_effect(self, s).unwrap())
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
                    BinOp::Divide => Instruction::Div(left, right),
                    BinOp::Multiply => Instruction::Mul(left, right),
                    BinOp::Subtract => Instruction::Sub(left, right),
                    BinOp::Add => Instruction::Add(left, right),
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
    fn addressable_expr(
        &mut self,
        ctx: &mut FunCtx,
        expr: ExprIdx,
    ) -> Option<(Value, TypeIdx, bool)> {
        use Expression as E;
        match self.ast.exprs[expr].0 {
            E::BinOp(left, BinOp::Index, right) => {
                let right = self.check_expr(ctx, right, TYPE_USIZE, None)?;

                // TODO: doesn't have to be addressable
                let (value, ty, mutable) = self.addressable_expr(ctx, left)?;

                let (ptr, elem_ty) = match self.ir.types[ty] {
                    Type::ConstArray(_, inner) => (value.inner_ptr(), inner),
                    Type::Slice(inner) => {
                        let ptr = ctx.push(Instruction::Member(value, 0));
                        (ptr, inner)
                    }
                    Type::Error => {
                        return Some((Value::ConstantError, TYPE_ERROR, true));
                    }
                    _ => todo!("give error"),
                };
                let elem_ty = self.child_ty(elem_ty, ty);

                let elem = ctx.push_deref(Instruction::AdjacentPtr(ptr, right, elem_ty));
                Some((elem, elem_ty, mutable && !ty.is_const()))
            }
            E::Ident(id) => {
                let name = &self.ast.idents[id].0;
                match ctx.get_value(self, name) {
                    Some(var) => {
                        if var.mutable {
                            // mutable variables must always be references
                            Some((var.value, var.ty, true))
                        } else {
                            // immutable reference time
                            let val = ctx.as_deref(var.value);
                            Some((val, var.ty, false))
                        }
                    }
                    None => {
                        self.errors
                            .push(self.ast.idents[id].with(Error::UnknownValue));
                        Some((Value::ConstantError, TYPE_ERROR, true))
                    }
                }
            }
            E::Error => Some((Value::ConstantError, TYPE_ERROR, true)),
            _ => todo!("give error"),
        }
    }
    fn synth_expr(&mut self, ctx: &mut FunCtx, expr: ExprIdx) -> Option<(Value, TypeIdx)> {
        use Expression as E;
        match self.ast.exprs[expr].0 {
            E::Body(ref body) => ctx.child(|ctx| {
                for expr in body.main.iter().copied() {
                    self.check_expr(ctx, expr, TYPE_NONE, None)?;
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
            E::TryWith(body, handler) => ctx.child(|ctx| {
                let handler = match handler {
                    Some(handler) => Some(self.synth_expr(ctx, handler)?),
                    None => None,
                };

                let end = ctx.blocks.push(
                    BlockIdx,
                    Block {
                        instructions: VecMap::new(),
                        value: None,
                    },
                );

                ctx.jump();
                let old_yeet = ctx.yeetable;
                let old_def = ctx.yeetable_def;
                let old_ret = ctx.yeetable_ret;

                ctx.yeetable = None;
                ctx.yeetable_def = None;
                ctx.yeetable_ret = Some(end);
                if let Some((handler, ty)) = handler {
                    if ty != TYPE_ERROR {
                        let Type::Handler(lazy) = self.ir.types[ty] else {
                            unreachable!()
                        };
                        let Type::HandlerType(ref ty) = self.ir.types[lazy.typeof_handler] else {
                            unreachable!()
                        };

                        ctx.yeetable = Some(ty.fail_type);
                        ctx.scope.top().effect_stack.push((
                            ty.effect.clone(),
                            handler,
                            ctx.yeetable_ret,
                        ));
                    }
                }

                let body_synth = self.synth_expr(ctx, body);

                if body_synth.is_none() && ctx.yeetable.is_none() {
                    ctx.yeetable = old_yeet;
                    ctx.yeetable_def = old_def;
                    ctx.yeetable_ret = old_ret;
                    None?;
                }
                let ty = body_synth
                    .as_ref()
                    .map(|&(_, ty)| ty)
                    .or(ctx.yeetable)
                    .unwrap();

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
                ctx.blocks[end].value = Some(
                    body_synth
                        .into_iter()
                        .map(|(value, _)| (value, last))
                        .collect(),
                );

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
                        let mut value_captures = Vec::new();
                        let mut effect_captures = Vec::new();
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
                                Some(EffectIdent {
                                    effect: eff.effect,
                                    generic_params: eff.generic_params.clone(),
                                }),
                                &function.decl.sign,
                            );

                            // analyze function
                            let imp = self.generate_function(
                                Either::Right(&sign),
                                function.body,
                                ctx.scope,
                                Some(fail),
                                None,
                                &mut value_captures,
                                &mut effect_captures,
                            );

                            match matching {
                                Some((idx, _)) => funs[idx] = (sign, imp),
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
                                continue;
                            };

                            // check sign mismatch
                            self.check_sign(
                                sign,
                                FunIdent::Effect(eff.effect, idx),
                                &eff.generic_params,
                            );
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
                        let generic_params = self.to_generic_params(&generics);

                        let value_captures_types = value_captures
                            .iter()
                            .map(|s| Capture {
                                debug_name: s.into(),
                                ty: ctx.get_value(self, s).unwrap().ty,
                            })
                            .collect();
                        let handler = self.push_handler(Handler {
                            debug_name: format!("H{}", self.ir.handlers.len()),
                            generics,

                            effect: eff.effect,
                            generic_params: eff.generic_params.clone(),
                            fail,

                            value_captures: value_captures_types,
                            effect_captures: effect_captures.clone(),

                            funs,
                        });

                        let handler_ident = HandlerIdent {
                            handler,
                            generic_params,
                            fail_type: fail,
                        };
                        let idx = self.ir.lazy_handlers.push(
                            LazyIdx,
                            LazyValue::Some(GenericVal::Literal(handler_ident.clone())),
                        );
                        let metaty = self.insert_type(
                            Type::HandlerType(HandlerType {
                                effect: GenericVal::Literal(EffectIdent {
                                    effect: eff.effect,
                                    generic_params: eff.generic_params,
                                }),
                                fail_type: fail,
                            }),
                            false,
                        );
                        let ty = self.insert_type(
                            Type::Handler(Lazy {
                                idx,
                                typeof_handler: metaty,
                            }),
                            false,
                        );
                        Some((
                            Value::ConstantHandler(
                                handler_ident,
                                value_captures
                                    .into_iter()
                                    .map(|s| ctx.get_value(self, &s).unwrap().value)
                                    .collect(),
                                effect_captures
                                    .into_iter()
                                    .map(|s| ctx.get_effect(self, s).unwrap())
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
                                    self.insert_type(Type::CompileTime(val.clone()), false),
                                ))
                            } else {
                                todo!("give error: not constant")
                            }
                        }
                        Some(val)
                    })
                    .collect::<Option<Vec<_>>>()?;

                // get return type
                let sign = &fun.sign(&self.ir);
                let mut not_enough_info = false;
                let return_type =
                    match self.translate_generics(sign.return_type.ty, &generic_params, true) {
                        Some(ty) => ty,
                        None => {
                            not_enough_info = true;
                            TYPE_ERROR
                        }
                    };

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

                // get effects
                let mut effects = Vec::new();
                for effect in 0..fun.sign(&self.ir).effect_stack.len() {
                    // get effect ident
                    let ident = match fun.sign(&self.ir).effect_stack[effect].0 {
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
                                    Some((idx, self.translate_generics(ty, &generic_params, true)?))
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
                    match ctx.get_effect(self, ident) {
                        Some((idx, block)) => effects.push((idx, block)),
                        None => {
                            // error
                            let def = fun.sign(&self.ir).effect_stack[effect].empty();
                            self.errors
                                .push(self.ast.exprs[expr].with(Error::UnresolvedEffect(def)));
                        }
                    }
                }

                if not_enough_info {
                    self.errors
                        .push(self.ast.exprs[expr].with(Error::NotEnoughInfo));
                }

                let val = ctx.push(Instruction::Call(fun, generic_params, args, effects));
                Some((val, return_type))
            }

            E::BinOp(left, BinOp::Assign, right) => {
                let (value, ty, mutable) = self.addressable_expr(ctx, left)?;
                if !mutable {
                    todo!("give error")
                }

                let right = self.check_expr(ctx, right, ty, None)?;
                ctx.push(Instruction::Store(value.inner_ptr(), right));

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
                        let ptr = ctx.as_deref(left).inner_ptr();
                        (ptr, elem)
                    }
                    Type::Error => {
                        return Some((Value::ConstantError, TYPE_ERROR));
                    }
                    _ => todo!("give error"),
                };
                let elem_ty = self.child_ty(elem_ty, left_ty);

                if let E::BinOp(rleft, BinOp::Range, rright) = self.ast.exprs[right].0 {
                    let rleft = self.check_expr(ctx, rleft, TYPE_USIZE, None)?;
                    let rright = self.check_expr(ctx, rright, TYPE_USIZE, None)?;

                    let ptr = ctx.push(Instruction::AdjacentPtr(ptr, rleft.clone(), elem_ty));
                    let len = ctx.push(Instruction::Sub(rright, rleft));

                    let slice_ty = self.insert_type(Type::Slice(elem_ty), false);
                    let slice = Value::ConstantAggregate(slice_ty, vec![ptr, len].into());
                    Some((slice, slice_ty))
                } else {
                    let right = self.check_expr(ctx, right, TYPE_USIZE, None)?;
                    let elem = ctx.push_deref(Instruction::AdjacentPtr(ptr, right, elem_ty));
                    Some((elem, elem_ty))
                }
            }
            E::BinOp(_, BinOp::Range, _) => {
                todo!("give error")
            }
            E::BinOp(left, op, right) => {
                let (left, left_ty) = self.synth_expr(ctx, left)?;
                let (right, _right_ty) = self.synth_expr(ctx, right)?;
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
                let (value, ty, mutable) = self.addressable_expr(ctx, inner)?;
                if !mutable {
                    todo!("give error")
                }

                let ptr = value.inner_ptr();
                let loaded = ctx.push(Instruction::Load(ptr.clone()));
                let incremented = ctx.push(Instruction::Add(
                    loaded.clone(),
                    Value::ConstantInt(ty, false, 1),
                ));
                ctx.push(Instruction::Store(ptr, incremented));
                Some((loaded, ty))
            }
            E::UnOp(inner, UnOp::Reference) => {
                let (value, ty, mutable) = self.addressable_expr(ctx, inner)?;
                let ptr_ty = self.insert_type(Type::Pointer(ty), !mutable);
                Some((value.inner_ptr(), ptr_ty))
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
                            todo!("give error");
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
                                .push_value(Instruction::Yeet(value));
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
                            .push_value(Instruction::Yeet(value));
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
                    let ptr = ctx.push_deref(Instruction::Reference(value));
                    ctx.define(
                        name,
                        Variable {
                            value: ptr,
                            ty,
                            mutable,
                        },
                    );
                } else {
                    ctx.define(
                        name,
                        Variable {
                            value,
                            ty: ty.with_const(!self.is_copy(ty)),
                            mutable,
                        },
                    );
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
                        );
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
                    self.analyze_type(&mut ctx.scope, ty, None, false, &mut Self::lazy_handler);
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
            E::Member(_, _) => todo!(),
        }
    }
}

struct FunCtx<'a> {
    scope: &'a mut ScopeStack,

    yeetable: Option<TypeIdx>,
    yeetable_def: Option<Range>,
    yeetable_ret: Option<BlockIdx>,

    blocks: VecMap<BlockIdx, Block>,
    block: BlockIdx,

    capture_boundary: usize,
    value_captures: &'a mut Vec<String>,
    effect_captures: &'a mut Vec<GenericVal<EffectIdent>>,
}

impl FunCtx<'_> {
    fn child<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push();
        let t = f(self);
        self.scope.pop();
        t
    }
    fn as_deref(&mut self, value: Value) -> Value {
        match value {
            Value::Deref(_) => value,
            _ => self.push_deref(Instruction::Reference(value)),
        }
    }
    fn push(&mut self, instr: Instruction) -> Value {
        let idx = self.blocks[self.block].instructions.push(InstrIdx, instr);
        Value::Reg(self.block, Some(idx))
    }
    fn push_deref(&mut self, instr: Instruction) -> Value {
        Value::Deref(Box::new(self.push(instr)))
    }
    fn all_generics(&self) -> Generics {
        let mut generics = Vec::new();
        for scope in self.scope.scopes.iter() {
            generics.extend(scope.generics.values().cloned());
        }
        generics.sort_unstable_by_key(|generic| generic.idx.0);
        generics
    }
    fn get_value(&mut self, ctx: &SemCtx, name: &str) -> Option<Variable> {
        let mut iter = self.scope.scopes.iter().enumerate().rev().chain([
            (usize::MAX, &ctx.packages[self.scope.package]),
            (usize::MAX, &ctx.packages[ctx.ast.preamble]),
        ]);
        iter.find_map(|(n, s)| {
            let val = s.values.get(name).cloned()?;
            if n < self.capture_boundary && (val.mutable || !val.value.is_constant()) {
                let idx = match self
                    .value_captures
                    .iter()
                    .position(|candidate| name.eq(candidate))
                {
                    Some(idx) => idx,
                    None => {
                        let idx = self.value_captures.len();
                        self.value_captures.push(name.into());
                        idx
                    }
                };
                Some(Variable {
                    value: Value::Deref(Box::new(Value::Capture(idx))),
                    ..val
                })
            } else {
                Some(val)
            }
        })
    }
    fn get_effect(
        &mut self,
        ctx: &mut SemCtx,
        ident: GenericVal<EffectIdent>,
    ) -> Option<(Value, Option<BlockIdx>)> {
        // find matching effect in stack
        for (n, s) in self.scope.scopes.iter().enumerate().rev() {
            for &(ref candidate, ref value, block) in s.effect_stack.iter().rev() {
                if ident.eq(candidate) {
                    return if n < self.capture_boundary {
                        let idx = match self
                            .effect_captures
                            .iter()
                            .position(|candidate| ident.eq(candidate))
                        {
                            Some(idx) => idx,
                            None => {
                                let idx = self.effect_captures.len();
                                self.effect_captures.push(ident);
                                idx
                            }
                        };
                        Some((Value::Deref(Box::new(Value::EffectCapture(idx))), None))
                    } else {
                        Some((value.clone(), block))
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

                        Some((
                            Value::ConstantHandler(
                                HandlerIdent {
                                    handler: idx,
                                    generic_params,
                                    fail_type: fail,
                                },
                                Rc::new([]),
                                Rc::new([]),
                            ),
                            self.yeetable_ret,
                        ))
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
                    self.blocks[self.block].value = Some(phi);
                    Some((Value::Reg(self.block, None), common))
                }
            }
        }
    }
}

#[derive(Clone)]
struct TypeRange {
    loc: Range,
    def: Option<Range>,
}

pub fn analyze(ast: &Ast, errors: &mut Errors) -> SemIR {
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

    ctx.insert_type(Type::Error, false);
    ctx.insert_type(Type::None, false);
    ctx.insert_type(Type::Never, false);
    ctx.insert_type(Type::DataType, false);
    ctx.insert_type(Type::EffectType, false);
    ctx.insert_type(Type::Integer(false, IntSize::Size), false);
    ctx.insert_type(Type::Bool, false);
    ctx.insert_type(Type::Integer(true, IntSize::Reg), false);
    ctx.insert_type(Type::Str, false);
    ctx.insert_type(Type::Char, false);
    ctx.insert_type(Type::Integer(false, IntSize::Bits(8)), false);

    let mut insert = |t: Type| {
        let ty = ctx.insert_type(t, false);
        let name = format!("{}", FmtType(&ctx.ir, ty));
        let name = String::from(&name[1..name.len() - 1]);
        let types = &mut ctx.packages[ast.preamble].types;
        types.insert(name, ty);
    };

    insert(Type::Bool);
    insert(Type::Char);
    insert(Type::None);
    insert(Type::Never);

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
                            (generic.idx, ctx.insert_type(Type::Generic(generic), false))
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
                &mut Vec::new(),
            );
        }
    }

    // remove LazyValue::Refer
    let mut modified = true;
    while modified {
        modified = false;
        for idx in (0..ctx.ir.lazy_handlers.len()).map(LazyIdx) {
            if let LazyValue::Refer(refidx, ref params) = ctx.ir.lazy_handlers[idx] {
                let handler = match ctx.ir.lazy_handlers[refidx] {
                    LazyValue::Some(GenericVal::Literal(ref handler)) => {
                        let handler = handler.clone();
                        LazyValue::Some(GenericVal::Literal(match params {
                            Some(params) => {
                                let params = params.clone();
                                HandlerIdent {
                                    handler: handler.handler,
                                    generic_params: handler
                                        .generic_params
                                        .into_iter()
                                        .map(|(idx, ty)| {
                                            (
                                                idx,
                                                ctx.translate_generics(ty, &params, true).unwrap(),
                                            )
                                        })
                                        .collect(),
                                    fail_type: ctx
                                        .translate_generics(handler.fail_type, &params, true)
                                        .unwrap(),
                                }
                            }
                            None => handler,
                        }))
                    }
                    LazyValue::Some(GenericVal::Generic(genericidx)) => match params {
                        Some(params) => {
                            match ctx.ir.types[get_param(params, genericidx).unwrap()] {
                                Type::Handler(lazy) => ctx.ir.lazy_handlers[lazy.idx].clone(),
                                Type::Error => LazyValue::None,
                                _ => unreachable!(),
                            }
                        }
                        None => LazyValue::Some(GenericVal::Generic(genericidx)),
                    },
                    _ => continue,
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

    ctx.ir
}
