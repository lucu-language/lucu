use std::collections::{HashMap, HashSet};

use crate::{
    error::{Error, Errors, Ranged},
    parser::{
        self, BinOp, EffFunIdx, EffIdx, EffectIdent, ExprIdx, Expression, FunIdx, FunSign, Ident,
        PackageIdx, ParamIdx, Parsed, UnOp,
    },
    vecmap::{vecmap_index, VecMap, VecSet},
};

vecmap_index!(Val);
vecmap_index!(TypeIdx);
vecmap_index!(HandlerIdx);

impl TypeIdx {
    fn matches(self, other: TypeIdx) -> bool {
        self == TYPE_UNKNOWN || other == TYPE_UNKNOWN || self == other
    }
    fn join(self, other: TypeIdx) -> Option<TypeIdx> {
        if self == other {
            return Some(self);
        }
        if self == TYPE_UNKNOWN || self == TYPE_NEVER {
            return Some(other);
        }
        if other == TYPE_UNKNOWN || other == TYPE_NEVER {
            return Some(self);
        }
        None
    }
    fn to_base(self, ctx: &mut AsysContext) -> TypeIdx {
        match ctx.asys.types[self] {
            Type::Handler(effect, yeet, _) => {
                ctx.asys.insert_type(Type::Handler(effect, yeet, None))
            }
            _ => self,
        }
    }
    fn display(self, ctx: &AsysContext) -> String {
        match ctx.asys.types[self] {
            Type::FunctionLiteral(_) => "function literal".into(),
            Type::None => "none".into(),
            Type::Never => "never".into(),
            _ => format!("'{}'", self.display_inner(ctx)),
        }
    }
    fn display_fails(self, ctx: &AsysContext) -> String {
        match ctx.asys.types[self] {
            Type::None => " fails".into(),
            Type::Never => "".into(),
            _ => format!(" fails {}", self.display_inner(ctx)),
        }
    }
    fn display_inner(self, ctx: &AsysContext) -> String {
        match ctx.asys.types[self] {
            Type::FunctionLiteral(_) => "<unknown>".into(),
            Type::PackageLiteral(_) => "<unknown>".into(),
            Type::Int => "int".into(),
            Type::USize => "usize".into(),
            Type::UPtr => "uptr".into(),
            Type::U8 => "u8".into(),
            Type::Str => "str".into(),
            Type::Bool => "bool".into(),
            Type::Handler(val, yeets, _) => yeets.display_handler(val, ctx),
            Type::None => "()".into(),
            Type::Never => "!".into(),
            Type::Unknown => "<unknown>".into(),
            Type::Pointer(ty) => format!("^{}", ty.display_inner(ctx)),
            Type::MultiPointer(ty) => format!("[^]{}", ty.display_inner(ctx)),
            Type::ConstArray(size, ty) => format!("[{}]{}", size, ty.display_inner(ctx)),
        }
    }
    fn display_handler(self, handler: Val, ctx: &AsysContext) -> String {
        let effect_name = match handler.0 {
            usize::MAX => "<unknown>".into(),
            _ => match ctx.asys.defs[handler] {
                Definition::Effect(e) => ctx.parsed.idents[ctx.parsed.effects[e].name].0.clone(),
                _ => "<unknown>".into(),
            },
        };
        format!("{}{}", effect_name, self.display_fails(ctx))
    }
    fn from_val(ctx: &mut AsysContext, val: Val) -> Self {
        match val.0 == usize::MAX {
            true => TYPE_UNKNOWN,
            false => match ctx.asys.defs[val] {
                Definition::Parameter(_, _, t) => t,
                Definition::Variable(_, _, t) => t,
                Definition::EffectFunction(_, _, _) => {
                    ctx.asys.insert_type(Type::FunctionLiteral(val))
                }
                Definition::Function(_, _) => ctx.asys.insert_type(Type::FunctionLiteral(val)),

                Definition::BuiltinType(_) => TYPE_UNKNOWN,
                Definition::Effect(_) => TYPE_UNKNOWN,
                Definition::Package(pkg) => ctx.asys.insert_type(Type::PackageLiteral(pkg)),
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum Definition {
    Parameter(Val, ParamIdx, TypeIdx), // parameter index in function
    Variable(bool, ExprIdx, TypeIdx),  // variable defined at expr
    Effect(EffIdx),                    // effect index in ast
    EffectFunction(EffIdx, EffFunIdx, TypeIdx), // effect value, function index in effect
    Function(FunIdx, TypeIdx),         // function index in ast

    BuiltinType(TypeIdx), // builtin type
    Package(PackageIdx),  // package
}

#[derive(Debug)]
pub struct Capture {
    pub val: Val,
    pub mutable: bool,
}

pub fn add_capture(captures: &mut Vec<Capture>, capture: Capture) {
    let idx = captures.iter().position(|c| c.val == capture.val);
    if let Some(idx) = idx {
        captures[idx].mutable |= capture.mutable
    } else {
        captures.push(capture)
    }
}

#[derive(Debug, Default)]
pub enum HandlerDef {
    Handler(ExprIdx, Vec<Capture>),
    Call(Val, Vec<ExprIdx>),
    Param(ParamIdx),
    Signature,

    #[default]
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    FunctionLiteral(Val),
    PackageLiteral(PackageIdx),
    Handler(Val, TypeIdx, Option<HandlerIdx>),

    Pointer(TypeIdx),
    MultiPointer(TypeIdx),
    ConstArray(u64, TypeIdx),

    Int,
    USize,
    UPtr,
    U8,

    Str,
    Bool,
    None,
    Never,
    Unknown,
}

impl Type {
    fn is_int(&self) -> bool {
        matches!(self, Type::Int | Type::USize | Type::UPtr | Type::U8)
    }
    fn is_ptr(&self) -> bool {
        matches!(self, Type::Pointer(_) | Type::MultiPointer(_))
    }
}

pub struct Analysis {
    pub values: VecMap<Ident, Val>,
    pub defs: VecMap<Val, Definition>,
    pub handlers: VecMap<HandlerIdx, HandlerDef>,
    pub exprs: VecMap<ExprIdx, TypeIdx>,
    pub types: VecSet<TypeIdx, Type>,
    pub main: Option<FunIdx>,
}

struct AsysContext<'a> {
    asys: Analysis,
    packages: VecMap<PackageIdx, Package>,
    parsed: &'a Parsed,
}

struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    values: HashMap<String, Val>,
    effects: &'a HashMap<String, Val>,
    scoped_effects: &'a HashSet<Val>,
    pkg: PackageIdx,
}

#[derive(Default, Clone)]
struct Package {
    effects: HashMap<String, Val>,
    values: HashMap<String, Val>,
    implied: HashSet<Val>,
}

impl<'a> Scope<'a> {
    fn get(&self, key: &str) -> Option<Val> {
        match self.values.get(key) {
            Some(&v) => Some(v),
            None => self.parent.map(|p| p.get(key)).flatten(),
        }
    }
    fn child(&self) -> Scope {
        Scope {
            parent: Some(self),
            values: HashMap::new(),
            effects: self.effects,
            scoped_effects: self.scoped_effects,
            pkg: self.pkg,
        }
    }
}

impl Val {
    fn definition_range(&self, ctx: &AsysContext) -> Option<Ranged<()>> {
        match ctx.asys.defs[*self] {
            Definition::Parameter(f, p, _) => match ctx.asys.defs[f] {
                Definition::EffectFunction(e, f, _) => Some(
                    ctx.parsed.idents[ctx.parsed.effects[e].functions[f].sign.inputs[p].0].empty(),
                ),
                Definition::Function(f, _) => {
                    Some(ctx.parsed.idents[ctx.parsed.functions[f].decl.sign.inputs[p].0].empty())
                }
                _ => None,
            },
            Definition::Effect(e) => Some(ctx.parsed.idents[ctx.parsed.effects[e].name].empty()),
            Definition::EffectFunction(e, f, _) => {
                Some(ctx.parsed.idents[ctx.parsed.effects[e].functions[f].name].empty())
            }
            Definition::Function(f, _) => {
                Some(ctx.parsed.idents[ctx.parsed.functions[f].decl.name].empty())
            }
            Definition::Variable(_, e, _) => match ctx.parsed.exprs[e].0 {
                Expression::Let(_, name, _, _) => Some(ctx.parsed.idents[name].empty()),
                _ => None,
            },
            Definition::BuiltinType(_) => None,
            Definition::Package(_) => None,
        }
    }
}

impl Analysis {
    fn push_val(&mut self, id: Ident, def: Definition) -> Val {
        let val = self.defs.push(Val, def);
        self.values[id] = val;
        val
    }
    fn insert_type(&mut self, ty: Type) -> TypeIdx {
        self.types.insert(TypeIdx, ty).clone()
    }
}

fn analyze_assignable(
    ctx: &mut AsysContext,
    scope: &mut Scope,
    expr: ExprIdx,
    parent: ExprIdx,
    errors: &mut Errors,
) -> TypeIdx {
    let ty = analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, errors);
    match ctx.parsed.exprs[expr].0 {
        Expression::Ident(id) => {
            let val = ctx.asys.values[id];
            if val.0 != usize::MAX {
                match ctx.asys.defs[val] {
                    Definition::Variable(true, _, _) => ty,
                    _ => {
                        errors.push(
                            ctx.parsed.exprs[parent]
                                .with(Error::AssignImmutable(val.definition_range(ctx))),
                        );
                        TYPE_UNKNOWN
                    }
                }
            } else {
                TYPE_UNKNOWN
            }
        }
        Expression::BinOp(left, BinOp::Index, right) => {
            let array = analyze_assignable(ctx, scope, left, expr, errors);
            analyze_expr(ctx, scope, right, TYPE_USIZE, errors);

            match ctx.asys.types[array] {
                Type::ConstArray(_, ty) => ty,
                Type::Unknown => TYPE_UNKNOWN,
                _ => {
                    // TODO: error
                    TYPE_UNKNOWN
                }
            }
        }
        Expression::Error => TYPE_UNKNOWN,
        _ => {
            errors.push(ctx.parsed.exprs[parent].with(Error::AssignExpression));
            TYPE_UNKNOWN
        }
    }
}

fn capture_ident(
    ctx: &mut AsysContext,
    scope: &mut Scope,
    id: Ident,
    effect: Option<Val>,
    captures: &mut Vec<Capture>,
) {
    let val = ctx.asys.values[id];
    if val.0 != usize::MAX {
        match ctx.asys.defs[val] {
            Definition::EffectFunction(e, _, _) => {
                let e = ctx.asys.values[ctx.parsed.effects[e].name];
                if Some(e) != effect && scope.scoped_effects.contains(&e) {
                    add_capture(
                        captures,
                        Capture {
                            val: e,
                            mutable: false,
                        },
                    );
                }
            }
            Definition::Function(fun, _) => {
                let effects = ctx.parsed.functions[fun]
                    .decl
                    .sign
                    .effects
                    .iter()
                    .copied()
                    .map(|i| ctx.asys.values[i.effect]);
                for e in effects {
                    if Some(e) != effect && scope.scoped_effects.contains(&e) {
                        add_capture(
                            captures,
                            Capture {
                                val: e,
                                mutable: false,
                            },
                        );
                    }
                }
            }
            Definition::Parameter(_, _, _) => {
                if scope.get(&ctx.parsed.idents[id].0) == Some(val) {
                    add_capture(
                        captures,
                        Capture {
                            val,
                            mutable: false,
                        },
                    );
                }
            }
            Definition::Variable(mutable, _, _) => {
                if scope.get(&ctx.parsed.idents[id].0) == Some(val) {
                    add_capture(captures, Capture { val, mutable });
                }
            }
            Definition::Effect(_) => {
                if scope.get(&ctx.parsed.idents[id].0) == Some(val) {
                    add_capture(
                        captures,
                        Capture {
                            val,
                            mutable: false,
                        },
                    );
                }
            }
            Definition::BuiltinType(_) => {}
            Definition::Package(_) => {}
        }
    }
}

fn analyze_expr(
    ctx: &mut AsysContext,
    scope: &mut Scope,
    expr: ExprIdx,
    expected_type: TypeIdx,
    errors: &mut Errors,
) -> TypeIdx {
    let found_type = match ctx.parsed.exprs[expr].0 {
        // analyze
        Expression::Handler(ref handler) => {
            // resolve yeet
            let yeet_type = match handler.fail_type {
                parser::FailType::Never => TYPE_NEVER,
                parser::FailType::None => TYPE_NONE,
                parser::FailType::Some(t) => {
                    let yeet_type = analyze_type(ctx, scope, t, errors);

                    if matches!(ctx.asys.types[yeet_type], Type::Handler(_, _, _)) {
                        errors.push(ctx.parsed.types[t].with(Error::NestedHandlers));
                    }

                    yeet_type
                }
            };

            // put effect in scope
            let ident = handler.effect;
            let effect = analyze_effect(ctx, ident, scope, errors);

            // match fun names to effect
            if let Some(effect) = effect {
                for fun in handler.functions.iter() {
                    let name = &ctx.parsed.idents[fun.decl.name].0;
                    let effectfun = match ctx.asys.defs[effect] {
                        Definition::Effect(idx) => ctx.parsed.effects[idx]
                            .functions
                            .values()
                            .find(|decl| ctx.parsed.idents[decl.name].0.eq(name))
                            .map(|decl| ctx.asys.values[decl.name]),
                        _ => None,
                    };
                    match effectfun {
                        Some(val) => ctx.asys.values[fun.decl.name] = val,
                        None => errors.push(ctx.parsed.idents[fun.decl.name].with(
                            Error::UnknownEffectFun(
                                effect.definition_range(ctx),
                                Some(ctx.parsed.idents[ident.effect].empty()),
                            ),
                        )),
                    }
                }
            }

            // analyze functions
            let mut captures = Vec::new();
            for fun in handler.functions.iter() {
                let expected = analyze_return(ctx, scope, fun.decl.sign.output, errors);

                let mut child = scope.child();
                let val = ctx.asys.values[fun.decl.name];
                scope_sign(ctx, &mut child, &fun.decl.sign);

                let mut scoped = scope.scoped_effects.clone();
                scoped.extend(fun.decl.sign.effects.iter().copied().filter_map(|i| {
                    let val = ctx.asys.values[i.effect];
                    if val.0 == usize::MAX {
                        None
                    } else {
                        Some(val)
                    }
                }));
                child.scoped_effects = &scoped;

                let found = analyze_expr(ctx, &mut child, fun.body, expected, errors);

                // set concrete handler type
                if matches!(ctx.asys.types[expected], Type::Handler(_, _, _)) {
                    match &mut ctx.asys.defs[val] {
                        Definition::EffectFunction(_, _, typ) => *typ = found,
                        _ => unreachable!(),
                    }
                }

                // add captures
                ctx.parsed.for_each(
                    fun.body,
                    true,
                    true,
                    &mut |expr| match ctx.parsed.exprs[expr].0 {
                        Expression::Ident(id) => {
                            capture_ident(ctx, scope, id, effect, &mut captures);
                        }
                        _ => {}
                    },
                );
            }

            // get handler type
            let handler_type = match effect {
                Some(val) => {
                    let handler = ctx
                        .asys
                        .handlers
                        .push(HandlerIdx, HandlerDef::Handler(expr, captures));
                    ctx.asys
                        .insert_type(Type::Handler(val, yeet_type, Some(handler)))
                }
                None => TYPE_UNKNOWN,
            };

            handler_type
        }
        Expression::Ident(ident) => {
            let name = &ctx.parsed.idents[ident].0;
            match scope.get(name) {
                Some(val) => {
                    ctx.asys.values[ident] = val;
                    TypeIdx::from_val(ctx, val)
                }
                None => {
                    match scope
                        .scoped_effects
                        .iter()
                        .find(|&&v| match ctx.asys.defs[v] {
                            Definition::Effect(idx) => {
                                ctx.parsed.idents[ctx.parsed.effects[idx].name].0.eq(name)
                            }
                            _ => false,
                        })
                        .copied()
                    {
                        Some(val) => {
                            // handled effects may be implicitly converted to handlers that never fail
                            ctx.asys.values[ident] = val;
                            let handler = ctx.asys.handlers.push(HandlerIdx, HandlerDef::Signature);
                            ctx.asys
                                .insert_type(Type::Handler(val, TYPE_NEVER, Some(handler)))
                        }
                        None => {
                            errors.push(ctx.parsed.idents[ident].with(Error::UnknownValue));
                            TYPE_UNKNOWN
                        }
                    }
                }
            }
        }

        // traverse downwards
        Expression::Body(ref b) => {
            let mut child = scope.child();

            for &expr in b.main.iter() {
                analyze_expr(ctx, &mut child, expr, TYPE_UNKNOWN, errors);
            }
            match b.last {
                Some(expr) => analyze_expr(ctx, &mut child, expr, expected_type, errors),
                None => TYPE_NONE,
            }
        }
        Expression::Loop(expr) => {
            analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, errors);
            TYPE_NEVER
        }
        Expression::Call(cexpr, ref exprs) => {
            // get function
            let fun = match ctx.parsed.exprs[cexpr].0 {
                Expression::Ident(ident) => {
                    // calling directly with an identifier
                    // when a value is not found in scope we also check within effect functions
                    let name = &ctx.parsed.idents[ident].0;
                    match scope.get(name) {
                        Some(fun) => {
                            ctx.asys.values[ident] = fun;
                            Some(fun)
                        }
                        None => {
                            // check among effects
                            let effect_funs = scope
                                .scoped_effects
                                .iter()
                                .copied()
                                .flat_map(|val| match ctx.asys.defs[val] {
                                    Definition::Effect(idx) => {
                                        let effect_ident = ctx.parsed.effects[idx].name;
                                        let ctx = &*ctx;
                                        ctx.parsed.effects[idx].functions.values().map(
                                            move |decl| {
                                                (
                                                    effect_ident,
                                                    &ctx.parsed.idents[decl.name].0,
                                                    ctx.asys.values[decl.name],
                                                )
                                            },
                                        )
                                    }
                                    _ => unreachable!(),
                                })
                                .filter_map(|(i, s, v)| match name == s {
                                    true => Some((i, v)),
                                    false => None,
                                })
                                .collect::<Vec<_>>();

                            if effect_funs.len() > 1 {
                                errors.push(
                                    ctx.parsed.idents[ident].with(Error::MultipleEffects(
                                        effect_funs
                                            .into_iter()
                                            .map(|(i, _)| ctx.parsed.idents[i].empty())
                                            .collect(),
                                    )),
                                );
                                None
                            } else if let Some(&(_, fun)) = effect_funs.first() {
                                ctx.asys.values[ident] = fun;
                                Some(fun)
                            } else {
                                errors.push(ctx.parsed.idents[ident].with(Error::UnknownValue));
                                None
                            }
                        }
                    }
                }
                _ => {
                    let fun = analyze_expr(ctx, scope, cexpr, TYPE_UNKNOWN, errors);
                    match ctx.asys.types[fun] {
                        Type::FunctionLiteral(fun) => Some(fun),
                        Type::Unknown => None,
                        _ => {
                            errors.push(
                                ctx.parsed.exprs[cexpr]
                                    .with(Error::ExpectedFunction(fun.display(ctx))),
                            );
                            None
                        }
                    }
                }
            };
            // get function signature
            // TODO: error on effect mismatch
            let (params, return_type) = match fun {
                Some(fun) => match ctx.asys.defs[fun] {
                    Definition::Function(fun_idx, return_type) => {
                        ctx.asys.exprs[cexpr] = ctx.asys.insert_type(Type::FunctionLiteral(fun));
                        (
                            Some(
                                ctx.parsed.functions[fun_idx]
                                    .decl
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|&(ident, _)| {
                                        TypeIdx::from_val(ctx, ctx.asys.values[ident]).to_base(ctx)
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            return_type,
                        )
                    }
                    Definition::EffectFunction(eff_idx, fun_idx, return_type) => {
                        ctx.asys.exprs[cexpr] = ctx.asys.insert_type(Type::FunctionLiteral(fun));
                        (
                            Some(
                                ctx.parsed.effects[eff_idx].functions[fun_idx]
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|&(ident, _)| {
                                        TypeIdx::from_val(ctx, ctx.asys.values[ident]).to_base(ctx)
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            return_type,
                        )
                    }
                    _ => {
                        errors.push(ctx.parsed.exprs[cexpr].with(Error::ExpectedFunction(
                            TypeIdx::from_val(ctx, fun).display(ctx),
                        )));
                        (None, TYPE_UNKNOWN)
                    }
                },
                None => (None, TYPE_UNKNOWN),
            };
            // handle return type as handler
            // this way different calls always return different handlers according to the type checker
            // leading to a type mismatch
            let return_type = match ctx.asys.types[return_type] {
                Type::Handler(val, yeet, _) => {
                    let handler = ctx.asys.handlers.push(
                        HandlerIdx,
                        fun.map(|fun| HandlerDef::Call(fun, exprs.clone()))
                            .unwrap_or_default(),
                    );
                    ctx.asys
                        .insert_type(Type::Handler(val, yeet, Some(handler)))
                }
                _ => return_type,
            };
            // analyze arguments
            if let Some(params) = params {
                if params.len() != exprs.len() {
                    errors.push(
                        ctx.parsed.exprs[expr]
                            .with(Error::ParameterMismatch(params.len(), exprs.len())),
                    );
                }
                for (expr, expected) in exprs.iter().copied().zip(params.into_iter()) {
                    analyze_expr(ctx, scope, expr, expected, errors);
                }
            }
            return_type
        }
        Expression::TryWith(expr, return_type, handler) => {
            let return_type = analyze_return(ctx, scope, return_type, errors);

            let expected_return = match ctx.asys.types[return_type] {
                Type::None => TYPE_UNKNOWN,
                _ => return_type,
            };

            let mut child = scope.child();
            let ty = if let Some(handler) = handler {
                let handler_type = analyze_expr(ctx, &mut child, handler, TYPE_UNKNOWN, errors);

                let handler_type = match ctx.asys.types[handler_type] {
                    Type::Handler(handler, break_type, _) => Some((handler, break_type)),
                    Type::Unknown => None,
                    _ => {
                        errors.push(
                            ctx.parsed.exprs[handler]
                                .with(Error::ExpectedHandler(handler_type.display(ctx))),
                        );
                        None
                    }
                };

                if let Some((eff_val, handler_break)) = handler_type {
                    let effect = match ctx.asys.defs[eff_val] {
                        Definition::Effect(idx) => ctx.parsed.effects[idx].name,
                        _ => panic!(),
                    };

                    let expected_break = match ctx.asys.types[handler_break] {
                        Type::Never => expected_return,
                        _ => handler_break,
                    };

                    let mut scoped = child.scoped_effects.clone();
                    scoped.insert(ctx.asys.values[effect]);

                    child.scoped_effects = &scoped;
                    if !TypeIdx::matches(expected_break, expected_return) {
                        errors.push(ctx.parsed.exprs[handler].with(Error::TypeMismatch(
                            format!("'{}'", expected_return.display_handler(eff_val, ctx)),
                            format!("'{}'", expected_break.display_handler(eff_val, ctx)),
                        )));

                        analyze_expr(ctx, &mut child, expr, expected_return, errors)
                    } else {
                        analyze_expr(ctx, &mut child, expr, expected_break, errors)
                    }
                } else {
                    TYPE_UNKNOWN
                }
            } else {
                analyze_expr(ctx, &mut child, expr, expected_return, errors)
            };

            if matches!(ctx.asys.types[ty], Type::Handler(_, _, _)) {
                let expr = match &ctx.parsed.exprs[expr].0 {
                    Expression::Body(body) => body.last.unwrap(),
                    _ => expr,
                };

                errors.push(ctx.parsed.exprs[expr].with(Error::TryReturnsHandler));
            }

            ty
        }
        Expression::Member(expr, field) => {
            let handler = if let Expression::Ident(ident) = ctx.parsed.exprs[expr].0 {
                // getting a member directly with an identifier
                // when a value is not found in scope we also check within effects
                let name = &ctx.parsed.idents[ident].0;
                match scope.get(name) {
                    Some(val) => {
                        ctx.asys.values[ident] = val;

                        let ty = TypeIdx::from_val(ctx, val);
                        ctx.asys.exprs[expr] = ty;
                        Some(ty)
                    }
                    None => match scope.effects.get(name) {
                        Some(&effect) => {
                            ctx.asys.values[ident] = effect;

                            if !scope.scoped_effects.contains(&effect) {
                                errors.push(ctx.parsed.idents[ident].with(Error::UnhandledEffect));
                            }

                            let ty = ctx
                                .asys
                                .insert_type(Type::Handler(effect, TYPE_NEVER, None));
                            ctx.asys.exprs[expr] = ty;
                            Some(ty)
                        }
                        None => match ctx.parsed.packages[scope.pkg].imports.get(name) {
                            Some(&pkg) => {
                                let ty = ctx.asys.insert_type(Type::PackageLiteral(pkg));
                                ctx.asys.push_val(ident, Definition::Package(pkg));
                                ctx.asys.exprs[expr] = ty;
                                Some(ty)
                            }
                            None => {
                                // TODO: custom error
                                errors.push(ctx.parsed.idents[ident].with(Error::UnknownValue));
                                None
                            }
                        },
                    },
                }
            } else {
                // TODO: allow parent expr to be effect of package
                Some(analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, errors))
            };

            if let Some(handler) = handler {
                match ctx.asys.types[handler] {
                    Type::PackageLiteral(pkg) => {
                        let name = &ctx.parsed.idents[field].0;
                        match ctx.packages[pkg].values.get(name) {
                            Some(&val) => {
                                ctx.asys.values[field] = val;
                                TypeIdx::from_val(ctx, val)
                            }
                            None => {
                                // TODO: custom error
                                errors.push(ctx.parsed.idents[field].with(Error::UnknownField(
                                    None,
                                    Some(ctx.parsed.exprs[expr].empty()),
                                )));
                                TYPE_UNKNOWN
                            }
                        }
                    }
                    Type::Handler(effect, _, _) => {
                        let name = &ctx.parsed.idents[field].0;
                        let fun = match ctx.asys.defs[effect] {
                            Definition::Effect(idx) => ctx.parsed.effects[idx]
                                .functions
                                .values()
                                .find(|decl| ctx.parsed.idents[decl.name].0.eq(name))
                                .map(|decl| ctx.asys.values[decl.name]),
                            _ => None,
                        };
                        match fun {
                            Some(fun) => {
                                ctx.asys.values[field] = fun;
                                ctx.asys.insert_type(Type::FunctionLiteral(fun))
                            }
                            None => {
                                errors.push(ctx.parsed.idents[field].with(
                                    Error::UnknownEffectFun(
                                        effect.definition_range(ctx),
                                        Some(ctx.parsed.exprs[expr].empty()),
                                    ),
                                ));
                                TYPE_UNKNOWN
                            }
                        }
                    }
                    Type::Unknown => TYPE_UNKNOWN,
                    _ => {
                        // TODO: type definition
                        errors.push(ctx.parsed.idents[field].with(Error::UnknownField(
                            None,
                            Some(ctx.parsed.exprs[expr].empty()),
                        )));
                        TYPE_UNKNOWN
                    }
                }
            } else {
                TYPE_UNKNOWN
            }
        }
        Expression::IfElse(cond, no, yes) => {
            analyze_expr(ctx, scope, cond, TYPE_BOOL, errors);
            let yes_type = analyze_expr(ctx, scope, no, expected_type, errors);
            let no_type = match yes {
                Some(expr) => analyze_expr(ctx, scope, expr, expected_type, errors),
                None => TYPE_NONE,
            };
            TypeIdx::join(yes_type, no_type).unwrap_or(TYPE_NONE)
        }
        Expression::BinOp(left, op, right) => match op {
            BinOp::Assign => {
                let left_type = analyze_assignable(ctx, scope, left, expr, errors);
                analyze_expr(ctx, scope, right, left_type, errors);
                TYPE_NONE
            }
            BinOp::Index => {
                let array = analyze_expr(ctx, scope, left, TYPE_UNKNOWN, errors);
                analyze_expr(ctx, scope, right, TYPE_USIZE, errors);

                match ctx.asys.types[array] {
                    Type::ConstArray(_, ty) => ty,
                    Type::MultiPointer(ty) => ty,
                    Type::Unknown => TYPE_UNKNOWN,
                    _ => {
                        // TODO: error
                        TYPE_UNKNOWN
                    }
                }
            }
            _ => {
                let ret_ty = match op {
                    BinOp::Equals | BinOp::Less | BinOp::Greater => Some(TYPE_BOOL),
                    BinOp::Divide | BinOp::Multiply | BinOp::Subtract | BinOp::Add => None,
                    BinOp::Assign | BinOp::Index => unreachable!(),
                };
                match ret_ty {
                    Some(ret_ty) => {
                        let op_ty = analyze_expr(ctx, scope, left, TYPE_UNKNOWN, errors);
                        analyze_expr(ctx, scope, right, op_ty, errors);
                        ret_ty
                    }
                    None => {
                        let op_ty = analyze_expr(ctx, scope, left, expected_type, errors);
                        analyze_expr(ctx, scope, right, op_ty, errors);
                        op_ty
                    }
                }
            }
        },
        Expression::UnOp(uexpr, op) => match op {
            UnOp::PostIncrement => analyze_assignable(ctx, scope, uexpr, expr, errors),
            UnOp::Reference => {
                let ty = analyze_expr(ctx, scope, uexpr, TYPE_UNKNOWN, errors);
                match ctx.asys.types[expected_type] {
                    Type::Pointer(_) => ctx.asys.insert_type(Type::Pointer(ty)),
                    Type::MultiPointer(_) => {
                        // TODO: make sure only arrays may implicitly convert to multi pointer
                        ctx.asys.insert_type(Type::MultiPointer(ty))
                    }
                    _ => ctx.asys.insert_type(Type::Pointer(ty)),
                }
            }
            UnOp::Cast => {
                let ty = analyze_expr(ctx, scope, uexpr, TYPE_UNKNOWN, errors);
                match (&ctx.asys.types[ty], &ctx.asys.types[expected_type]) {
                    (t1, Type::UPtr) if t1.is_ptr() => expected_type,
                    (Type::UPtr, t2) if t2.is_ptr() => expected_type,
                    (t1, t2) if t1.is_ptr() && t2.is_ptr() => expected_type,
                    (t1, t2) if t1.is_int() && t2.is_int() => expected_type,
                    (_t1, _t2) => ty,
                }
            }
        },
        Expression::Yeet(val) => {
            // TODO: yeet type analysis
            if let Some(expr) = val {
                analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, errors);
            }
            TYPE_NEVER
        }
        Expression::Let(mutable, name, ty, rexpr) => {
            let val_type = match ty {
                Some(ty) => analyze_type(ctx, scope, ty, errors),
                None => TYPE_UNKNOWN,
            };
            let val_type = analyze_expr(ctx, scope, rexpr, val_type, errors);

            let val = ctx
                .asys
                .push_val(name, Definition::Variable(mutable, expr, val_type));
            scope.values.insert(ctx.parsed.idents[name].0.clone(), val);
            TYPE_NONE
        }

        // these have no identifiers
        Expression::String(_) => match ctx.asys.types[expected_type] {
            Type::Str => TYPE_STR,

            // default type for literal
            _ => TYPE_STR,
        },
        Expression::Character(_) => match ctx.asys.types[expected_type] {
            // TODO: check if fits
            Type::U8 => TYPE_U8,

            // default type for literal
            // TODO: character type
            _ => TYPE_U8,
        },
        Expression::Int(_) => match ctx.asys.types[expected_type] {
            // TODO: check if fits
            Type::Int => TYPE_INT,
            Type::USize => TYPE_USIZE,
            Type::UPtr => TYPE_UPTR,
            Type::U8 => TYPE_U8,

            // default type for literal
            _ => TYPE_INT,
        },
        Expression::Uninit => {
            // TODO: error if expected_type is undefined
            expected_type
        }
        Expression::Error => TYPE_UNKNOWN,
    };

    let typ = match (expected_type, found_type.to_base(ctx)) {
        (a, b) if TypeIdx::matches(a, b) => found_type,
        (_, TYPE_NEVER) => expected_type,

        (_, _) => {
            errors.push(ctx.parsed.exprs[expr].with(Error::TypeMismatch(
                expected_type.display(ctx),
                found_type.display(ctx),
            )));
            expected_type
        }
    };

    ctx.asys.exprs[expr] = typ;
    ctx.asys.exprs[expr]
}

fn analyze_effect(
    ctx: &mut AsysContext,
    ident: EffectIdent,
    scope: &Scope,
    errors: &mut Errors,
) -> Option<Val> {
    let effects = match ident.package {
        Some(package) => {
            let name = &ctx.parsed.idents[package].0;
            match ctx.parsed.packages[scope.pkg].imports.get(name) {
                Some(&pkg) => {
                    ctx.asys.push_val(package, Definition::Package(pkg));
                    &ctx.packages[pkg].effects
                }
                None => {
                    // TODO: custom error
                    errors.push(ctx.parsed.idents[package].with(Error::UnknownValue));
                    return None;
                }
            }
        }
        None => &scope.effects,
    };
    let ident = ident.effect;

    let name = &ctx.parsed.idents[ident].0;
    match effects.get(name) {
        Some(&val) => {
            ctx.asys.values[ident] = val;
            Some(val)
        }
        None => {
            // TODO: custom error on package
            errors.push(ctx.parsed.idents[ident].with(Error::UnknownEffect));
            None
        }
    }
}

fn analyze_return(
    ctx: &mut AsysContext,
    scope: &Scope,
    ty: Option<parser::TypeIdx>,
    errors: &mut Errors,
) -> TypeIdx {
    match ty {
        Some(ty) => analyze_type(ctx, scope, ty, errors),
        None => TYPE_NONE,
    }
}

fn analyze_type(
    ctx: &mut AsysContext,
    scope: &Scope,
    ty: parser::TypeIdx,
    errors: &mut Errors,
) -> TypeIdx {
    use parser::Type as T;
    let (id, fail) = match ctx.parsed.types[ty].0 {
        T::Never => return TYPE_NEVER,
        T::Error => return TYPE_UNKNOWN,
        T::Path(id) => (id, parser::FailType::Never),
        T::Handler(id, fail) => (id, fail),
        T::Pointer(ty) => {
            let inner = analyze_type(ctx, scope, ty, errors);
            return ctx.asys.insert_type(Type::Pointer(inner));
        }
        T::MultiPointer(ty) => {
            let inner = analyze_type(ctx, scope, ty, errors);
            return ctx.asys.insert_type(Type::MultiPointer(inner));
        }
        T::ConstArray(size, ty) => {
            let inner = analyze_type(ctx, scope, ty, errors);
            return ctx.asys.insert_type(Type::ConstArray(size, inner));
        }
    };

    let name = &ctx.parsed.idents[id].0;

    // check scope
    match scope.get(name) {
        Some(val) => {
            ctx.asys.values[id] = val;
            match ctx.asys.defs[val] {
                Definition::BuiltinType(ty) => {
                    if matches!(fail, parser::FailType::Never) {
                        ty
                    } else {
                        errors.push(ctx.parsed.idents[id].with(Error::ExpectedEffect(
                            ty.display(ctx),
                            val.definition_range(ctx),
                        )));
                        TYPE_UNKNOWN
                    }
                }
                _ => {
                    errors.push(
                        ctx.parsed.idents[id].with(Error::ExpectedType(val.definition_range(ctx))),
                    );
                    TYPE_UNKNOWN
                }
            }
        }

        // check effects
        None => match scope.effects.get(name) {
            Some(&val) => {
                ctx.asys.values[id] = val;
                let fail = match fail {
                    parser::FailType::Never => TYPE_NEVER,
                    parser::FailType::None => TYPE_NONE,
                    parser::FailType::Some(ty) => analyze_type(ctx, scope, ty, errors),
                };
                if matches!(ctx.asys.types[fail], Type::Handler(_, _, _)) {
                    errors.push(ctx.parsed.types[ty].with(Error::NestedHandlers))
                }
                ctx.asys.insert_type(Type::Handler(val, fail, None))
            }
            None => {
                if matches!(fail, parser::FailType::Never) {
                    errors.push(ctx.parsed.idents[id].with(Error::UnknownType))
                } else {
                    errors.push(ctx.parsed.idents[id].with(Error::UnknownEffect))
                }
                TYPE_UNKNOWN
            }
        },
    }
}

fn analyze_sign(
    ctx: &mut AsysContext,
    scope: &Scope,
    val: Val,
    func: &FunSign,
    errors: &mut Errors,
) {
    // put effects in scope
    for &effect in func.effects.iter() {
        analyze_effect(ctx, effect, scope, errors);
    }

    // put args in scope
    for (i, &(param, ty)) in func.inputs.values().enumerate() {
        // resolve type
        let typ = analyze_type(ctx, scope, ty, errors);
        let typ = match ctx.asys.types[typ] {
            Type::Handler(effect, yeet, _) => {
                let handler = ctx
                    .asys
                    .handlers
                    .push(HandlerIdx, HandlerDef::Param(ParamIdx(i)));
                ctx.asys
                    .insert_type(Type::Handler(effect, yeet, Some(handler)))
            }
            _ => typ,
        };
        ctx.asys
            .push_val(param, Definition::Parameter(val, ParamIdx(i), typ));
    }
}

fn scope_sign(ctx: &mut AsysContext, scope: &mut Scope, func: &FunSign) {
    // put args in scope
    for &(param, _) in func.inputs.values() {
        // add parameter to scope
        scope
            .values
            .insert(ctx.parsed.idents[param].0.clone(), ctx.asys.values[param]);
    }
}

pub const TYPE_NONE: TypeIdx = TypeIdx(1);
pub const TYPE_NEVER: TypeIdx = TypeIdx(2);

const TYPE_UNKNOWN: TypeIdx = TypeIdx(0);
const TYPE_INT: TypeIdx = TypeIdx(3);
const TYPE_STR: TypeIdx = TypeIdx(4);
const TYPE_BOOL: TypeIdx = TypeIdx(5);

const TYPE_USIZE: TypeIdx = TypeIdx(6);
const TYPE_UPTR: TypeIdx = TypeIdx(7);
const TYPE_U8: TypeIdx = TypeIdx(8);

pub fn analyze(parsed: &Parsed, errors: &mut Errors) -> Analysis {
    let mut asys = Analysis {
        values: VecMap::filled(parsed.idents.len(), Val(usize::MAX)),
        exprs: VecMap::filled(parsed.exprs.len(), TYPE_UNKNOWN),
        defs: VecMap::new(),
        main: None,
        handlers: VecMap::new(),
        types: VecSet::new(),
    };

    asys.types.insert(TypeIdx, Type::Unknown);
    asys.types.insert(TypeIdx, Type::None);
    asys.types.insert(TypeIdx, Type::Never);
    asys.types.insert(TypeIdx, Type::Int);
    asys.types.insert(TypeIdx, Type::Str);
    asys.types.insert(TypeIdx, Type::Bool);
    asys.types.insert(TypeIdx, Type::USize);
    asys.types.insert(TypeIdx, Type::UPtr);
    asys.types.insert(TypeIdx, Type::U8);

    let str = asys.defs.push(Val, Definition::BuiltinType(TYPE_STR));
    let int = asys.defs.push(Val, Definition::BuiltinType(TYPE_INT));
    let usize = asys.defs.push(Val, Definition::BuiltinType(TYPE_USIZE));
    let uptr = asys.defs.push(Val, Definition::BuiltinType(TYPE_UPTR));
    let u8 = asys.defs.push(Val, Definition::BuiltinType(TYPE_U8));

    let mut packages = VecMap::filled(parsed.packages.len(), Package::default());
    let vals = &mut packages[parsed.preamble].values;
    vals.insert("str".into(), str);
    vals.insert("int".into(), int);
    vals.insert("usize".into(), usize);
    vals.insert("uptr".into(), uptr);
    vals.insert("u8".into(), u8);

    // TODO: determine best order for analysing packages
    // and error on import cycles

    let mut ctx = AsysContext {
        asys,
        parsed,
        packages,
    };

    // analyze effect signatures
    for (idx, package) in parsed.packages.iter(PackageIdx) {
        // put names in scope
        // TODO: error on conflict
        for (i, effect) in package
            .effects
            .iter()
            .copied()
            .map(|idx| (idx, &parsed.effects[idx]))
        {
            // add effect to scope
            let val = ctx.asys.push_val(effect.name, Definition::Effect(i));
            ctx.packages[idx]
                .effects
                .insert(parsed.idents[effect.name].0.clone(), val);
        }
        for &implied in package.implied.iter() {
            let handler = match &parsed.exprs[implied].0 {
                Expression::Handler(handler) => handler,
                _ => panic!(),
            };
            let name = &parsed.idents[handler.effect.effect].0;
            if let Some(effect) = ctx.packages[idx].effects.get(name).copied() {
                ctx.packages[idx].implied.insert(effect);
            }
        }
    }

    // analyze function signatures
    for (idx, package) in parsed.packages.iter(PackageIdx) {
        let mut values = HashMap::new();
        values.extend(
            ctx.packages[parsed.preamble]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        values.extend(
            ctx.packages[idx]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut effects = HashMap::new();
        effects.extend(
            ctx.packages[parsed.preamble]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        effects.extend(
            ctx.packages[idx]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut scoped_effects = HashSet::new();
        scoped_effects.extend(ctx.packages[parsed.preamble].implied.iter().copied());
        scoped_effects.extend(ctx.packages[idx].implied.iter().copied());

        let global_scope = Scope {
            parent: None,
            values,
            effects: &effects,
            scoped_effects: &scoped_effects,
            pkg: idx,
        };

        for (i, effect) in package
            .effects
            .iter()
            .copied()
            .map(|idx| (idx, &parsed.effects[idx]))
        {
            for (fi, decl) in effect.functions.iter(EffFunIdx) {
                let scope = Scope {
                    parent: Some(&global_scope),
                    values: HashMap::new(),
                    effects: &effects,
                    scoped_effects: &HashSet::new(),
                    pkg: idx,
                };
                let return_type = analyze_return(&mut ctx, &scope, decl.sign.output, errors);
                let val = ctx
                    .asys
                    .push_val(decl.name, Definition::EffectFunction(i, fi, return_type));
                analyze_sign(&mut ctx, &scope, val, &decl.sign, errors);
            }
        }

        for (i, fun) in package
            .functions
            .iter()
            .copied()
            .map(|i| (i, &parsed.functions[i]))
        {
            // add function to scope
            let scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                effects: &effects,
                scoped_effects: &HashSet::new(),
                pkg: idx,
            };
            let return_type = analyze_return(&mut ctx, &scope, fun.decl.sign.output, errors);
            let val = ctx
                .asys
                .push_val(fun.decl.name, Definition::Function(i, return_type));
            ctx.packages[idx]
                .values
                .insert(parsed.idents[fun.decl.name].0.clone(), val);
            analyze_sign(&mut ctx, &scope, val, &fun.decl.sign, errors);

            // check if main
            if parsed.idents[fun.decl.name].0 == "main" {
                ctx.asys.main = Some(i);
            }
        }
    }

    // analyze effect and function bodies
    for (idx, package) in parsed.packages.iter(PackageIdx) {
        let mut values = HashMap::new();
        values.extend(
            ctx.packages[parsed.preamble]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        values.extend(
            ctx.packages[idx]
                .values
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut effects = HashMap::new();
        effects.extend(
            ctx.packages[parsed.preamble]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        effects.extend(
            ctx.packages[idx]
                .effects
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );

        let mut scoped_effects = HashSet::new();
        scoped_effects.extend(ctx.packages[parsed.preamble].implied.iter().copied());
        scoped_effects.extend(ctx.packages[idx].implied.iter().copied());

        let global_scope = Scope {
            parent: None,
            values,
            effects: &effects,
            scoped_effects: &scoped_effects,
            pkg: idx,
        };

        // analyze effects and functions
        for &implied in package.implied.iter() {
            let mut scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                effects: &effects,
                scoped_effects: &scoped_effects,
                pkg: idx,
            };
            analyze_expr(&mut ctx, &mut scope, implied, TYPE_UNKNOWN, errors);
        }
        for effect in package
            .effects
            .iter()
            .copied()
            .map(|idx| &parsed.effects[idx])
        {
            for fun in effect.functions.values() {
                let mut scope = Scope {
                    parent: Some(&global_scope),
                    values: HashMap::new(),
                    effects: &effects,
                    scoped_effects: &scoped_effects,
                    pkg: idx,
                };
                scope_sign(&mut ctx, &mut scope, &fun.sign);
            }
        }
        for fun in package
            .functions
            .iter()
            .copied()
            .map(|i| &parsed.functions[i])
        {
            let mut scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                effects: &effects,
                scoped_effects: &scoped_effects,
                pkg: idx,
            };
            let val = ctx.asys.values[fun.decl.name];
            scope_sign(&mut ctx, &mut scope, &fun.decl.sign);

            let mut scoped = scope.scoped_effects.clone();
            scoped.extend(fun.decl.sign.effects.iter().filter_map(|&i| {
                let val = ctx.asys.values[i.effect];
                if val.0 == usize::MAX {
                    None
                } else {
                    Some(val)
                }
            }));
            scope.scoped_effects = &scoped;

            let expected = match ctx.asys.defs[val] {
                Definition::Function(_, return_type) => return_type,
                _ => unreachable!(),
            };
            let found = analyze_expr(&mut ctx, &mut scope, fun.body, expected, errors);

            // set concrete handler type
            if matches!(ctx.asys.types[expected], Type::Handler(_, _, _)) {
                match &mut ctx.asys.defs[val] {
                    Definition::Function(_, typ) => *typ = found,
                    _ => unreachable!(),
                }
            }
        }
    }

    ctx.asys
}
