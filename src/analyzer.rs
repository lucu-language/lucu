use std::collections::HashMap;

use crate::{
    error::{Error, Errors, Ranged},
    parser::{self, BinOp, ExprIdx, Expression, FunSign, Ident, Parsed, UnOp, AST},
    vecmap::{VecMap, VecSet},
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Val(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ParamIdx(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct FunIdx(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct EffIdx(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct EffFunIdx(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct TypeIdx(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct HandlerIdx(usize);

impl From<Val> for usize {
    fn from(value: Val) -> Self {
        value.0
    }
}

impl From<ParamIdx> for usize {
    fn from(value: ParamIdx) -> Self {
        value.0
    }
}

impl From<FunIdx> for usize {
    fn from(value: FunIdx) -> Self {
        value.0
    }
}

impl From<EffIdx> for usize {
    fn from(value: EffIdx) -> Self {
        value.0
    }
}

impl From<EffFunIdx> for usize {
    fn from(value: EffFunIdx) -> Self {
        value.0
    }
}

impl From<TypeIdx> for usize {
    fn from(value: TypeIdx) -> Self {
        value.0
    }
}

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
            Type::Int => "int".into(),
            Type::Str => "str".into(),
            Type::Bool => "bool".into(),
            Type::Handler(val, yeets, _) => yeets.display_handler(val, ctx),
            Type::None => "()".into(),
            Type::Never => "!".into(),
            Type::Unknown => "<unknown>".into(),
            Type::Pointer(ty) => format!("^{}", ty.display_inner(ctx)),
            Type::ConstArray(size, ty) => format!("[{}]{}", size, ty.display_inner(ctx)),
        }
    }
    fn display_handler(self, handler: Val, ctx: &AsysContext) -> String {
        let effect_name = match handler.0 {
            usize::MAX => "<unknown>".into(),
            _ => match ctx.asys.defs[handler] {
                Definition::Effect(e) => ctx.parsed.idents[ctx.ast.effects[e].name].0.clone(),
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
                Definition::BuiltinEffect => TYPE_UNKNOWN,
                Definition::Effect(_) => TYPE_UNKNOWN,
            },
        }
    }
}

impl From<HandlerIdx> for usize {
    fn from(value: HandlerIdx) -> Self {
        value.0
    }
}

#[derive(Debug, Clone)]
pub enum Definition {
    Parameter(Val, ParamIdx, TypeIdx), // parameter index in function
    Variable(bool, ExprIdx, TypeIdx),  // variable defined at expr
    Effect(EffIdx),                    // effect index in ast
    EffectFunction(Val, EffFunIdx, TypeIdx), // effect value, function index in effect
    Function(FunIdx, TypeIdx),         // function index in ast

    BuiltinEffect,        // builtin effects
    BuiltinType(TypeIdx), // builtin type
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
    Handler(Val, TypeIdx, Option<HandlerIdx>),

    Pointer(TypeIdx),
    ConstArray(u64, TypeIdx),

    Int,
    Str,
    Bool,
    None,
    Never,
    Unknown,
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
    ast: &'a AST,
    parsed: &'a Parsed,
}

struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    values: HashMap<String, Val>,
    effects: &'a HashMap<String, (Val, HashMap<String, Val>)>,
    scoped_effects: &'a Vec<(Ident, &'a (Val, HashMap<String, Val>))>,
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
        }
    }
}

impl Val {
    fn definition_range(&self, ctx: &AsysContext) -> Option<Ranged<()>> {
        match ctx.asys.defs[*self] {
            Definition::Parameter(f, p, _) => match ctx.asys.defs[f] {
                Definition::EffectFunction(e, f, _) => match ctx.asys.defs[e] {
                    Definition::Effect(e) => Some(
                        ctx.parsed.idents[ctx.ast.effects[e].functions[f].sign.inputs[p].0].empty(),
                    ),
                    _ => None,
                },
                Definition::Function(f, _) => {
                    Some(ctx.parsed.idents[ctx.ast.functions[f].decl.sign.inputs[p].0].empty())
                }
                _ => None,
            },
            Definition::Effect(e) => Some(ctx.parsed.idents[ctx.ast.effects[e].name].empty()),
            Definition::EffectFunction(e, f, _) => match ctx.asys.defs[e] {
                Definition::Effect(e) => {
                    Some(ctx.parsed.idents[ctx.ast.effects[e].functions[f].name].empty())
                }
                _ => None,
            },
            Definition::Function(f, _) => {
                Some(ctx.parsed.idents[ctx.ast.functions[f].decl.name].empty())
            }
            Definition::BuiltinEffect => None,
            Definition::Variable(_, e, _) => match ctx.parsed.exprs[e].0 {
                Expression::Let(_, name, _, _) => Some(ctx.parsed.idents[name].empty()),
                _ => None,
            },
            Definition::BuiltinType(_) => None,
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
            analyze_expr(ctx, scope, right, TYPE_INT, errors);

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
                if Some(e) != effect && scope.scoped_effects.iter().any(|(_, &(val, _))| e == val) {
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
                let effects = ctx.ast.functions[fun]
                    .decl
                    .sign
                    .effects
                    .iter()
                    .copied()
                    .map(|i| ctx.asys.values[i]);
                for e in effects {
                    if Some(e) != effect
                        && scope.scoped_effects.iter().any(|(_, &(val, _))| e == val)
                    {
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
            Definition::BuiltinEffect => todo!(),
            Definition::BuiltinType(_) => {}
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
            let funs = scope_effect(ctx, ident, scope, errors);
            let effect = funs.as_ref().copied().map(|(e, _)| e);

            // match fun names to effect
            if let Some((effect, funs)) = funs {
                for fun in handler.functions.iter() {
                    let name = &ctx.parsed.idents[fun.decl.name].0;
                    match funs.get(name) {
                        Some(&val) => ctx.asys.values[fun.decl.name] = val,
                        None => errors.push(ctx.parsed.idents[fun.decl.name].with(
                            Error::UnknownEffectFun(
                                effect.definition_range(ctx),
                                Some(ctx.parsed.idents[ident].empty()),
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
                scope_sign(ctx, &mut child, val, &fun.decl.sign, errors);

                let mut scoped = scope.scoped_effects.clone();
                scoped.extend(fun.decl.sign.effects.iter().copied().filter_map(|i| {
                    scope
                        .effects
                        .get(&ctx.parsed.idents[i].0)
                        .map(|effect| (i, effect))
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
                ctx.parsed
                    .for_each(fun.body, &mut |expr| match ctx.parsed.exprs[expr].0 {
                        Expression::Ident(id) => {
                            capture_ident(ctx, scope, id, effect, &mut captures);
                        }
                        _ => {}
                    });
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
                        .find(|&&(ident, _)| ctx.parsed.idents[ident].0.eq(name))
                    {
                        Some((_, &(val, _))) => {
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
                                .flat_map(|&(i, &(_, ref h))| {
                                    h.iter().map(move |(s, &v)| (i, s, v))
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
            let (params, return_type) = match fun {
                Some(fun) => match ctx.asys.defs[fun] {
                    Definition::Function(fun_idx, return_type) => {
                        ctx.asys.exprs[cexpr] = ctx.asys.insert_type(Type::FunctionLiteral(fun));
                        (
                            Some(
                                ctx.ast.functions[fun_idx]
                                    .decl
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|&(ident, _)| {
                                        TypeIdx::from_val(ctx, ctx.asys.values[ident]).to_base(ctx)
                                    })
                                    .collect(),
                            ),
                            return_type,
                        )
                    }
                    Definition::EffectFunction(effect, fun_idx, return_type) => {
                        ctx.asys.exprs[cexpr] = ctx.asys.insert_type(Type::FunctionLiteral(fun));
                        match ctx.asys.defs[effect] {
                            Definition::Effect(eff_idx) => (
                                Some(
                                    ctx.ast.effects[eff_idx].functions[fun_idx]
                                        .sign
                                        .inputs
                                        .values()
                                        .map(|&(ident, _)| {
                                            TypeIdx::from_val(ctx, ctx.asys.values[ident])
                                                .to_base(ctx)
                                        })
                                        .collect(),
                                ),
                                return_type,
                            ),
                            Definition::BuiltinEffect => match fun {
                                PUTINT => (Some(vec![TYPE_INT]), TYPE_NONE),
                                PUTSTR => (Some(vec![TYPE_STR]), TYPE_NONE),
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        }
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
                        Definition::Effect(idx) => ctx.ast.effects[idx].name,
                        _ => panic!(),
                    };

                    let expected_break = match ctx.asys.types[handler_break] {
                        Type::Never => expected_return,
                        _ => handler_break,
                    };

                    let mut scoped = child.scoped_effects.clone();

                    let pos = scoped.iter().position(|(_, &(v, _))| v == eff_val);
                    match pos {
                        Some(pos) => scoped[pos].0 = effect,
                        None => scoped.push((effect, &scope.effects[&ctx.parsed.idents[effect].0])),
                    }

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
                        Some(val)
                    }
                    None => match scope.effects.get(name) {
                        Some(&(effect, _)) => {
                            ctx.asys.values[ident] = effect;

                            if !scope.scoped_effects.iter().any(|(_, &(v, _))| v == effect) {
                                errors.push(ctx.parsed.idents[ident].with(Error::UnhandledEffect));
                            }

                            Some(effect)
                        }
                        None => {
                            errors.push(ctx.parsed.idents[ident].with(Error::UnknownValue));
                            None
                        }
                    },
                }
            } else {
                let _out = analyze_expr(ctx, scope, expr, TYPE_UNKNOWN, errors);
                todo!("member");
            };

            let effect = handler.and_then(|h| match ctx.asys.defs[h] {
                Definition::Parameter(_, _, t) | Definition::Variable(_, _, t) => {
                    match ctx.asys.types[t] {
                        Type::Handler(effect, _, _) => Some(effect),
                        Type::Unknown => None,
                        _ => {
                            // TODO: type definition
                            errors.push(ctx.parsed.idents[field].with(Error::UnknownField(
                                None,
                                Some(ctx.parsed.exprs[expr].empty()),
                            )));
                            None
                        }
                    }
                }
                Definition::Effect(_) => Some(h),
                Definition::BuiltinEffect => None,
                _ => {
                    // TODO: type definition
                    errors.push(ctx.parsed.idents[field].with(Error::UnknownField(
                        None,
                        Some(ctx.parsed.exprs[expr].empty()),
                    )));
                    None
                }
            });

            match effect {
                Some(effect) => {
                    let funs = &scope
                        .effects
                        .values()
                        .find(|&&(e, _)| e == effect)
                        .expect("unknown effect value")
                        .1;

                    let name = &ctx.parsed.idents[field].0;
                    match funs.get(name).copied() {
                        Some(fun) => {
                            ctx.asys.values[field] = fun;
                            ctx.asys.insert_type(Type::FunctionLiteral(fun))
                        }
                        None => {
                            errors.push(ctx.parsed.idents[field].with(Error::UnknownEffectFun(
                                effect.definition_range(ctx),
                                Some(ctx.parsed.exprs[expr].empty()),
                            )));
                            TYPE_UNKNOWN
                        }
                    }
                }
                None => TYPE_UNKNOWN,
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
                analyze_expr(ctx, scope, right, TYPE_INT, errors);

                match ctx.asys.types[array] {
                    Type::ConstArray(_, ty) => ty,
                    Type::Unknown => TYPE_UNKNOWN,
                    _ => {
                        // TODO: error
                        TYPE_UNKNOWN
                    }
                }
            }
            _ => {
                let (op_type, ret_type) = match op {
                    BinOp::Equals | BinOp::Less | BinOp::Greater => (TYPE_INT, TYPE_BOOL),
                    BinOp::Divide | BinOp::Multiply | BinOp::Subtract | BinOp::Add => {
                        (TYPE_INT, TYPE_INT)
                    }
                    BinOp::Assign | BinOp::Index => unreachable!(),
                };
                analyze_expr(ctx, scope, left, op_type, errors);
                analyze_expr(ctx, scope, right, op_type, errors);
                ret_type
            }
        },
        Expression::UnOp(uexpr, op) => match op {
            UnOp::PostIncrement => analyze_assignable(ctx, scope, uexpr, expr, errors),
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
        Expression::Int(_) => match ctx.asys.types[expected_type] {
            Type::Int => TYPE_INT,

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

fn scope_effect<'a>(
    ctx: &mut AsysContext,
    ident: Ident,
    scope: &'a mut Scope,
    errors: &mut Errors,
) -> Option<(Val, &'a HashMap<String, Val>)> {
    let name = &ctx.parsed.idents[ident].0;
    match scope.effects.get(name) {
        Some(&(val, ref vec)) => {
            ctx.asys.values[ident] = val;
            Some((val, vec))
        }
        None => {
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
            Some(&(val, _)) => {
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

fn scope_sign(
    ctx: &mut AsysContext,
    scope: &mut Scope,
    val: Val,
    func: &FunSign,
    errors: &mut Errors,
) {
    // put effects in scope
    for &effect in func.effects.iter() {
        scope_effect(ctx, effect, scope, errors);
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

        // add parameter to scope
        scope.values.insert(
            ctx.parsed.idents[param].0.clone(),
            ctx.asys
                .push_val(param, Definition::Parameter(val, ParamIdx(i), typ)),
        );
    }
}

pub const STR: Val = Val(0);
pub const INT: Val = Val(1);

pub const DEBUG: Val = Val(2);
pub const PUTINT: Val = Val(3);
pub const PUTSTR: Val = Val(4);

pub const PUTINT_IDX: EffFunIdx = EffFunIdx(0);
pub const PUTSTR_IDX: EffFunIdx = EffFunIdx(1);

pub const TYPE_NONE: TypeIdx = TypeIdx(1);
pub const TYPE_NEVER: TypeIdx = TypeIdx(2);

const TYPE_UNKNOWN: TypeIdx = TypeIdx(0);
const TYPE_INT: TypeIdx = TypeIdx(3);
const TYPE_STR: TypeIdx = TypeIdx(4);
const TYPE_BOOL: TypeIdx = TypeIdx(5);

pub fn analyze(ast: &AST, parsed: &Parsed, errors: &mut Errors) -> Analysis {
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

    let mut effects = HashMap::new();
    let mut values = HashMap::new();
    let mut scoped_effects = Vec::new();

    // built-in values
    values.insert("str".to_owned(), STR);
    values.insert("int".to_owned(), INT);

    let mut debug = HashMap::new();
    debug.insert("putint".to_owned(), PUTINT);
    debug.insert("putstr".to_owned(), PUTSTR);
    effects.insert("debug".to_owned(), (DEBUG, debug));

    asys.defs = VecMap::filled(5, Definition::BuiltinEffect);
    asys.defs[PUTINT] = Definition::EffectFunction(DEBUG, EffFunIdx(0), TYPE_NONE);
    asys.defs[PUTSTR] = Definition::EffectFunction(DEBUG, EffFunIdx(1), TYPE_NONE);
    asys.defs[STR] = Definition::BuiltinType(TYPE_STR);
    asys.defs[INT] = Definition::BuiltinType(TYPE_INT);

    let mut ctx = AsysContext { asys, ast, parsed };

    let mut global_scope = Scope {
        parent: None,
        values,
        effects: &HashMap::new(),
        scoped_effects: &Vec::new(),
    };

    // put names in scope
    // TODO: error on conflict
    for (i, effect) in ast.effects.values().enumerate() {
        // add effect to scope
        let val = ctx
            .asys
            .push_val(effect.name, Definition::Effect(EffIdx(i)));
        effects.insert(parsed.idents[effect.name].0.clone(), (val, HashMap::new()));
    }
    for effect in ast.effects.values() {
        // add effect to scope
        let val = ctx.asys.values[effect.name];
        let name = &parsed.idents[effect.name].0;

        // remember effect functions
        for (i, func) in effect.functions.values().enumerate() {
            let scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                effects: &effects,
                scoped_effects: &scoped_effects,
            };
            let return_type = analyze_return(&mut ctx, &scope, func.sign.output, errors);
            effects.get_mut(name).unwrap().1.insert(
                parsed.idents[func.name].0.clone(),
                ctx.asys.push_val(
                    func.name,
                    Definition::EffectFunction(val, EffFunIdx(i), return_type),
                ),
            );
        }
    }
    for &implied in ast.implied.iter() {
        let handler = match &parsed.exprs[implied].0 {
            Expression::Handler(handler) => handler,
            _ => panic!(),
        };
        let name = &parsed.idents[handler.effect].0;
        if let Some(effect) = effects.get(name) {
            scoped_effects.push((handler.effect, effect));
        }
    }
    for (i, func) in ast.functions.values().enumerate() {
        // add function to scope
        let scope = Scope {
            parent: Some(&global_scope),
            values: HashMap::new(),
            effects: &effects,
            scoped_effects: &scoped_effects,
        };
        let return_type = analyze_return(&mut ctx, &scope, func.decl.sign.output, errors);
        global_scope.values.insert(
            parsed.idents[func.decl.name].0.clone(),
            ctx.asys
                .push_val(func.decl.name, Definition::Function(FunIdx(i), return_type)),
        );

        // check if main
        if parsed.idents[func.decl.name].0 == "main" {
            ctx.asys.main = Some(FunIdx(i));
        }
    }

    // analyze effects and functions
    for &implied in ast.implied.iter() {
        let mut scope = Scope {
            parent: Some(&global_scope),
            values: HashMap::new(),
            effects: &effects,
            scoped_effects: &scoped_effects,
        };
        analyze_expr(&mut ctx, &mut scope, implied, TYPE_UNKNOWN, errors);
    }
    for effect in ast.effects.values() {
        for fun in effect.functions.values() {
            let mut scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                effects: &effects,
                scoped_effects: &scoped_effects,
            };
            let val = ctx.asys.values[fun.name];
            scope_sign(&mut ctx, &mut scope, val, &fun.sign, errors);
        }
    }
    for fun in ast.functions.values() {
        let mut scope = Scope {
            parent: Some(&global_scope),
            values: HashMap::new(),
            effects: &effects,
            scoped_effects: &scoped_effects,
        };
        let val = ctx.asys.values[fun.decl.name];
        scope_sign(&mut ctx, &mut scope, val, &fun.decl.sign, errors);

        let mut scoped = scope.scoped_effects.clone();
        scoped.extend(fun.decl.sign.effects.iter().filter_map(|&i| {
            scope
                .effects
                .get(&parsed.idents[i].0)
                .map(|effect| (i, effect))
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

    ctx.asys
}
