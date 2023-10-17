use std::collections::HashMap;

use crate::{
    error::{Error, Errors, Ranged},
    parser::{self, ExprIdx, Expression, FunSign, Ident, Op, ParseContext, AST},
    vecmap::VecMap,
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

#[derive(Debug, Clone)]
pub enum Definition {
    Parameter(Val, ParamIdx, Type),       // parameter index in function
    Variable(ExprIdx, Type),              // variable defined at expr
    Effect(EffIdx),                       // effect index in ast
    EffectFunction(Val, EffFunIdx, Type), // effect value, function index in effect
    Function(FunIdx, Type),               // function index in ast

    BuiltinEffect,     // builtin effects
    BuiltinType(Type), // builtin type
}

#[derive(Debug, Clone)]
pub enum HandlerDef {
    Handler(ExprIdx, Vec<Val>),
    Call(Val, Vec<ExprIdx>),
    Param(ParamIdx),
    Signature,
    Unknown,
}

impl HandlerDef {
    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unknown, _) => true,
            (_, Self::Unknown) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    FunctionLiteral(Val),
    Handler(Val, Box<Type>, HandlerDef),

    Int,
    Str,
    Bool,
    None,
    Never,
    Unknown,
}

impl Type {
    fn display(&self, actx: &Analysis, ast: &AST, ctx: &ParseContext) -> String {
        match *self {
            Type::FunctionLiteral(_) => "function literal".into(),

            Type::Int => "'int'".into(),
            Type::Str => "'str'".into(),
            Type::Bool => "'bool'".into(),
            Type::Handler(val, ref yeets, _) => {
                format!("'{}'", yeets.display_handler(val, actx, ast, ctx))
            }
            Type::None => "none".into(),
            Type::Never => "!".into(),
            Type::Unknown => "<unknown>".into(),
        }
    }
    fn display_fails(&self, actx: &Analysis, ast: &AST, ctx: &ParseContext) -> String {
        match *self {
            Type::FunctionLiteral(_) => " fails <unknown>".into(),
            Type::Int => " fails int".into(),
            Type::Str => " fails str".into(),
            Type::Bool => " fails bool".into(),
            Type::Handler(val, ref yeets, _) => {
                format!(" fails {}", yeets.display_handler(val, actx, ast, ctx))
            }
            Type::None => " fails".into(),
            Type::Never => "".into(),
            Type::Unknown => " fails <unknown>".into(),
        }
    }
    fn display_handler(
        &self,
        handler: Val,
        actx: &Analysis,
        ast: &AST,
        ctx: &ParseContext,
    ) -> String {
        let effect_name = match handler.0 {
            usize::MAX => "<unknown>".into(),
            _ => match actx.defs[handler] {
                Definition::Effect(e) => ctx.idents[ast.effects[e].name].0.clone(),
                _ => "<unknown>".into(),
            },
        };
        format!("{}{}", effect_name, self.display_fails(actx, ast, ctx))
    }
    fn matches(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Unknown, _) | (_, Type::Unknown) => true,
            (Type::FunctionLiteral(v1), Type::FunctionLiteral(v2)) => v1 == v2,
            (Type::Int, Type::Int) => true,
            (Type::Str, Type::Str) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::None, Type::None) => true,
            (Type::Never, Type::Never) => true,
            (Type::Handler(v1, b1, e1), Type::Handler(v2, b2, e2)) => {
                v1 == v2 && Type::matches(b1, b2) && HandlerDef::matches(e1, e2)
            }
            _ => false,
        }
    }
    fn to_param(&self) -> Type {
        match self {
            Type::Handler(effect, yeet, _) => {
                Type::Handler(effect.clone(), yeet.clone(), HandlerDef::Unknown)
            }
            _ => self.clone(),
        }
    }
    fn from_val(actx: &Analysis, val: Val) -> Type {
        match val.0 == usize::MAX {
            true => Type::Unknown,
            false => match &actx.defs[val] {
                Definition::Parameter(_, _, t) => t.clone(),
                Definition::Variable(_, t) => t.clone(),
                Definition::EffectFunction(_, _, _) => Type::FunctionLiteral(val),
                Definition::Function(_, _) => Type::FunctionLiteral(val),

                Definition::BuiltinType(_) => Type::Unknown,
                Definition::BuiltinEffect => Type::Unknown,
                Definition::Effect(_) => Type::Unknown,
            },
        }
    }
    fn from_type(
        actx: &Analysis,
        ast: &AST,
        ctx: &ParseContext,
        typ: &parser::Type,
        errors: &mut Errors,
    ) -> Self {
        let val = actx.values[typ.ident];
        let yeet_type = match typ.yeets {
            Some(parser::ReturnType::Type(typ)) => {
                Type::from_type(actx, ast, ctx, &ctx.types[typ].0, errors)
            }
            Some(parser::ReturnType::Never) => Type::Never,
            None => Type::None,
        };
        match val.0 == usize::MAX {
            true => Type::Unknown,
            false => match &actx.defs[val] {
                Definition::BuiltinType(t) => {
                    if matches!(yeet_type, Type::Never) {
                        t.clone()
                    } else {
                        errors.push(ctx.idents[typ.ident].with(Error::ExpectedEffect(
                            t.display(actx, ast, ctx),
                            val.definition_range(actx, ast, ctx),
                        )));
                        Type::Unknown
                    }
                }
                Definition::Effect(_) => {
                    if let Some(parser::ReturnType::Type(t)) = typ.yeets {
                        if !matches!(ctx.types[t].0.yeets, Some(parser::ReturnType::Never)) {
                            errors.push(ctx.types[t].with(Error::NestedHandlers));
                        }
                    }
                    Type::Handler(val, Box::new(yeet_type), HandlerDef::Unknown)
                }
                _ => {
                    errors.push(
                        ctx.idents[typ.ident]
                            .with(Error::ExpectedType(val.definition_range(actx, ast, ctx))),
                    );
                    Type::Unknown
                }
            },
        }
    }
}

pub struct Analysis {
    pub values: VecMap<Ident, Val>,
    pub defs: VecMap<Val, Definition>,
    pub types: VecMap<ExprIdx, Type>,
    pub main: Option<FunIdx>,
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
    fn definition_range(
        &self,
        actx: &Analysis,
        ast: &AST,
        ctx: &ParseContext,
    ) -> Option<Ranged<()>> {
        match actx.defs[*self] {
            Definition::Parameter(f, p, _) => match actx.defs[f] {
                Definition::EffectFunction(e, f, _) => match actx.defs[e] {
                    Definition::Effect(e) => {
                        Some(ctx.idents[ast.effects[e].functions[f].sign.inputs[p].0].empty())
                    }
                    _ => None,
                },
                Definition::Function(f, _) => {
                    Some(ctx.idents[ast.functions[f].decl.sign.inputs[p].0].empty())
                }
                _ => None,
            },
            Definition::Effect(e) => Some(ctx.idents[ast.effects[e].name].empty()),
            Definition::EffectFunction(e, f, _) => match actx.defs[e] {
                Definition::Effect(e) => Some(ctx.idents[ast.effects[e].functions[f].name].empty()),
                _ => None,
            },
            Definition::Function(f, _) => Some(ctx.idents[ast.functions[f].decl.name].empty()),
            Definition::BuiltinEffect => None,
            Definition::Variable(e, _) => match ctx.exprs[e].0 {
                Expression::Let(name, _, _) => Some(ctx.idents[name].empty()),
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
}

fn analyze_expr<'a>(
    actx: &'a mut Analysis,
    scope: &mut Scope,
    ast: &AST,
    ctx: &ParseContext,
    expr: ExprIdx,
    expected_type: &Type,
    errors: &mut Errors,
) -> &'a Type {
    let found_type = match ctx.exprs[expr].0 {
        // analyze
        Expression::Handler(ref handler) => {
            // resolve yeet
            let yeet_type =
                analyze_return(actx, ast, ctx, scope, handler.break_type.as_ref(), errors);

            if let Some(parser::ReturnType::Type(t)) = handler.break_type {
                if !matches!(ctx.types[t].0.yeets, Some(parser::ReturnType::Never)) {
                    errors.push(ctx.types[t].with(Error::NestedHandlers));
                }
            }

            // put effect in scope
            let ident = handler.effect;
            let funs = scope_effect(actx, ctx, ident, scope, errors);
            let effect = funs.as_ref().copied().map(|(e, _)| e);

            // match fun names to effect
            if let Some((effect, funs)) = funs {
                for fun in handler.functions.iter() {
                    let name = &ctx.idents[fun.decl.name].0;
                    match funs.get(name) {
                        Some(&val) => actx.values[fun.decl.name] = val,
                        None => {
                            errors.push(ctx.idents[fun.decl.name].with(Error::UnknownEffectFun(
                                effect.definition_range(actx, ast, ctx),
                                Some(ctx.idents[ident].empty()),
                            )))
                        }
                    }
                }
            }

            // analyze functions
            let mut captures = Vec::new();
            for fun in handler.functions.iter() {
                let expected =
                    analyze_return(actx, ast, ctx, scope, fun.decl.sign.output.as_ref(), errors);

                let mut child = scope.child();
                let val = actx.values[fun.decl.name];
                scope_sign(actx, &mut child, ast, ctx, val, &fun.decl.sign, errors);

                let found = analyze_expr(actx, &mut child, ast, ctx, fun.body, &expected, errors);

                // set concrete handler type
                if matches!(expected, Type::Handler(_, _, _)) {
                    let found = found.clone();
                    match &mut actx.defs[val] {
                        Definition::EffectFunction(_, _, typ) => *typ = found,
                        _ => unreachable!(),
                    }
                }

                // add captures
                ctx.for_each(fun.body, &mut |expr| {
                    if let Expression::Ident(i) = ctx.exprs[expr].0 {
                        let val = actx.values[i];

                        // capture effects from (effect) functions
                        if val.0 != usize::MAX {
                            match actx.defs[val] {
                                Definition::EffectFunction(e, _, _) => {
                                    // TODO: do not capture effect function effects
                                    if Some(e) != effect && !captures.contains(&e) {
                                        captures.push(e);
                                    }
                                }
                                Definition::Function(fun, _) => {
                                    let effects = ast.functions[fun]
                                        .decl
                                        .sign
                                        .effects
                                        .iter()
                                        .copied()
                                        .map(|i| actx.values[i]);
                                    // TODO: do not capture effect function effects
                                    for e in effects {
                                        if Some(e) != effect && !captures.contains(&e) {
                                            captures.push(e);
                                        }
                                    }
                                }
                                _ => {
                                    if scope.get(&ctx.idents[i].0) == Some(val)
                                        && !captures.contains(&val)
                                    {
                                        captures.push(val);
                                    }
                                }
                            }
                        }
                    }
                });
            }

            // get handler type
            let handler_type = match effect {
                Some(val) => Type::Handler(
                    val,
                    Box::new(yeet_type),
                    HandlerDef::Handler(expr, captures),
                ),
                None => Type::Unknown,
            };

            handler_type
        }
        Expression::Ident(ident) => {
            let name = &ctx.idents[ident].0;
            match scope.get(name) {
                Some(val) => {
                    actx.values[ident] = val;
                    Type::from_val(actx, val).clone()
                }
                None => {
                    match scope
                        .scoped_effects
                        .iter()
                        .find(|&&(ident, _)| ctx.idents[ident].0.eq(name))
                    {
                        Some((_, &(val, _))) => {
                            // handled effects may be implicitly converted to handlers that never fail
                            actx.values[ident] = val;
                            Type::Handler(val, Box::new(Type::Never), HandlerDef::Signature)
                        }
                        None => {
                            errors.push(ctx.idents[ident].with(Error::UnknownValue));
                            Type::Unknown
                        }
                    }
                }
            }
        }

        // traverse downwards
        Expression::Body(ref b) => {
            let mut child = scope.child();

            for &expr in b.main.iter() {
                analyze_expr(actx, &mut child, ast, ctx, expr, &Type::Unknown, errors);
            }
            match b.last {
                Some(expr) => {
                    analyze_expr(actx, &mut child, ast, ctx, expr, expected_type, errors).clone()
                }
                None => Type::None,
            }
        }
        Expression::Call(cexpr, ref exprs) => {
            // get function
            let fun = match ctx.exprs[cexpr].0 {
                Expression::Ident(ident) => {
                    // calling directly with an identifier
                    // when a value is not found in scope we also check within effect functions
                    let name = &ctx.idents[ident].0;
                    match scope.get(name) {
                        Some(fun) => {
                            actx.values[ident] = fun;
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
                                    ctx.idents[ident].with(Error::MultipleEffects(
                                        effect_funs
                                            .into_iter()
                                            .map(|(i, _)| ctx.idents[i].empty())
                                            .collect(),
                                    )),
                                );
                                None
                            } else if let Some(&(_, fun)) = effect_funs.first() {
                                actx.values[ident] = fun;
                                Some(fun)
                            } else {
                                errors.push(ctx.idents[ident].with(Error::UnknownValue));
                                None
                            }
                        }
                    }
                }
                _ => {
                    let fun = analyze_expr(actx, scope, ast, ctx, cexpr, &Type::Unknown, errors);
                    match fun {
                        Type::FunctionLiteral(fun) => Some(*fun),
                        Type::Unknown => None,
                        _ => {
                            errors.push(ctx.exprs[cexpr].with(Error::ExpectedFunction(
                                fun.clone().display(actx, ast, ctx),
                            )));
                            None
                        }
                    }
                }
            };
            // get function signature
            let (params, return_type) = match fun {
                Some(fun) => match actx.defs[fun] {
                    Definition::Function(fun_idx, ref return_type) => {
                        actx.types[cexpr] = Type::FunctionLiteral(fun);
                        (
                            Some(
                                ast.functions[fun_idx]
                                    .decl
                                    .sign
                                    .inputs
                                    .values()
                                    .map(|&(ident, _)| {
                                        Type::from_val(actx, actx.values[ident]).to_param()
                                    })
                                    .collect(),
                            ),
                            return_type.clone(),
                        )
                    }
                    Definition::EffectFunction(effect, fun_idx, ref return_type) => {
                        actx.types[cexpr] = Type::FunctionLiteral(fun);
                        match actx.defs[effect] {
                            Definition::Effect(eff_idx) => (
                                Some(
                                    ast.effects[eff_idx].functions[fun_idx]
                                        .sign
                                        .inputs
                                        .values()
                                        .map(|&(ident, _)| {
                                            Type::from_val(actx, actx.values[ident]).to_param()
                                        })
                                        .collect(),
                                ),
                                return_type.clone(),
                            ),
                            Definition::BuiltinEffect => match fun {
                                PUTINT => (Some(vec![Type::Int]), Type::None),
                                PUTSTR => (Some(vec![Type::Str]), Type::None),
                                _ => unreachable!(),
                            },
                            _ => unreachable!(),
                        }
                    }
                    _ => {
                        errors.push(ctx.exprs[cexpr].with(Error::ExpectedFunction(
                            Type::from_val(actx, fun).display(actx, ast, ctx),
                        )));
                        (None, Type::Unknown)
                    }
                },
                None => (None, Type::Unknown),
            };
            // handle return type as handler
            // this way different calls always return different handlers according to the type checker
            // leading to a type mismatch
            let return_type = match return_type {
                Type::Handler(val, yeet, _) => Type::Handler(
                    val,
                    yeet,
                    fun.map(|fun| HandlerDef::Call(fun, exprs.clone()))
                        .unwrap_or(HandlerDef::Unknown),
                ),
                _ => return_type,
            };
            // analyze arguments
            if let Some(params) = params {
                if params.len() != exprs.len() {
                    errors.push(
                        ctx.exprs[expr].with(Error::ParameterMismatch(params.len(), exprs.len())),
                    );
                }
                for (expr, expected) in exprs.iter().copied().zip(params.into_iter()) {
                    analyze_expr(actx, scope, ast, ctx, expr, &expected, errors);
                }
            }
            return_type
        }
        Expression::TryWith(expr, ref break_type, handler) => {
            let return_type = analyze_return(actx, ast, ctx, scope, break_type.as_ref(), errors);

            let expected_return = match return_type {
                Type::None => Type::Unknown,
                _ => return_type,
            };

            let mut child = scope.child();
            let typ = if let Some(handler) = handler {
                let handler_type =
                    analyze_expr(actx, &mut child, ast, ctx, handler, &Type::Unknown, errors);

                let handler_type = match handler_type {
                    Type::Handler(handler, break_type, _) => {
                        Some((*handler, break_type.as_ref().clone()))
                    }
                    Type::Unknown => None,
                    _ => {
                        errors.push(ctx.exprs[handler].with(Error::ExpectedHandler(
                            handler_type.clone().display(actx, ast, ctx),
                        )));
                        None
                    }
                };

                if let Some((eff_val, handler_break)) = handler_type {
                    let effect = match actx.defs[eff_val] {
                        Definition::Effect(idx) => ast.effects[idx].name,
                        _ => panic!(),
                    };

                    let expected_break = match handler_break {
                        Type::Never => expected_return.clone(),
                        _ => handler_break,
                    };

                    let mut scoped = child.scoped_effects.clone();

                    let pos = scoped.iter().position(|(_, &(v, _))| v == eff_val);
                    match pos {
                        Some(pos) => scoped[pos].0 = effect,
                        None => scoped.push((effect, &scope.effects[&ctx.idents[effect].0])),
                    }

                    child.scoped_effects = &scoped;
                    if !Type::matches(&expected_break, &expected_return) {
                        errors.push(ctx.exprs[handler].with(Error::TypeMismatch(
                            format!(
                                "'{}'",
                                expected_return.display_handler(eff_val, actx, ast, ctx)
                            ),
                            format!(
                                "'{}'",
                                expected_break.display_handler(eff_val, actx, ast, ctx)
                            ),
                        )));

                        analyze_expr(actx, &mut child, ast, ctx, expr, &expected_return, errors)
                            .clone()
                    } else {
                        analyze_expr(actx, &mut child, ast, ctx, expr, &expected_break, errors)
                            .clone()
                    }
                } else {
                    Type::Unknown
                }
            } else {
                analyze_expr(actx, &mut child, ast, ctx, expr, &expected_return, errors).clone()
            };

            if matches!(typ, Type::Handler(_, _, _)) {
                let expr = match &ctx.exprs[expr].0 {
                    Expression::Body(body) => body.last.unwrap(),
                    _ => expr,
                };

                errors.push(ctx.exprs[expr].with(Error::TryReturnsHandler));
            }

            typ
        }
        Expression::Member(expr, field) => {
            let handler = if let Expression::Ident(ident) = ctx.exprs[expr].0 {
                // getting a member directly with an identifier
                // when a value is not found in scope we also check within effects
                let name = &ctx.idents[ident].0;
                match scope.get(name) {
                    Some(val) => {
                        actx.values[ident] = val;
                        Some(val)
                    }
                    None => match scope.effects.get(name) {
                        Some(&(effect, _)) => {
                            actx.values[ident] = effect;

                            if !scope.scoped_effects.iter().any(|(_, &(v, _))| v == effect) {
                                errors.push(ctx.idents[ident].with(Error::UnhandledEffect));
                            }

                            Some(effect)
                        }
                        None => {
                            errors.push(ctx.idents[ident].with(Error::UnknownValue));
                            None
                        }
                    },
                }
            } else {
                let _out = analyze_expr(actx, scope, ast, ctx, expr, &Type::Unknown, errors);
                todo!("member");
            };

            let effect = handler.and_then(|h| match actx.defs[h] {
                Definition::Parameter(_, _, ref t) | Definition::Variable(_, ref t) => match *t {
                    Type::Handler(effect, _, _) => Some(effect),
                    Type::Unknown => None,
                    _ => {
                        // TODO: type definition
                        errors.push(
                            ctx.idents[field]
                                .with(Error::UnknownField(None, Some(ctx.exprs[expr].empty()))),
                        );
                        None
                    }
                },
                Definition::Effect(_) => Some(h),
                _ => {
                    // TODO: type definition
                    errors.push(
                        ctx.idents[field]
                            .with(Error::UnknownField(None, Some(ctx.exprs[expr].empty()))),
                    );
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

                    let name = &ctx.idents[field].0;
                    match funs.get(name).copied() {
                        Some(fun) => {
                            actx.values[field] = fun;
                            Type::FunctionLiteral(fun)
                        }
                        None => {
                            errors.push(ctx.idents[field].with(Error::UnknownEffectFun(
                                effect.definition_range(actx, ast, ctx),
                                Some(ctx.exprs[expr].empty()),
                            )));
                            Type::Unknown
                        }
                    }
                }
                None => Type::Unknown,
            }
        }
        Expression::IfElse(cond, no, yes) => {
            analyze_expr(actx, scope, ast, ctx, cond, &Type::Bool, errors);
            let yes_type = analyze_expr(actx, scope, ast, ctx, no, expected_type, errors).clone();
            let no_type = match yes {
                Some(expr) => {
                    analyze_expr(actx, scope, ast, ctx, expr, expected_type, errors).clone()
                }
                None => Type::None,
            };
            match (&yes_type, &no_type) {
                (_, _) if Type::matches(&yes_type, &no_type) => yes_type.clone(),
                (Type::Never, _) => no_type.clone(),
                (_, Type::Never) => yes_type.clone(),

                (_, _) => Type::None,
            }
        }
        Expression::Op(left, op, right) => match op {
            Op::Assign => {
                let left_type =
                    analyze_expr(actx, scope, ast, ctx, left, &Type::Unknown, errors).clone();
                analyze_expr(actx, scope, ast, ctx, right, &left_type, errors);
                Type::None
            }
            _ => {
                let (op_type, ret_type) = match op {
                    Op::Equals | Op::Less | Op::Greater => (Type::Int, Type::Bool),
                    Op::Divide | Op::Multiply | Op::Subtract | Op::Add => (Type::Int, Type::Int),
                    Op::Assign => unreachable!(),
                };
                analyze_expr(actx, scope, ast, ctx, left, &op_type, errors);
                analyze_expr(actx, scope, ast, ctx, right, &op_type, errors);
                ret_type
            }
        },
        Expression::Yeet(val) => {
            // TODO: yeet type analysis
            if let Some(expr) = val {
                analyze_expr(actx, scope, ast, ctx, expr, &Type::Unknown, errors);
            }
            Type::Never
        }
        Expression::Let(name, ref typ, expr) => {
            let val_type = match typ {
                Some(typ) => Type::from_type(actx, ast, ctx, typ, errors),
                None => Type::Unknown,
            };
            let val_type = analyze_expr(actx, scope, ast, ctx, expr, &val_type, errors).clone();

            let val = actx.push_val(name, Definition::Variable(expr, val_type));
            scope.values.insert(ctx.idents[name].0.clone(), val);
            Type::None
        }

        // these have no identifiers
        Expression::String(_) => match &expected_type {
            Type::Str => Type::Str,

            // default type for literal
            _ => Type::Str,
        },
        Expression::Int(_) => match &expected_type {
            Type::Int => Type::Int,

            // default type for literal
            _ => Type::Int,
        },
        Expression::Error => Type::Unknown,
    };

    let typ = match (expected_type, &found_type) {
        (_, _) if Type::matches(expected_type, &found_type) => found_type,
        (_, Type::Never) => expected_type.clone(),

        (_, _) => {
            errors.push(ctx.exprs[expr].with(Error::TypeMismatch(
                expected_type.display(actx, ast, ctx),
                found_type.display(actx, ast, ctx),
            )));
            expected_type.clone()
        }
    };

    actx.types[expr] = typ;
    &actx.types[expr]
}

fn scope_effect<'a>(
    actx: &mut Analysis,
    ctx: &ParseContext,
    ident: Ident,
    scope: &'a mut Scope,
    errors: &mut Errors,
) -> Option<(Val, &'a HashMap<String, Val>)> {
    let name = &ctx.idents[ident].0;
    match scope.effects.get(name) {
        Some(&(val, ref vec)) => {
            actx.values[ident] = val;
            Some((val, vec))
        }
        None => {
            errors.push(ctx.idents[ident].with(Error::UnknownEffect));
            None
        }
    }
}

fn analyze_return(
    actx: &mut Analysis,
    ast: &AST,
    ctx: &ParseContext,
    scope: &Scope,
    output: Option<&parser::ReturnType>,
    errors: &mut Errors,
) -> Type {
    match output {
        Some(&parser::ReturnType::Type(typ)) => {
            analyze_type(actx, ast, ctx, scope, &ctx.types[typ].0, errors)
        }
        Some(parser::ReturnType::Never) => Type::Never,
        None => Type::None,
    }
}

fn analyze_type(
    actx: &mut Analysis,
    ast: &AST,
    ctx: &ParseContext,
    scope: &Scope,
    typ: &parser::Type,
    errors: &mut Errors,
) -> Type {
    let name = &ctx.idents[typ.ident].0;

    // check scope
    match scope.get(name) {
        Some(val) => actx.values[typ.ident] = val,

        // check effects
        None => match scope.effects.get(name) {
            Some(&(val, _)) => actx.values[typ.ident] = val,
            None => errors.push(ctx.idents[typ.ident].with(Error::UnknownType)),
        },
    }

    Type::from_type(actx, ast, ctx, typ, errors)
}

fn scope_sign(
    actx: &mut Analysis,
    scope: &mut Scope,
    ast: &AST,
    ctx: &ParseContext,
    val: Val,
    func: &FunSign,
    errors: &mut Errors,
) {
    // put effects in scope
    for &effect in func.effects.iter() {
        scope_effect(actx, ctx, effect, scope, errors);
    }

    // put args in scope
    for (i, &(param, typ)) in func.inputs.values().enumerate() {
        // resolve type
        let typ = analyze_type(actx, ast, ctx, scope, &ctx.types[typ].0, errors);
        let typ = match typ {
            Type::Handler(effect, yeet, _) => {
                Type::Handler(effect, yeet, HandlerDef::Param(ParamIdx(i)))
            }
            typ => typ,
        };

        // add parameter to scope
        scope.values.insert(
            ctx.idents[param].0.clone(),
            actx.push_val(param, Definition::Parameter(val, ParamIdx(i), typ)),
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

pub fn analyze(ast: &AST, ctx: &ParseContext, errors: &mut Errors) -> Analysis {
    let mut actx = Analysis {
        values: VecMap::filled(ctx.idents.len(), Val(usize::MAX)),
        types: VecMap::filled(ctx.exprs.len(), Type::Unknown),
        defs: VecMap::new(),
        main: None,
    };

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

    actx.defs = VecMap::filled(5, Definition::BuiltinEffect);
    actx.defs[PUTINT] = Definition::EffectFunction(DEBUG, EffFunIdx(0), Type::None);
    actx.defs[PUTSTR] = Definition::EffectFunction(DEBUG, EffFunIdx(1), Type::None);
    actx.defs[STR] = Definition::BuiltinType(Type::Str);
    actx.defs[INT] = Definition::BuiltinType(Type::Int);

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
        let val = actx.push_val(effect.name, Definition::Effect(EffIdx(i)));
        effects.insert(ctx.idents[effect.name].0.clone(), (val, HashMap::new()));
    }
    for effect in ast.effects.values() {
        // add effect to scope
        let val = actx.values[effect.name];
        let name = &ctx.idents[effect.name].0;

        // remember effect functions
        for (i, func) in effect.functions.values().enumerate() {
            let scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                effects: &effects,
                scoped_effects: &scoped_effects,
            };
            let return_type = analyze_return(
                &mut actx,
                ast,
                ctx,
                &scope,
                func.sign.output.as_ref(),
                errors,
            );
            effects.get_mut(name).unwrap().1.insert(
                ctx.idents[func.name].0.clone(),
                actx.push_val(
                    func.name,
                    Definition::EffectFunction(val, EffFunIdx(i), return_type),
                ),
            );
        }
    }
    for &implied in ast.implied.iter() {
        let handler = match &ctx.exprs[implied].0 {
            Expression::Handler(handler) => handler,
            _ => panic!(),
        };
        let name = &ctx.idents[handler.effect].0;
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
        let return_type = analyze_return(
            &mut actx,
            ast,
            ctx,
            &scope,
            func.decl.sign.output.as_ref(),
            errors,
        );
        global_scope.values.insert(
            ctx.idents[func.decl.name].0.clone(),
            actx.push_val(func.decl.name, Definition::Function(FunIdx(i), return_type)),
        );

        // check if main
        if ctx.idents[func.decl.name].0 == "main" {
            actx.main = Some(FunIdx(i));
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
        analyze_expr(
            &mut actx,
            &mut scope,
            &ast,
            &ctx,
            implied,
            &Type::Unknown,
            errors,
        );
    }
    for effect in ast.effects.values() {
        for fun in effect.functions.values() {
            let mut scope = Scope {
                parent: Some(&global_scope),
                values: HashMap::new(),
                effects: &effects,
                scoped_effects: &scoped_effects,
            };
            let val = actx.values[fun.name];
            scope_sign(&mut actx, &mut scope, ast, ctx, val, &fun.sign, errors);
        }
    }
    for fun in ast.functions.values() {
        let mut scope = Scope {
            parent: Some(&global_scope),
            values: HashMap::new(),
            effects: &effects,
            scoped_effects: &scoped_effects,
        };
        let val = actx.values[fun.decl.name];
        scope_sign(&mut actx, &mut scope, ast, ctx, val, &fun.decl.sign, errors);

        let mut scoped = scope.scoped_effects.clone();
        scoped.extend(fun.decl.sign.effects.iter().filter_map(|&i| {
            scope
                .effects
                .get(&ctx.idents[i].0)
                .map(|effect| (i, effect))
        }));
        scope.scoped_effects = &scoped;

        let expected = match actx.defs[val] {
            Definition::Function(_, ref return_type) => return_type.clone(),
            _ => unreachable!(),
        };
        let found = analyze_expr(&mut actx, &mut scope, ast, ctx, fun.body, &expected, errors);

        // set concrete handler type
        if matches!(expected, Type::Handler(_, _, _)) {
            let found = found.clone();
            match &mut actx.defs[val] {
                Definition::Function(_, typ) => *typ = found,
                _ => unreachable!(),
            }
        }
    }

    actx
}
