use std::collections::HashMap;

use crate::{
    error::{Error, Errors, Ranged},
    parser::{ExprIdx, Expression, FunSign, Ident, ParseContext, ReturnType, AST},
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
    Parameter(Val, ParamIdx),       // parameter index in function
    Effect(EffIdx),                 // effect index in ast
    EffectFunction(Val, EffFunIdx), // effect value, function index in effect
    Function(FunIdx),               // function index in ast

    Builtin, // builtin effects
}

pub struct Analysis {
    pub values: VecMap<Ident, Val>,
    pub defs: VecMap<Val, Definition>,
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
            Definition::Parameter(f, p) => match actx.defs[f] {
                Definition::EffectFunction(e, f) => match actx.defs[e] {
                    Definition::Effect(e) => {
                        Some(ctx.idents[ast.effects[e].functions[f].sign.inputs[p].0].empty())
                    }
                    _ => None,
                },
                Definition::Function(f) => {
                    Some(ctx.idents[ast.functions[f].decl.sign.inputs[p].0].empty())
                }
                _ => None,
            },
            Definition::Effect(e) => Some(ctx.idents[ast.effects[e].name].empty()),
            Definition::EffectFunction(e, f) => match actx.defs[e] {
                Definition::Effect(e) => Some(ctx.idents[ast.effects[e].functions[f].name].empty()),
                _ => None,
            },
            Definition::Function(f) => Some(ctx.idents[ast.functions[f].decl.name].empty()),
            Definition::Builtin => None,
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

fn analyze_expr(
    actx: &mut Analysis,
    scope: &mut Scope,
    ast: &AST,
    ctx: &ParseContext,
    expr: ExprIdx,
    errors: &mut Errors,
) {
    match ctx.exprs[expr].0 {
        // analyze
        Expression::Handler(ref handler) => {
            // resolve return
            match handler.break_type {
                Some(ReturnType::Type(ref typ)) => {
                    let name = &ctx.idents[typ.ident].0;
                    match scope.get(name) {
                        Some(val) => actx.values[typ.ident] = val,
                        None => errors.push(ctx.idents[typ.ident].with(Error::UnknownValue)),
                    }
                }
                _ => {}
            }

            // put effect in scope
            let ident = handler.effect;
            let funs = scope_effect(actx, ctx, ident, scope, errors);

            // match fun names to effect
            if let Some((effect, funs)) = funs {
                for fun in handler.functions.iter() {
                    let name = &ctx.idents[fun.decl.name].0;
                    match funs.get(name) {
                        Some(&val) => actx.values[fun.decl.name] = val,
                        None => {
                            errors.push(ctx.idents[fun.decl.name].with(Error::UnknownEffectFun(
                                ctx.idents[handler.effect].empty(),
                                effect.definition_range(actx, ast, ctx),
                            )))
                        }
                    }
                }
            }

            // analyze functions
            for fun in handler.functions.iter() {
                let mut scope = scope.child();
                let val = actx.values[fun.decl.name];
                scope_sign(actx, &mut scope, ctx, val, &fun.decl.sign, errors);
                analyze_expr(actx, &mut scope, ast, ctx, fun.body, errors);
            }
        }
        Expression::Ident(ident) => {
            let name = &ctx.idents[ident].0;
            match scope.get(name) {
                Some(val) => actx.values[ident] = val,
                None => {
                    // check among effects
                    let effect_funs = scope
                        .scoped_effects
                        .iter()
                        .flat_map(|&(i, &(_, ref h))| h.iter().map(move |(s, &v)| (i, s, v)))
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
                        )
                    } else if let Some(&(_, fun)) = effect_funs.first() {
                        actx.values[ident] = fun;
                    } else {
                        errors.push(ctx.idents[ident].with(Error::UnknownValue))
                    }
                }
            }
        }

        // traverse downwards
        Expression::Body(ref b) => {
            let mut child = scope.child();

            for &expr in b.main.iter() {
                analyze_expr(actx, &mut child, ast, ctx, expr, errors);
            }
            if let Some(expr) = b.last {
                analyze_expr(actx, &mut child, ast, ctx, expr, errors);
            }
        }
        Expression::Call(expr, ref exprs) => {
            analyze_expr(actx, scope, ast, ctx, expr, errors);
            for &expr in exprs {
                analyze_expr(actx, scope, ast, ctx, expr, errors);
            }
        }
        Expression::TryWith(expr, handler) => {
            let mut child = scope.child();

            if let Some(handler) = handler {
                analyze_expr(actx, &mut child, ast, ctx, handler, errors);

                // TODO: first class handlers
                let Expression::Handler(ref handler) = ctx.exprs[handler].0 else { panic!() };
                let mut scoped = child.scoped_effects.clone();
                let val = actx.values[handler.effect];

                if val.0 != usize::MAX {
                    let pos = scoped.iter().position(|(_, &(v, _))| v == val);
                    match pos {
                        Some(pos) => scoped[pos].0 = handler.effect,
                        None => scoped.push((
                            handler.effect,
                            &scope.effects[&ctx.idents[handler.effect].0],
                        )),
                    }
                }

                child.scoped_effects = &scoped;
                analyze_expr(actx, &mut child, ast, ctx, expr, errors);
            } else {
                analyze_expr(actx, &mut child, ast, ctx, expr, errors);
            }
        }
        Expression::Member(expr, field) => {
            if let Expression::Ident(ident) = ctx.exprs[expr].0 {
                // TODO: for now we assume the ident is of an effect
                let name = &ctx.idents[ident].0;
                match scope.effects.get(name) {
                    Some(&(effect, ref funs)) => {
                        actx.values[ident] = effect;

                        if !scope.scoped_effects.iter().any(|(_, &(v, _))| v == effect) {
                            errors.push(ctx.idents[ident].with(Error::UnhandledEffect));
                        }

                        let name = &ctx.idents[field].0;
                        match funs.get(name).copied() {
                            Some(fun) => {
                                actx.values[field] = fun;
                            }
                            None => errors.push(ctx.idents[field].with(Error::UnknownEffectFun(
                                ctx.idents[ident].empty(),
                                effect.definition_range(actx, ast, ctx),
                            ))),
                        }
                    }
                    None => errors.push(ctx.idents[ident].with(Error::UnknownEffect)),
                }
            } else {
                todo!("member");
            }
        }
        Expression::IfElse(cond, no, yes) => {
            analyze_expr(actx, scope, ast, ctx, cond, errors);
            analyze_expr(actx, scope, ast, ctx, no, errors);
            if let Some(expr) = yes {
                analyze_expr(actx, scope, ast, ctx, expr, errors);
            }
        }
        Expression::Op(left, _, right) => {
            analyze_expr(actx, scope, ast, ctx, left, errors);
            analyze_expr(actx, scope, ast, ctx, right, errors);
        }
        Expression::Yeet(val) => {
            if let Some(expr) = val {
                analyze_expr(actx, scope, ast, ctx, expr, errors);
            }
        }

        // these have no identifiers'
        Expression::String(_) => {}
        Expression::Error => {}
        Expression::Int(_) => {}
    }
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

fn scope_sign(
    actx: &mut Analysis,
    scope: &mut Scope,
    ctx: &ParseContext,
    val: Val,
    func: &FunSign,
    errors: &mut Errors,
) {
    // put effects in scope
    for &effect in func.effects.iter() {
        scope_effect(actx, ctx, effect, scope, errors);
    }

    // resolve return
    match func.output {
        Some(ReturnType::Type(ref typ)) => {
            let name = &ctx.idents[typ.ident].0;
            match scope.get(name) {
                Some(val) => actx.values[typ.ident] = val,
                None => errors.push(ctx.idents[typ.ident].with(Error::UnknownValue)),
            }
        }
        _ => {}
    }

    // put args in scope
    for (i, &(param, ref typ)) in func.inputs.values().enumerate() {
        // resolve type
        let name = &ctx.idents[typ.ident].0;
        match scope.get(name) {
            Some(val) => actx.values[typ.ident] = val,
            None => errors.push(ctx.idents[typ.ident].with(Error::UnknownValue)),
        }

        // add parameter to scope
        scope.values.insert(
            ctx.idents[param].0.clone(),
            actx.push_val(param, Definition::Parameter(val, ParamIdx(i))),
        );
    }
}

pub const STR: Val = Val(0);
pub const INT: Val = Val(1);

pub const DEBUG: Val = Val(2);
pub const PUTINT: Val = Val(3);
pub const PUTSTR: Val = Val(4);

pub fn analyze(ast: &AST, ctx: &ParseContext, errors: &mut Errors) -> Analysis {
    let mut actx = Analysis {
        values: VecMap::filled(ctx.idents.len(), Val(usize::MAX)),
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

    actx.defs = VecMap::filled(5, Definition::Builtin);
    actx.defs[PUTINT] = Definition::EffectFunction(DEBUG, EffFunIdx(0));
    actx.defs[PUTSTR] = Definition::EffectFunction(DEBUG, EffFunIdx(1));

    // put names in scope
    // TODO: error on conflict
    for (i, effect) in ast.effects.values().enumerate() {
        // add effect to scope
        let val = actx.push_val(effect.name, Definition::Effect(EffIdx(i)));

        // remember effect functions
        let mut funcs = HashMap::new();
        for (i, func) in effect.functions.values().enumerate() {
            funcs.insert(
                ctx.idents[func.name].0.clone(),
                actx.push_val(func.name, Definition::EffectFunction(val, EffFunIdx(i))),
            );
        }

        effects.insert(ctx.idents[effect.name].0.clone(), (val, funcs));
    }
    for &implied in ast.implied.iter() {
        // TODO: first class handlers
        let Expression::Handler(handler) = &ctx.exprs[implied].0 else { panic!() };
        let name = &ctx.idents[handler.effect].0;
        if let Some(effect) = effects.get(name) {
            scoped_effects.push((handler.effect, effect));
        }
    }
    for (i, func) in ast.functions.values().enumerate() {
        // add function to scope
        values.insert(
            ctx.idents[func.decl.name].0.clone(),
            actx.push_val(func.decl.name, Definition::Function(FunIdx(i))),
        );

        // check if main
        if ctx.idents[func.decl.name].0 == "main" {
            actx.main = Some(FunIdx(i));
        }
    }

    // analyze effects and functions
    let mut scope = Scope {
        parent: None,
        values,
        effects: &effects,
        scoped_effects: &scoped_effects,
    };

    for &implied in ast.implied.iter() {
        analyze_expr(&mut actx, &mut scope, &ast, &ctx, implied, errors);
    }
    for effect in ast.effects.values() {
        for fun in effect.functions.values() {
            let mut scope = scope.child();
            let val = actx.values[fun.name];
            scope_sign(&mut actx, &mut scope, ctx, val, &fun.sign, errors);
        }
    }
    for fun in ast.functions.values() {
        let mut scope = scope.child();
        let val = actx.values[fun.decl.name];
        scope_sign(&mut actx, &mut scope, ctx, val, &fun.decl.sign, errors);

        let mut scoped = scope.scoped_effects.clone();
        scoped.extend(fun.decl.sign.effects.iter().filter_map(|&i| {
            scope
                .effects
                .get(&ctx.idents[i].0)
                .map(|effect| (i, effect))
        }));
        scope.scoped_effects = &scoped;
        analyze_expr(&mut actx, &mut scope, ast, ctx, fun.body, errors);
    }

    actx
}
