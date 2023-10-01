use std::collections::HashMap;

use crate::{
    error::{Error, Errors},
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
    Parameter(ParamIdx),            // parameter index in function
    Effect(EffIdx),                 // effect index in ast
    EffectFunction(Val, EffFunIdx), // effect value, function index in effect
    Function(FunIdx),               // function index in ast

    Builtin, // builtin effects
}

pub struct Analysis {
    pub values: VecMap<Ident, Val>,
    pub defs: VecMap<Val, Definition>,
    pub main: Option<FunIdx>,
    pub closures: HashMap<ExprIdx, Vec<Val>>,
}

struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    values: HashMap<String, Val>,
    effects: &'a HashMap<String, (Val, HashMap<String, Val>)>,
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
    ctx: &ParseContext,
    expr: ExprIdx,
    errors: &mut Errors,
) {
    match ctx.exprs[expr].0 {
        // analyze
        Expression::Handler(ref handler) => {
            // put effect in scope
            let ident = handler.effect;
            let funcs = scope_effect(actx, ctx, ident, scope, errors);

            // match func names to effect
            if let Some(funs) = funcs {
                for fun in handler.functions.iter() {
                    let name = &ctx.idents[fun.decl.name].0;
                    match funs.get(name) {
                        Some(&val) => actx.values[fun.decl.name] = val,
                        None => errors.push(
                            ctx.idents[fun.decl.name]
                                .with(Error::UnknownEffectFun(ctx.idents[handler.effect].empty())),
                        ),
                    }
                }
            }

            // analyze functions
            for func in handler.functions.iter() {
                let mut scope = scope.child();
                scope_sign(actx, &mut scope, ctx, &func.decl.sign, errors);
                analyze_expr(actx, &mut scope, ctx, func.body, errors);
            }
        }
        Expression::Ident(ident) => {
            let name = &ctx.idents[ident].0;
            match scope.get(name) {
                Some(val) => actx.values[ident] = val,
                None => errors.push(ctx.idents[ident].with(Error::UnknownValue)),
            }
        }

        // traverse downwards
        Expression::Body(ref b) => {
            let mut child = scope.child();

            for &expr in b.main.iter() {
                analyze_expr(actx, &mut child, ctx, expr, errors);
            }
            if let Some(expr) = b.last {
                analyze_expr(actx, &mut child, ctx, expr, errors);
            }
        }
        Expression::Call(expr, ref exprs) => {
            analyze_expr(actx, scope, ctx, expr, errors);
            for &expr in exprs {
                analyze_expr(actx, scope, ctx, expr, errors);
            }
        }
        Expression::TryWith(expr, handler) => {
            let mut child = scope.child();
            analyze_expr(actx, &mut child, ctx, handler, errors);
            analyze_expr(actx, &mut child, ctx, expr, errors);
        }
        Expression::Member(expr, _) => {
            analyze_expr(actx, scope, ctx, expr, errors);
        }
        Expression::IfElse(cond, no, yes) => {
            analyze_expr(actx, scope, ctx, cond, errors);
            analyze_expr(actx, scope, ctx, no, errors);
            if let Some(expr) = yes {
                analyze_expr(actx, scope, ctx, expr, errors);
            }
        }
        Expression::Op(left, _, right) => {
            analyze_expr(actx, scope, ctx, left, errors);
            analyze_expr(actx, scope, ctx, right, errors);
        }
        Expression::Break(val) => {
            if let Some(expr) = val {
                analyze_expr(actx, scope, ctx, expr, errors);
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
) -> Option<&'a HashMap<String, Val>> {
    let name = &ctx.idents[ident].0;
    match scope.effects.get(name) {
        Some((val, vec)) => {
            actx.values[ident] = *val;
            scope
                .values
                .extend(vec.iter().map(|(s, &v)| (s.clone(), v)));
            Some(vec)
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
            actx.push_val(param, Definition::Parameter(ParamIdx(i))),
        );
    }
}

pub const STR: Val = Val(0);
pub const INT: Val = Val(1);

pub const DEBUG: Val = Val(2);
pub const PUTINT: Val = Val(3);

pub fn analyze(ast: &AST, ctx: &ParseContext, errors: &mut Errors) -> Analysis {
    let mut actx = Analysis {
        values: VecMap::filled(ctx.idents.len(), Val(usize::MAX)),
        defs: VecMap::new(),
        main: None,
        closures: HashMap::new(),
    };

    let mut effects = HashMap::new();
    let mut values = HashMap::new();

    // built-in values
    values.insert("str".to_owned(), STR);
    values.insert("int".to_owned(), INT);
    values.insert("debug".to_owned(), DEBUG);

    let mut debug = HashMap::new();
    debug.insert("putint".to_owned(), PUTINT);
    effects.insert("debug".to_owned(), (DEBUG, debug));

    actx.defs = VecMap::filled(4, Definition::Builtin);
    actx.defs[PUTINT] = Definition::EffectFunction(DEBUG, EffFunIdx(0));

    // put names in scope
    // TODO: error on conflict
    for (i, effect) in ast.effects.values().enumerate() {
        // add effect to scope
        let val = actx.push_val(effect.name, Definition::Effect(EffIdx(i)));
        values.insert(ctx.idents[effect.name].0.clone(), val);

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
    let scope = Scope {
        parent: None,
        values,
        effects: &effects,
    };

    for effect in ast.effects.values() {
        for func in effect.functions.values() {
            let mut scope = scope.child();
            scope_sign(&mut actx, &mut scope, ctx, &func.sign, errors);
        }
    }
    for func in ast.functions.values() {
        let mut scope = scope.child();
        scope_sign(&mut actx, &mut scope, ctx, &func.decl.sign, errors);
        analyze_expr(&mut actx, &mut scope, ctx, func.body, errors);
    }

    actx
}
