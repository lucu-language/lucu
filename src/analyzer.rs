use std::{collections::HashMap, println};

use crate::parser::{Expr, Expression, FunSign, Ident, ParseContext, AST};

pub type Val = usize;

pub struct Analysis {
    // Scope Analysis: translation from Ident to Val
    pub values: Vec<Val>,
    types: usize,
}

struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    values: HashMap<String, Val>,
    effects: &'a HashMap<Val, HashMap<String, Val>>,
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
    fn push_val(&mut self, id: Ident) -> Val {
        self.values[id] = self.types;
        self.types += 1;
        self.values[id]
    }
}

fn analyze_expr(actx: &mut Analysis, scope: &mut Scope, ctx: &ParseContext, expr: Expr) {
    match ctx.exprs[expr].0 {
        // analyze
        Expression::Handler(ref handler) => {
            // put effect in scope
            let ident = handler.effect;
            let funcs = scope_effect(actx, ctx, ident, scope);

            // match func names to effect
            if let Some(funcs) = funcs {
                for func in handler.functions.iter() {
                    let name = &ctx.idents[func.decl.name].0;
                    match funcs.get(name) {
                        Some(&val) => actx.values[func.decl.name] = val,
                        None => println!(
                            "unknown func {} of effect {}",
                            name, ctx.idents[handler.effect].0
                        ),
                    }
                }
            }

            // analyze functions
            for func in handler.functions.iter() {
                let mut scope = scope.child();
                scope_sign(actx, &mut scope, ctx, &func.decl.sign);
                analyze_expr(actx, &mut scope, ctx, func.body);
            }
        }
        Expression::Ident(ident) => {
            let name = &ctx.idents[ident].0;
            match scope.get(name) {
                Some(val) => actx.values[ident] = val,
                None => println!("unknown value {}", name),
            }
        }

        // traverse downwards
        Expression::Body(ref b) => {
            let mut child = scope.child();

            for &expr in b.main.iter() {
                analyze_expr(actx, &mut child, ctx, expr);
            }
            if let Some(expr) = b.last {
                analyze_expr(actx, &mut child, ctx, expr);
            }
        }
        Expression::Call(expr, ref exprs) => {
            analyze_expr(actx, scope, ctx, expr);
            for &expr in exprs {
                analyze_expr(actx, scope, ctx, expr);
            }
        }
        Expression::TryWith(expr, handler) => {
            let mut child = scope.child();
            analyze_expr(actx, &mut child, ctx, handler);
            analyze_expr(actx, &mut child, ctx, expr);
        }
        Expression::Member(expr, _) => {
            analyze_expr(actx, scope, ctx, expr);
        }
        Expression::IfElse(cond, no, yes) => {
            analyze_expr(actx, scope, ctx, cond);
            analyze_expr(actx, scope, ctx, no);
            if let Some(expr) = yes {
                analyze_expr(actx, scope, ctx, expr);
            }
        }
        Expression::Op(left, _, right) => {
            analyze_expr(actx, scope, ctx, left);
            analyze_expr(actx, scope, ctx, right);
        }
        Expression::Break(val) => {
            if let Some(expr) = val {
                analyze_expr(actx, scope, ctx, expr);
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
    ident: usize,
    scope: &'a mut Scope,
) -> Option<&'a HashMap<String, Val>> {
    let name = &ctx.idents[ident].0;
    match scope.get(name) {
        Some(val) => {
            actx.values[ident] = val;
            match scope.effects.get(&val) {
                Some(vec) => {
                    scope
                        .values
                        .extend(vec.iter().map(|(s, &v)| (s.clone(), v)));
                    Some(vec)
                }
                None => {
                    println!("{} is not an effect", name);
                    None
                }
            }
        }
        None => {
            println!("unknown value {}", name);
            None
        }
    }
}

fn scope_sign(actx: &mut Analysis, scope: &mut Scope, ctx: &ParseContext, func: &FunSign) {
    // put effects in scope
    for &effect in func.effects.iter() {
        scope_effect(actx, ctx, effect, scope);
    }

    // resolve return
    match func.output {
        Some(Some(ref typ)) => {
            let name = &ctx.idents[typ.ident].0;
            match scope.get(name) {
                Some(val) => actx.values[typ.ident] = val,
                None => println!("unknown value {}", name),
            }
        }
        _ => {}
    }

    // put args in scope
    for &(param, ref typ) in func.inputs.iter() {
        // resolve type
        let name = &ctx.idents[typ.ident].0;
        match scope.get(name) {
            Some(val) => actx.values[typ.ident] = val,
            None => println!("unknown value {}", name),
        }

        // add parameter to scope
        scope
            .values
            .insert(ctx.idents[param].0.clone(), actx.push_val(param));
    }
}

pub fn analyze(ast: &AST, ctx: &ParseContext) -> Analysis {
    let mut actx = Analysis {
        values: vec![usize::MAX; ctx.idents.len()],
        types: 0,
    };

    let mut effects = HashMap::new();
    let mut values = HashMap::new();

    // built-in values
    values.insert("str".to_owned(), 0);
    values.insert("int".to_owned(), 1);
    values.insert("debug".to_owned(), 2);

    let mut debug = HashMap::new();
    debug.insert("putint".to_owned(), 3);
    effects.insert(2, debug);

    actx.types = 4;

    // put names in scope
    // TODO: error on conflict
    for effect in ast.effects.iter() {
        // add effect to scope
        let val = actx.push_val(effect.name);
        values.insert(ctx.idents[effect.name].0.clone(), val);

        // remember effect functions
        let mut funcs = HashMap::new();
        for func in effect.functions.iter() {
            funcs.insert(ctx.idents[func.name].0.clone(), actx.push_val(func.name));
        }

        effects.insert(val, funcs);
    }
    for func in ast.functions.iter() {
        // add function to scope
        values.insert(
            ctx.idents[func.decl.name].0.clone(),
            actx.push_val(func.decl.name),
        );
    }

    // analyze effects and functions
    let scope = Scope {
        parent: None,
        values,
        effects: &effects,
    };

    for effect in ast.effects.iter() {
        for func in effect.functions.iter() {
            let mut scope = scope.child();
            scope_sign(&mut actx, &mut scope, ctx, &func.sign);
        }
    }
    for func in ast.functions.iter() {
        let mut scope = scope.child();
        scope_sign(&mut actx, &mut scope, ctx, &func.decl.sign);
        analyze_expr(&mut actx, &mut scope, ctx, func.body);
    }

    actx
}
