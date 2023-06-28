use std::{collections::HashMap, println};

use crate::parser::{Expr, Expression, FunSign, Ident, ParseContext, AST};

pub type Val = usize;

pub struct Analysis {
    // Scope Analysis: translation from Ident to Val
    pub values: Vec<Val>,
    types: usize,
}

// TODO: use parentage instead of cloning
#[derive(Clone, Default)]
struct Scope {
    values: HashMap<String, Val>,
    effects: HashMap<Val, HashMap<String, Val>>,
}

impl Analysis {
    fn traverse<T: Clone>(
        &mut self,
        ctx: &ParseContext,
        start: Expr,
        data: &mut T,
        f: &impl Fn(&mut Self, &ParseContext, Expr, &mut T),
    ) {
        match ctx.exprs[start].0 {
            Expression::Body(ref b) => {
                let mut child_data = data.clone();
                for &expr in b.main.iter() {
                    self.traverse(ctx, expr, &mut child_data, f);
                }
                if let Some(expr) = b.last {
                    self.traverse(ctx, expr, &mut child_data, f);
                }

                f(self, ctx, start, data);
            }

            Expression::Call(expr, ref exprs) => {
                self.traverse(ctx, expr, data, f);
                for &expr in exprs.iter() {
                    self.traverse(ctx, expr, data, f);
                }

                f(self, ctx, start, data);
            }
            Expression::TryWith(expr, handler) => {
                let mut child_data = data.clone();

                self.traverse(ctx, handler, &mut child_data, f);
                self.traverse(ctx, expr, &mut child_data, f);

                f(self, ctx, start, &mut child_data);
            }
            Expression::Member(expr, _) => {
                self.traverse(ctx, expr, data, f);
                f(self, ctx, start, data);
            }
            Expression::IfElse(cond, no, yes) => {
                self.traverse(ctx, cond, data, f);
                self.traverse(ctx, no, data, f);
                if let Some(yes) = yes {
                    self.traverse(ctx, yes, data, f);
                }
                f(self, ctx, start, data);
            }
            Expression::Op(left, _, right) => {
                self.traverse(ctx, left, data, f);
                self.traverse(ctx, right, data, f);
                f(self, ctx, start, data);
            }
            Expression::Break(val) => {
                if let Some(val) = val {
                    self.traverse(ctx, val, data, f);
                }
                f(self, ctx, start, data);
            }

            Expression::Error => f(self, ctx, start, data),
            Expression::String(_) => f(self, ctx, start, data),
            Expression::Ident(_) => f(self, ctx, start, data),
            Expression::Handler(_) => f(self, ctx, start, data),
            Expression::Int(_) => f(self, ctx, start, data),
        }
    }
    fn push_val(&mut self, id: Ident) -> Val {
        self.values[id] = self.types;
        self.types += 1;
        self.values[id]
    }
}

fn analyze_expr(actx: &mut Analysis, scope: &mut Scope, ctx: &ParseContext, expr: Expr) {
    actx.traverse(
        ctx,
        expr,
        scope,
        &|actx, ctx, expr, scope| match ctx.exprs[expr].0 {
            Expression::Handler(ref handler) => {
                // put effect in scope
                let ident = handler.effect;
                let funcs = scope_effect(actx, ctx, ident, scope);

                // match func names to effect
                if let Some(funcs) = funcs {
                    for (_, func) in handler.functions.iter() {
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
                for (_, func) in handler.functions.iter() {
                    let mut scope = scope.clone();
                    scope_sign(actx, &mut scope, ctx, &func.decl.sign);
                    analyze_expr(actx, &mut scope, ctx, func.body);
                }
            }
            Expression::Ident(ident) => {
                let name = &ctx.idents[ident].0;
                match scope.values.get(name) {
                    Some(&val) => actx.values[ident] = val,
                    None => println!("unknown value {}", name),
                }
            }
            Expression::Member(_, _) => todo!(),

            Expression::Body(_) => {}
            Expression::Call(_, _) => {}
            Expression::TryWith(_, _) => {}
            Expression::String(_) => {}
            Expression::Error => {}
            Expression::IfElse(_, _, _) => {}
            Expression::Op(_, _, _) => {}
            Expression::Break(_) => {}
            Expression::Int(_) => {}
        },
    );
}

fn scope_effect<'a>(
    actx: &mut Analysis,
    ctx: &ParseContext,
    ident: usize,
    scope: &'a mut Scope,
) -> Option<&'a HashMap<String, Val>> {
    let name = &ctx.idents[ident].0;
    match scope.values.get(name) {
        Some(&val) => {
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
            match scope.values.get(name) {
                Some(&val) => actx.values[typ.ident] = val,
                None => println!("unknown value {}", name),
            }
        }
        _ => {}
    }

    // put args in scope
    for &(param, ref typ) in func.inputs.iter() {
        // resolve type
        let name = &ctx.idents[typ.ident].0;
        match scope.values.get(name) {
            Some(&val) => actx.values[typ.ident] = val,
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

    let mut scope = Scope::default();

    // built-in values
    scope.values.insert("str".to_owned(), 0);
    scope.values.insert("int".to_owned(), 1);
    scope.values.insert("debug".to_owned(), 2);

    let mut debug = HashMap::new();
    debug.insert("putint".to_owned(), 3);
    scope.effects.insert(2, debug);

    actx.types = 4;

    // put names in scope
    // TODO: error on conflict
    for effect in ast.effects.values() {
        // add effect to scope
        let val = actx.push_val(effect.name);
        scope.values.insert(ctx.idents[effect.name].0.clone(), val);

        // remember effect functions
        let mut funcs = HashMap::new();
        for (_, func) in effect.functions.iter() {
            funcs.insert(ctx.idents[func.name].0.clone(), actx.push_val(func.name));
        }

        scope.effects.insert(val, funcs);
    }
    for func in ast.functions.values() {
        // add function to scope
        scope.values.insert(
            ctx.idents[func.decl.name].0.clone(),
            actx.push_val(func.decl.name),
        );
    }

    // analyze effects and functions
    for effect in ast.effects.values() {
        for (_, func) in effect.functions.iter() {
            let mut scope = scope.clone();
            scope_sign(&mut actx, &mut scope, ctx, &func.sign);
        }
    }
    for func in ast.functions.values() {
        let mut scope = scope.clone();
        scope_sign(&mut actx, &mut scope, ctx, &func.decl.sign);
        analyze_expr(&mut actx, &mut scope, ctx, func.body);
    }

    actx
}
