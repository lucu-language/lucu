use std::{collections::HashMap, fs::read_to_string, rc::Rc};

use lexer::Tokenizer;
use parser::{Expression, Function, ParseContext, AST};

// mod analyzer;
mod lexer;
mod parser;

fn main() {
    let file = read_to_string("example.lucu").unwrap();
    let tokenizer = Tokenizer::new(file.as_str());
    let (ast, ctx) = parser::parse_ast(tokenizer);
    println!("{:#?}\n", &ctx.errors);

    eval_ast(ast, ctx);
}

#[derive(Clone)]
enum Value {
    String(String),
    Function(Rc<dyn Fn(Vec<Value>, &ParseContext) -> Value>),
    None,
}

fn eval_ast(ast: AST, ctx: ParseContext) {
    let mut scope = HashMap::new();
    scope.insert(
        "write".to_owned(),
        Value::Function(Rc::new(|vals, _| {
            match vals.get(0).unwrap() {
                Value::String(s) => print!("{}", s),
                _ => panic!(),
            };
            Value::None
        })),
    );

    let main = ast.functions.get("main").unwrap();
    eval_expr(main.body, &mut scope, &ctx);
}

fn create_func(func: &Function, scope: &HashMap<String, Value>, ctx: &ParseContext) -> Value {
    // TODO: scope effects differently
    let expr = func.body;
    let scope = scope.clone();
    let names: Vec<String> = func
        .decl
        .sign
        .inputs
        .iter()
        .map(|r| ctx.idents[r.0 .0 .0].clone())
        .collect();

    Value::Function(Rc::new(move |vals, ctx| {
        let mut scope = scope.clone();
        for (name, value) in names.iter().zip(vals.into_iter()) {
            scope.insert(name.clone(), value);
        }
        eval_expr(expr, &mut scope, ctx)
    }))
}

fn eval_expr(expr: usize, scope: &mut HashMap<String, Value>, ctx: &ParseContext) -> Value {
    match &ctx.exprs[expr].0 {
        Expression::Body(b) => {
            let mut inner_scope = scope.clone();
            for main in b.main.iter() {
                eval_expr(*main, &mut inner_scope, ctx);
            }

            if let Some(last) = b.last {
                eval_expr(last, &mut inner_scope, ctx)
            } else {
                Value::None
            }
        }
        Expression::String(s) => Value::String(s.clone()),
        Expression::Ident(p) => scope.get(&ctx.idents[p.0 .0]).unwrap().clone(),
        Expression::Call(expr, args) => {
            let f = match eval_expr(*expr, scope, ctx) {
                Value::Function(f) => f,
                _ => panic!(),
            };
            let args = args.iter().map(|e| eval_expr(*e, scope, ctx)).collect();
            f(args, ctx)
        }
        Expression::TryWith(inner, handlers) => {
            let mut inner_scope = scope.clone();
            for handler in handlers.iter() {
                for func in handler.functions.iter() {
                    inner_scope.insert(func.0.clone(), create_func(func.1, scope, ctx));
                }
            }
            eval_expr(*inner, &mut inner_scope, ctx)
        }
        Expression::Member(_, _) => todo!(),
        Expression::Error => todo!(),
    }
}
