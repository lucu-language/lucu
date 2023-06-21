use std::{collections::HashMap, fs::read_to_string, rc::Rc};

use lexer::Tokenizer;
use parser::{Expression, Function, AST};

// mod analyzer;
mod lexer;
mod parser;

fn main() {
    let file = read_to_string("example.lucu").unwrap();
    let tokenizer = Tokenizer::new(file.as_str());
    let mut errors = Vec::new();
    let ast = parser::parse_ast(tokenizer, &mut errors);
    println!("{:#?}\n", errors);

    eval_ast(ast.unwrap())
}

#[derive(Clone)]
enum Value {
    String(String),
    Function(Rc<dyn Fn(Vec<Value>, &Vec<Expression>) -> Value>),
    None,
}

fn eval_ast(ast: AST) {
    let exprs = ast.exprs.into_iter().map(|r| r.0).collect();

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
    eval_expr(main.body, &exprs, &mut scope);
}

fn create_func(func: &Function, scope: &HashMap<String, Value>) -> Value {
    // TODO: scope effects differently
    let expr = func.body;
    let scope = scope.clone();
    let names: Vec<String> = func
        .decl
        .sign
        .inputs
        .iter()
        .map(|r| r.0 .0.clone())
        .collect();

    Value::Function(Rc::new(move |vals, exprs| {
        let mut scope = scope.clone();
        for (name, value) in names.iter().zip(vals.into_iter()) {
            scope.insert(name.clone(), value);
        }
        eval_expr(expr, exprs, &mut scope)
    }))
}

fn eval_expr(expr: usize, exprs: &Vec<Expression>, scope: &mut HashMap<String, Value>) -> Value {
    match &exprs[expr] {
        Expression::Body(b) => {
            let mut inner_scope = scope.clone();
            for main in b.main.iter() {
                eval_expr(*main, exprs, &mut inner_scope);
            }

            if let Some(last) = b.last {
                eval_expr(last, exprs, &mut inner_scope)
            } else {
                Value::None
            }
        }
        Expression::String(s) => Value::String(s.clone()),
        Expression::Ident(p) => scope.get(&p.ident.0).unwrap().clone(),
        Expression::Call(expr, args) => {
            let f = match eval_expr(*expr, exprs, scope) {
                Value::Function(f) => f,
                _ => panic!(),
            };
            let args = args.iter().map(|e| eval_expr(*e, exprs, scope)).collect();
            f(args, exprs)
        }
        Expression::TryWith(inner, handlers) => {
            let mut inner_scope = scope.clone();
            for handler in handlers.iter() {
                for func in handler.functions.iter() {
                    inner_scope.insert(func.0.clone(), create_func(func.1, scope));
                }
            }
            eval_expr(*inner, exprs, &mut inner_scope)
        }
        Expression::Member(_, _) => todo!(),
        Expression::Error => todo!(),
    }
}
