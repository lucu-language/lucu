#![feature(let_chains)]

use std::{collections::HashMap, fs::read_to_string, print, println, rc::Rc};

use lexer::Tokenizer;
use parser::{Expression, Function, ParseContext, AST};

mod analyzer;
mod lexer;
mod parser;

fn main() {
    let file = read_to_string("div.lucu").unwrap();
    let tokenizer = Tokenizer::new(file.as_str());
    let (ast, ctx) = parser::parse_ast(tokenizer);
    let actx = analyzer::analyze(&ast, &ctx);

    // print errors
    println!("\n--- ERRORS ---");
    println!("{:#?}", ctx.errors);

    // visualize idents
    println!("\n--- SCOPE ANALYSIS ---");

    let mut idents = actx
        .values
        .iter()
        .zip(ctx.idents.iter())
        .collect::<Vec<_>>();
    idents.sort_by_key(|(_, range)| range.1);

    let mut chars = file.chars().enumerate();
    let mut idents = idents.into_iter().peekable();

    while let Some((i, char)) = chars.next() {
        if let Some(id) = idents.peek() && id.1.1 == i {
            // background!
            let mut bg = 100;

            if *id.0 != usize::MAX {
                bg = 41 + (*id.0 % 14);

                if bg >= 48 {
                    bg = 101 + (bg - 48)
                }
            }

            print!("\x1b[{};30m{} {}", bg, id.0, char);

            if id.1.2 != i + 1 {
                while let Some((i, char)) = chars.next() {
                    print!("{}", char);
                    if id.1.2 == i + 1 {
                        break;
                    }
                }
            }

            print!("\x1b[0m");
            idents.next();
        } else {
            print!("{}", char);
        }
    }

    // execute
    println!("\n--- OUTPUT ---");
    eval_ast(ast, ctx);
}

#[derive(Clone)]
enum Value {
    String(String),
    Int(i64),
    Function(Rc<dyn Fn(Vec<Value>, &ParseContext) -> Result<Value, (usize, Value)>>),
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
            Ok(Value::None)
        })),
    );

    scope.insert(
        "putint".to_owned(),
        Value::Function(Rc::new(|vals, _| {
            match vals.get(0).unwrap() {
                Value::Int(i) => print!("{}", i),
                _ => panic!(),
            };
            Ok(Value::None)
        })),
    );

    let main = ast.functions.get("main").unwrap();
    let _ = eval_expr(main.body, &mut scope, &ctx, 0);
}

fn create_func(
    func: &Function,
    scope: &HashMap<String, Value>,
    ctx: &ParseContext,
    frame: usize,
) -> Value {
    // TODO: scope effects differently
    let expr = func.body;
    let scope = scope.clone();
    let names: Vec<String> = func
        .decl
        .sign
        .inputs
        .iter()
        .map(|r| ctx.idents[r.0].0.clone())
        .collect();

    Value::Function(Rc::new(move |vals, ctx| {
        let mut scope = scope.clone();
        for (name, value) in names.iter().zip(vals.into_iter()) {
            scope.insert(name.clone(), value);
        }
        eval_expr(expr, &mut scope, ctx, frame)
    }))
}

fn eval_expr(
    expr: usize,
    scope: &mut HashMap<String, Value>,
    ctx: &ParseContext,
    frame: usize,
) -> Result<Value, (usize, Value)> {
    match &ctx.exprs[expr].0 {
        Expression::Body(b) => {
            let mut inner_scope = scope.clone();
            for main in b.main.iter() {
                eval_expr(*main, &mut inner_scope, ctx, frame)?;
            }

            if let Some(last) = b.last {
                eval_expr(last, &mut inner_scope, ctx, frame)
            } else {
                Ok(Value::None)
            }
        }
        Expression::String(s) => Ok(Value::String(s.clone())),
        Expression::Ident(p) => Ok(scope.get(&ctx.idents[*p].0).unwrap().clone()),
        Expression::Call(expr, args) => {
            let f = match eval_expr(*expr, scope, ctx, frame)? {
                Value::Function(f) => f,
                _ => panic!(),
            };
            let args: Result<_, _> = args
                .iter()
                .map(|e| eval_expr(*e, scope, ctx, frame))
                .collect();
            f(args?, ctx)
        }
        Expression::TryWith(inner, handler) => {
            let mut inner_scope = scope.clone();
            eval_expr(*handler, &mut inner_scope, ctx, frame)?;
            match eval_expr(*inner, &mut inner_scope, ctx, frame + 1) {
                Err((f, val)) if f == frame => Ok(val),
                e => e,
            }
        }
        Expression::Member(_, _) => todo!(),
        Expression::Error => todo!(),
        Expression::Handler(handler) => {
            for func in handler.functions.iter() {
                scope.insert(func.0.clone(), create_func(func.1, scope, ctx, frame));
            }
            Ok(Value::None)
        }
        Expression::IfElse(cond, yes, no) => {
            if match eval_expr(*cond, scope, ctx, frame)? {
                Value::Int(i) => i != 0,
                _ => panic!(),
            } {
                eval_expr(*yes, scope, ctx, frame)
            } else if let Some(no) = no {
                eval_expr(*no, scope, ctx, frame)
            } else {
                Ok(Value::None)
            }
        }
        Expression::Op(left, op, right) => {
            let Value::Int(left) = eval_expr(*left, scope, ctx, frame)? else { panic!() };
            let Value::Int(right) = eval_expr(*right, scope, ctx, frame)? else { panic!() };

            Ok(Value::Int(match op {
                parser::Op::Equals => {
                    if left == right {
                        1
                    } else {
                        0
                    }
                }
                parser::Op::Divide => left / right,
            }))
        }
        Expression::Int(num) => Ok(Value::Int(*num as i64)),
        Expression::Break(val) => {
            let val = val
                .map(|v| eval_expr(v, scope, ctx, frame))
                .unwrap_or(Ok(Value::None))?;
            Err((frame, val))
        }
    }
}
