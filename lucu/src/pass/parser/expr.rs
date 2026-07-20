use do_notation::m;

use crate::ast::{self, LambdaParameter};
use crate::error::Result;
use crate::pass::parser::Parser;
use crate::pass::parser::err::Expected;
use crate::tokens::{Group, Keyword, Symbol, SymbolAssign, TokenEnum};

type Expr = Result<Box<ast::Expression>>;

#[derive(PartialEq, Eq)]
enum AllowLambda {
    No,
    Yes,
    Force,
}

impl From<bool> for AllowLambda {
    fn from(value: bool) -> Self {
        if value { Self::Yes } else { Self::No }
    }
}

impl<'a> Parser<'a> {
    pub fn call(&mut self, allow_lambda: bool) -> Result<ast::Call> {
        m! {
            fun <- self.path(false);
            call <- self.call_suffix(fun, AllowLambda::from(allow_lambda));
            return call.unwrap_or_else(Into::into);
        }
    }

    fn call_suffix(
        &mut self,
        fun: ast::Path,
        allow_lambda: AllowLambda,
    ) -> Result<std::result::Result<ast::Call, ast::Path>> {
        m! {
            args <- self.when_next(TokenEnum::Open(Group::Parenthesis), |p| p.many_grouped(Group::Parenthesis, Symbol::Comma, |p| p.expression(true)));
            block <- if allow_lambda != AllowLambda::No
                && (self.is_next(TokenEnum::Identifier) || self.is_next(TokenEnum::Open(Group::Brace))) {
                if self.is_next(TokenEnum::Identifier) {
                    // we allow identifiers here to make this possible:
                    // `unfounded loop { ... }`
                    let p = &mut *self;
                    m! {
                        fun <- p.path(false);
                        call <- p.call_suffix(fun, AllowLambda::Force);
                        let call = call.unwrap_or_else(Into::into);
                        return Some(Box::new(ast::Expression::Call(call)));
                    }
                } else {
                    self.expression_top(true).map(Some)
                }
            } else if allow_lambda != AllowLambda::Force {
                Result::new(None)
            } else {
                // NOTE: do we maybe want a more specific error here?
                self.error(Expected::Token(TokenEnum::Open(Group::Brace)))
            };
            with_effects <- self.when_next(Keyword::With, Parser::with_effects);
            return if args.is_some() || block.is_some() || with_effects.is_some() {
                Ok(ast::Call {
                    fun,
                    args,
                    block,
                    with_effects,
                })
            } else {
                Err(fun)
            };
        }
    }

    pub fn statement(&mut self) -> Expr {
        match self.next().token {
            TokenEnum::Keyword(Keyword::Discard) => {
                m! {
                    let tk_discard = self.skip();
                    expr <- self.expression(true);
                    return Box::new(ast::Expression::Discard { tk_discard, expr });
                }
            }
            TokenEnum::Keyword(Keyword::Let) => {
                m! {
                    let tk_let = self.skip();
                    var <- self.ident();
                    ty <- self.unless_next(&[TokenEnum::Symbol(Symbol::Assign(SymbolAssign::Equals))], Self::r#type);
                    let end = self.last_token_end;
                    tk_equals <- self.consume(Symbol::Assign(SymbolAssign::Equals));
                    match self.next().token {
                        // FIXME: allow multiple values
                        TokenEnum::Keyword(Keyword::Use) => m! {
                            let tk_use = self.skip();
                            call <- self.call(true);
                            tk_newline <- self.consume(Symbol::Semicolon);
                            block <- self.many(Symbol::Semicolon, Self::statement);
                            return Box::new(ast::Expression::Use {
                                params: Some((tk_let, ast::Separated { elements: vec![(LambdaParameter { var, ty }, None)], end }, tk_equals)),
                                tk_use,
                                call,
                                tk_newline,
                                block,
                            });
                        },
                        _ => self.expression(true).map(|value| {
                           Box::new(ast::Expression::Let { tk_let, var, ty, tk_equals, value })
                        })
                    }
                }
            }
            TokenEnum::Keyword(Keyword::Use) => {
                m! {
                    let tk_use = self.skip();
                    call <- self.call(true);
                    tk_newline <- self.consume(Symbol::Semicolon);
                    block <- self.many(Symbol::Semicolon, Self::statement);
                    return Box::new(ast::Expression::Use {
                        params: None,
                        tk_use,
                        call,
                        tk_newline,
                        block,
                    });
                }
            }
            _ => self.expression(true),
        }
    }

    pub fn expression(&mut self, allow_lambda: bool) -> Expr {
        self.expression_assign(allow_lambda)
    }

    fn expression_assign(&mut self, allow_lambda: bool) -> Expr {
        self.expression_right_recurse(
            &|p| p.expression_pipe(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Assign(op)) => Some(op.into()),
                _ => None,
            },
            &ast::Expression::AssignOp,
        )
    }

    fn expression_pipe(&mut self, allow_lambda: bool) -> Expr {
        // TODO: pipe operator
        self.expression_equality(allow_lambda)
    }

    fn expression_equality(&mut self, allow_lambda: bool) -> Expr {
        self.expression_left_recurse(
            &|p| p.expression_inequality(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Equality(op)) => {
                    Some(ast::PredicateOp::Equality(op.into()))
                }
                _ => None,
            },
            &ast::Expression::PredicateOp,
        )
    }

    fn expression_inequality(&mut self, allow_lambda: bool) -> Expr {
        self.expression_left_recurse(
            &|p| p.expression_addition(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Inequality(op)) => {
                    Some(ast::PredicateOp::Inequality(op.into()))
                }
                _ => None,
            },
            &ast::Expression::PredicateOp,
        )
    }

    fn expression_addition(&mut self, allow_lambda: bool) -> Expr {
        self.expression_left_recurse(
            &|p| p.expression_multiplication(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Plus) => Some(ast::MathOp::Add),
                TokenEnum::Symbol(Symbol::Dash) => Some(ast::MathOp::Sub),
                _ => None,
            },
            &ast::Expression::MathOp,
        )
    }

    fn expression_multiplication(&mut self, allow_lambda: bool) -> Expr {
        self.expression_left_recurse(
            &|p| p.expression_typed(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Star) => Some(ast::MathOp::Mul),
                TokenEnum::Symbol(Symbol::Slash) => Some(ast::MathOp::Div),
                TokenEnum::Symbol(Symbol::Percent) => Some(ast::MathOp::Mod),
                _ => None,
            },
            &ast::Expression::MathOp,
        )
    }

    fn expression_typed(&mut self, allow_lambda: bool) -> Expr {
        // TODO: 'expr as type'
        self.expression_prefix(allow_lambda)
    }

    fn expression_prefix(&mut self, allow_lambda: bool) -> Expr {
        match self.next().token {
            TokenEnum::Symbol(Symbol::Plus) => {
                let tk_op = self.skip();
                self.expression_prefix(allow_lambda).map(|expr| {
                    Box::new(ast::Expression::UnOp {
                        op: ast::UnOp::Plus,
                        tk_op,
                        expr,
                    })
                })
            }
            TokenEnum::Symbol(Symbol::Dash) => {
                let tk_op = self.skip();
                self.expression_prefix(allow_lambda).map(|expr| {
                    Box::new(ast::Expression::UnOp {
                        op: ast::UnOp::Negate,
                        tk_op,
                        expr,
                    })
                })
            }
            TokenEnum::Keyword(Keyword::Extend) => {
                let tk_cast = self.skip();
                self.expression_prefix(allow_lambda).map(|expr| {
                    Box::new(ast::Expression::Cast {
                        op: ast::Cast::Extend,
                        tk_cast,
                        expr,
                    })
                })
            }
            TokenEnum::Keyword(Keyword::Truncate) => {
                let tk_cast = self.skip();
                self.expression_prefix(allow_lambda).map(|expr| {
                    Box::new(ast::Expression::Cast {
                        op: ast::Cast::Truncate,
                        tk_cast,
                        expr,
                    })
                })
            }
            TokenEnum::Keyword(Keyword::Transmute) => {
                let tk_cast = self.skip();
                self.expression_prefix(allow_lambda).map(|expr| {
                    Box::new(ast::Expression::Cast {
                        op: ast::Cast::Transmute,
                        tk_cast,
                        expr,
                    })
                })
            }
            _ => self.expression_postfix(allow_lambda),
        }
    }

    pub fn index(&mut self) -> Result<ast::Index> {
        m! {
            from <- self.unless_next(&[TokenEnum::Symbol(Symbol::DotDot)], |p| p.expression(true));
            to <- self.consume_next(
                Symbol::DotDot,
                |parse| parse.unless_next(&[TokenEnum::Symbol(Symbol::Colon)], |p| p.expression(true))
            );
            match (from, to) {
                (None, None) =>
                    self.error(Expected::Index),
                (Some(single), None) =>
                    Result::new(ast::Index::Single(single)),
                (from, Some((range, to))) => self
                    .when_next(Symbol::Colon, Self::sentinel)
                    .map(|sentinel| ast::Index::Range { from, range, to, sentinel }),
            }
        }
    }

    fn expression_postfix(&mut self, allow_lambda: bool) -> Expr {
        let mut expr = self.expression_top(allow_lambda);
        while expr.value().is_some() {
            let s = &mut *self;
            match s.next().token {
                TokenEnum::Open(Group::Bracket) => {
                    expr = m! {
                        array <- expr;
                        index <- s.grouped(Group::Bracket, Self::index);
                        return Box::new(ast::Expression::Index {
                            array,
                            index
                        });
                    };
                }
                TokenEnum::Symbol(Symbol::Caret) => {
                    expr = m! {
                        expr <- expr;
                        let tk_caret = s.skip();
                        return Box::new(ast::Expression::Dereference {
                            expr,
                            tk_caret
                        });
                    };
                }
                TokenEnum::Symbol(Symbol::Dot) => {
                    expr = m! {
                        lhs <- expr;
                        let tk_dot = s.skip();
                        rhs <- s.ident();
                        return Box::new(ast::Expression::Member {
                            lhs,
                            tk_dot,
                            rhs
                        });
                    }
                }
                _ => return expr,
            }
        }
        expr
    }

    fn expression_top(&mut self, allow_lambda: bool) -> Expr {
        match self.next().token {
            TokenEnum::Open(Group::Parenthesis) => self
                .grouped(Group::Parenthesis, |p| p.expression(true))
                .map(|expr| Box::new(ast::Expression::Enclosed(expr))),
            TokenEnum::Open(Group::Brace) => self
                .grouped(Group::Brace, Self::block)
                .map(|block| Box::new(ast::Expression::Block(block))),
            TokenEnum::Open(Group::Bracket) => self
                .many_grouped(Group::Bracket, Symbol::Comma, |p| p.expression(true))
                .map(|exprs| Box::new(ast::Expression::Array(exprs))),
            TokenEnum::Keyword(Keyword::Handle) => {
                m! {
                    let tk_handle = self.skip();
                    expr <- self.expression(allow_lambda);
                    return Box::new(ast::Expression::Handle { tk_handle, expr });
                }
            }
            TokenEnum::Keyword(Keyword::Raise) => {
                m! {
                    let tk_raise = self.skip();
                    expr <- self.unless_next(&[TokenEnum::Symbol(Symbol::Comma), TokenEnum::Symbol(Symbol::Semicolon)], |p| p.expression(allow_lambda));
                    return Box::new(ast::Expression::Raise { tk_raise, expr });
                }
            }
            TokenEnum::Symbol(Symbol::TripleDash) => {
                Result::new(Box::new(ast::Expression::Uninit(self.skip())))
            }
            TokenEnum::Keyword(Keyword::If) => {
                m! {
                    let tk_if = self.skip();
                    condition <- self.expression(false);
                    branch_true <- match self.next().token {
                        TokenEnum::Keyword(Keyword::Then) => {
                            let tk_then = self.skip();
                            self.expression(true).map(|branch| (Some(tk_then), branch))
                        },
                        TokenEnum::Open(Group::Brace) => self
                            .grouped(Group::Brace, Self::block)
                            .map(|block| (None, Box::new(ast::Expression::Block(block)))),
                        _ => self.error(Expected::IfBlock),
                    };
                    branch_false <- self.consume_next(Keyword::Else, |p| p.expression(true));
                    return Box::new(ast::Expression::If { tk_if, condition, branch_true, branch_false });
                }
            }
            // TODO: better way of handling generics
            TokenEnum::Identifier => {
                m! {
                    ident <- self.ident();
                    fun <- match self.next().token {
                        TokenEnum::Symbol(Symbol::Dot) => {
                            let tk_dot = self.skip();
                            self.ident().and_then(|member| {
                                self.when(Parser::starts_multiple_generics, |parser|
                                    parser.many_grouped(Group::Bracket, Symbol::Comma, Parser::generic_argument)
                                ).map(|generics| ast::Path {
                                    origin: ast::PathOrigin::Package(ident, tk_dot, member),
                                    generics,
                                })
                            })
                        }
                        _ => {
                            self.when(Parser::starts_multiple_generics, |parser|
                                parser.many_grouped(Group::Bracket, Symbol::Comma, Parser::generic_argument)
                            ).map(|generics| ast::Path {
                                origin: ast::PathOrigin::Local(ident),
                                generics,
                            })
                        }
                    };
                    call <- self.call_suffix(fun, AllowLambda::from(allow_lambda));
                    return Box::new(call.map_or_else(ast::Expression::Path, ast::Expression::Call));
                }
            }
            _ if self.starts_constant() => self
                .constant(Expected::Expression)
                .map(|constant| Box::new(ast::Expression::Constant(constant))),
            _ => self.error(Expected::Expression),
        }
    }

    fn starts_lambda(&self) -> bool {
        matches!(self.tokens[0].token, TokenEnum::Identifier)
            && matches!(
                self.tokens[1].token,
                TokenEnum::Symbol(Symbol::Comma) | TokenEnum::Symbol(Symbol::Arrow)
            )
    }
    fn starts_multiple_generics(&self) -> bool {
        self.is_next(TokenEnum::Open(Group::Bracket)) && self.group_contains(Symbol::Comma)
    }

    pub fn lambda_parameter(&mut self) -> Result<ast::LambdaParameter> {
        m! {
            var <- self.ident_or_underscore();
            ty <- self.unless_next(&[TokenEnum::Symbol(Symbol::Comma), TokenEnum::Symbol(Symbol::Arrow)], Parser::r#type);
            return ast::LambdaParameter { var, ty };
        }
    }
    pub fn block(&mut self) -> Result<ast::Block> {
        m! {
            params <- if self.starts_lambda() {
                let s = &mut *self;
                m! {
                    names <- s.many_until_seperated(Symbol::Comma, &[TokenEnum::Symbol(Symbol::Arrow)], Self::lambda_parameter);
                    tk_arrow <- s.consume(TokenEnum::Symbol(Symbol::Arrow));
                    return Some((names, tk_arrow));
                }
            } else {
                Result::new(None)
            };
            stmts <- self.many(Symbol::Semicolon, Self::statement);
            return ast::Block { params, stmts };
        }
    }

    fn expression_right_recurse<T>(
        &mut self,
        inner: &impl Fn(&mut Self) -> Expr,
        op_ctor: &impl Fn(TokenEnum) -> Option<T>,
        expr_ctor: &impl Fn(
            T,
            Box<ast::Expression>,
            ast::Token,
            Box<ast::Expression>,
        ) -> ast::Expression,
    ) -> Expr {
        inner(self).and_then(|lhs| match op_ctor(self.next().token) {
            Some(op) => {
                m! {
                    let tk_op = self.skip();
                    rhs <- self.expression_right_recurse(inner, op_ctor, expr_ctor);
                    return Box::new(expr_ctor(op, lhs, tk_op, rhs));
                }
            }
            None => Result::new(lhs),
        })
    }

    fn expression_left_recurse<T>(
        &mut self,
        inner: &impl Fn(&mut Self) -> Expr,
        op_ctor: &impl Fn(TokenEnum) -> Option<T>,
        expr_ctor: &impl Fn(
            T,
            Box<ast::Expression>,
            ast::Token,
            Box<ast::Expression>,
        ) -> ast::Expression,
    ) -> Expr {
        let mut expr = inner(self);
        while expr.value().is_some()
            && let Some(op) = op_ctor(self.next().token)
        {
            let s = &mut *self;
            expr = m! {
                lhs <- expr;
                let tk_op = s.skip();
                rhs <- inner(s);
                return Box::new(expr_ctor(op, lhs, tk_op, rhs));
            };
        }
        expr
    }
}
