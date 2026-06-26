use do_notation::m;

use crate::ast::{self, LambdaParameter, Path, Token};
use crate::error::Result;
use crate::pass::parser::Parser;
use crate::pass::parser::err::Expected;
use crate::tokens::{Group, Keyword, Symbol, SymbolAssign, TokenEnum};

type Expr = Result<Box<ast::Expression>>;

impl<'a> Parser<'a> {
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
                        TokenEnum::Keyword(Keyword::Use) => m! {
                            let tk_use = self.skip();
                            fun <- self.path(false);
                            args <- self.when_next(
                                TokenEnum::Open(Group::Parenthesis),
                                |parser| parser.many_grouped(Group::Parenthesis, Symbol::Comma, |p| p.expression(true))
                            );
                            tk_newline <- self.consume(Symbol::Semicolon);
                            block <- self.many(Symbol::Semicolon, Self::statement);
                            return Box::new(ast::Expression::Use {
                                params: Some((tk_let, ast::Separated { elements: vec![(LambdaParameter { var, ty }, None)], end }, tk_equals)),
                                tk_use,
                                fun,
                                args,
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
                    fun <- self.path(false);
                    args <- self.when_next(
                        TokenEnum::Open(Group::Parenthesis),
                        |parser| parser.many_grouped(Group::Parenthesis, Symbol::Comma, |p| p.expression(true))
                    );
                    tk_newline <- self.consume(Symbol::Semicolon);
                    block <- self.many(Symbol::Semicolon, Self::statement);
                    return Box::new(ast::Expression::Use {
                        params: None,
                        tk_use,
                        fun,
                        args,
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
                TokenEnum::Symbol(Symbol::Equality(op)) => Some(ast::BinOp::Equality(op.into())),
                _ => None,
            },
            &ast::Expression::BinOp,
        )
    }

    fn expression_inequality(&mut self, allow_lambda: bool) -> Expr {
        self.expression_left_recurse(
            &|p| p.expression_addition(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Inequality(op)) => {
                    Some(ast::BinOp::Inequality(op.into()))
                }
                _ => None,
            },
            &ast::Expression::BinOp,
        )
    }

    fn expression_addition(&mut self, allow_lambda: bool) -> Expr {
        self.expression_left_recurse(
            &|p| p.expression_multiplication(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Plus) => Some(ast::BinOp::Math(ast::MathOp::Add)),
                TokenEnum::Symbol(Symbol::Dash) => Some(ast::BinOp::Math(ast::MathOp::Sub)),
                _ => None,
            },
            &ast::Expression::BinOp,
        )
    }

    fn expression_multiplication(&mut self, allow_lambda: bool) -> Expr {
        self.expression_left_recurse(
            &|p| p.expression_typed(allow_lambda),
            &|t| match t {
                TokenEnum::Symbol(Symbol::Star) => Some(ast::BinOp::Math(ast::MathOp::Mul)),
                TokenEnum::Symbol(Symbol::Slash) => Some(ast::BinOp::Math(ast::MathOp::Div)),
                TokenEnum::Symbol(Symbol::Percent) => Some(ast::BinOp::Math(ast::MathOp::Mod)),
                _ => None,
            },
            &ast::Expression::BinOp,
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
                let tk_ext = self.skip();
                self.expression_prefix(allow_lambda)
                    .map(|expr| Box::new(ast::Expression::Ext { tk_ext, expr }))
            }
            TokenEnum::Keyword(Keyword::Truncate) => {
                let tk_trunc = self.skip();
                self.expression_prefix(allow_lambda)
                    .map(|expr| Box::new(ast::Expression::Trunc { tk_trunc, expr }))
            }
            TokenEnum::Keyword(Keyword::Transmute) => {
                let tk_transmute = self.skip();
                self.expression_prefix(allow_lambda)
                    .map(|expr| Box::new(ast::Expression::Transmute { tk_transmute, expr }))
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
                    todo!("error"),
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
                    todo!()
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
            TokenEnum::Keyword(Keyword::Perform) => {
                m! {
                    let tk_perform = self.skip();
                    expr <- self.expression(allow_lambda);
                    return Box::new(ast::Expression::Perform { tk_perform, expr });
                }
            }
            TokenEnum::Keyword(Keyword::Return) => {
                m! {
                    let tk_return = self.skip();
                    expr <- self.unless_next(&[TokenEnum::Symbol(Symbol::Comma), TokenEnum::Symbol(Symbol::Semicolon)], |p| p.expression(allow_lambda));
                    return Box::new(ast::Expression::Return { tk_return, expr });
                }
            }
            TokenEnum::Symbol(Symbol::DashDashDash) => {
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
                        _ => todo!("error")
                    };
                    branch_false <- self.consume_next(Keyword::Else, |p| p.expression(true));
                    return Box::new(ast::Expression::If { tk_if, condition, branch_true, branch_false });
                }
            }
            // FIXME: allow for generic arguments
            TokenEnum::Identifier => {
                m! {
                    ident <- self.ident();
                    fundefault <- match self.next().token {
                        TokenEnum::Symbol(Symbol::Dot) => {
                            let tk_dot = self.skip();
                            self.ident().map(|member| (
                                ast::Path {
                                    origin: ast::PathOrigin::Package(ident.clone(), tk_dot, member.clone()),
                                    generics: None
                                },
                                ast::Expression::MemberOrItem {
                                    lhs: ident,
                                    tk_dot,
                                    rhs: member,
                                }
                            ))
                        }
                        _ => {
                            Result::new((
                                ast::Path {
                                    origin: ast::PathOrigin::Local(ident.clone()),
                                    generics: None
                                },
                                ast::Expression::Local(ident),
                            ))
                        }
                    };
                    let (fun, default) = fundefault;
                    args <- self.when_next(TokenEnum::Open(Group::Parenthesis), |p| p.many_grouped(Group::Parenthesis, Symbol::Comma, |p| p.expression(true)));
                    block <- if allow_lambda && (self.is_next(TokenEnum::Identifier) || self.is_next(TokenEnum::Open(Group::Brace))) {
                        // TODO: if it is an identifier, force it to have lambda args?
                        self.expression_top(true).map(Some)
                    } else {
                        Result::new(None)
                    };
                    with_effects <- self.when_next(Keyword::With, Parser::with_effects);
                    return Box::new(if args.is_none() && block.is_none() && with_effects.is_none() {
                        default
                    } else {
                        ast::Expression::Call {
                            fun,
                            args,
                            block,
                            with_effects,
                        }
                    });
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
