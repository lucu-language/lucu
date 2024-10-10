use std::num::NonZeroU32;

use crate::{
    lexer::{FullToken, Group, Keyword, Literal, Symbol, Token},
    tree::{Location, NodeData},
};

use super::{
    Constant, Constraint, Definition, Error, Expression, Identifier, List, NodeVariant, ParseTree,
    Parser, Result, Type,
};

pub fn parse(tokens: &[FullToken]) -> (ParseTree, Vec<Error>) {
    let mut parser = Parser::new(tokens);
    parser.lucu();
    (parser.nodes, parser.errors)
}

fn skip_group<'a>(group: Group, tokens: &mut impl Iterator<Item = &'a FullToken>) {
    while let Some(token) = tokens.next().filter(|t| t.token != Token::Close(group)) {
        if let Token::Open(inner) = token.token {
            skip_group(inner, tokens);
        }
    }
}
fn starts_type<'a>(tokens: &mut impl Iterator<Item = &'a FullToken>) -> bool {
    match tokens.next().map(|t| t.token) {
        Some(Token::Open(Group::Bracket)) => {
            skip_group(Group::Bracket, tokens);
            starts_type(tokens)
        }
        Some(t) if t.starts_type() => true,
        _ => false,
    }
}

impl Parser<'_> {
    fn in_lambda_params(&self) -> bool {
        // matches: { -> OR { id -> OR { id ,
        let mut tokens = self.next_tokens();
        tokens.next();

        let Some(first) = tokens.next() else {
            return false;
        };
        if first.token == Token::Symbol(Symbol::Arrow) {
            return true;
        };

        tokens.next().is_some_and(|t| {
            matches!(
                t.token,
                Token::Symbol(Symbol::Comma) | Token::Symbol(Symbol::Arrow)
            )
        })
    }
    fn in_array_type(&self) -> bool {
        let mut tokens = self.next_tokens();
        tokens.next();

        skip_group(Group::Bracket, &mut tokens);
        starts_type(&mut tokens)
    }

    fn import(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::Import, |parser| {
            parser.token_expect(Token::Keyword(Keyword::Import))?;
            let path = parser.leaf(
                NodeVariant::Constant(Constant::String),
                Token::Literal(Literal::String),
            )?;
            let name = parser.leaf_option(
                NodeVariant::Identifier(Identifier::Identifier),
                Token::Literal(Literal::Identifier),
            );
            Ok((Some(path), name))
        })
    }
    fn definition(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::ConstrainedDefinition, |parser| {
            let constraints = parser.constraints();
            if parser.token_check(Token::Open(Group::Brace)) {
                let definitions = parser.grouped_delimited(
                    List::ConstrainedDefinitions,
                    Group::Brace,
                    Symbol::Semicolon,
                    Parser::definition,
                )?;
                Ok((constraints, Some(definitions)))
            } else {
                const EQUALS: Token = Token::Symbol(Symbol::Equals);
                let definition = parser.choice(NodeVariant::Definition, |parser, token| {
                    Ok(Some(match token {
                        Token::Keyword(Keyword::Const) => {
                            let name = parser.typed_name()?;
                            let constant = parser.consume_then(EQUALS, Parser::constant)?;
                            (Definition::Constant, name, constant)
                        }
                        Token::Keyword(Keyword::Default) => {
                            let id = parser.generic_identifier()?;
                            let definitions = parser.handler_impl()?;
                            (Definition::Default, id, definitions)
                        }
                        Token::Keyword(Keyword::Fun) => {
                            let name = parser.named_signature()?;
                            let body = parser.consume_then(EQUALS, Parser::expression)?;
                            (Definition::Function, name, body)
                        }
                        Token::Keyword(Keyword::Effect) => {
                            let name = parser.name()?;
                            let definitions = parser.consume_then(EQUALS, |parser| {
                                if parser.token_check(Token::Open(Group::Brace)) {
                                    // effect definition
                                    parser.grouped_delimited(
                                        List::ConstrainedDefinitions,
                                        Group::Brace,
                                        Symbol::Semicolon,
                                        Parser::definition,
                                    )
                                } else {
                                    // effect alias
                                    Ok(parser.delimited(
                                        List::Constraints,
                                        Symbol::Comma,
                                        Token::is_semicolon,
                                        Parser::constraint,
                                    ))
                                }
                            })?;
                            (Definition::Effect, name, definitions)
                        }
                        Token::Keyword(Keyword::Type) => {
                            let name = parser.name()?;
                            let typ = parser.consume_then(EQUALS, Parser::type_)?;
                            (Definition::Type, name, typ)
                        }
                        _ => return Ok(None),
                    }))
                })?;
                Ok((constraints, Some(definition)))
            }
        })
    }
    fn named_signature(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::NamedSignature, |parser| {
            let name = parser.name()?;
            let sig = parser.function_signature()?;
            Ok((Some(name), Some(sig)))
        })
    }
    fn function_signature(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::FunctionSignature, |parser| {
            let params = parser.function_parameters()?;
            let output = parser.consume_then(Token::Symbol(Symbol::Colon), Self::type_)?;
            Ok((Some(params), output))
        })
    }
    fn function_parameters(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::FunctionParameters, |parser| {
            let params = parser.check_then(Token::Open(Group::Parenthesis), |parser| {
                parser.grouped_delimited(
                    List::Parameters,
                    Group::Parenthesis,
                    Symbol::Comma,
                    Self::parameter,
                )
            })?;
            let blocks = parser.check_then(Token::Open(Group::Brace), |parser| {
                parser.many(List::BlockParameters, |parser| {
                    loop {
                        if parser.token_check(Token::Open(Group::Brace)) {
                            match parser.grouped(Group::Brace, Self::block_parameter) {
                                Ok(Some(v)) => return Ok(Some(v)),
                                Ok(None) => {}
                                Err(_) => unreachable!(), // we just did a check
                            }
                        } else {
                            return Ok(None);
                        }
                    }
                })
            })?;
            Ok((params, blocks))
        })
    }
    fn parameter(&mut self) -> Result<NonZeroU32> {
        let mutable = self.token_consume(Token::Keyword(Keyword::Mut));
        self.node(NodeVariant::Parameter { mutable }, |parser| {
            let ident = parser.identifier()?;
            parser.token_expect(Token::Symbol(Symbol::Colon))?;
            let typ = parser.type_()?;
            Ok((Some(ident), Some(typ)))
        })
    }
    fn block_parameter(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::BlockParameter, |parser| {
            let sig = parser.named_signature()?;
            let constraints = parser.constraints();
            Ok((Some(sig), constraints))
        })
    }
    fn expression(&mut self) -> Result<NonZeroU32> {
        self.expression_assign::<true>()
    }
    fn expression_assign<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        let lhs = self.expression_range::<LAMBDA>()?;
        self.peeked(
            NodeVariant::Expression,
            |_| Ok(lhs),
            |parser, peek| {
                Ok(match peek {
                    Token::Symbol(Symbol::Equals) => {
                        parser.skip();
                        let expr = parser.expression_assign::<LAMBDA>()?;
                        Some((Expression::Assign, Some(lhs), Some(expr)))
                    }
                    Token::Symbol(Symbol::PlusEquals) => {
                        parser.skip();
                        let expr = parser.expression_assign::<LAMBDA>()?;
                        Some((Expression::AssignAdd, Some(lhs), Some(expr)))
                    }
                    Token::Symbol(Symbol::DashEquals) => {
                        parser.skip();
                        let expr = parser.expression_assign::<LAMBDA>()?;
                        Some((Expression::AssignSub, Some(lhs), Some(expr)))
                    }
                    Token::Symbol(Symbol::StarEquals) => {
                        parser.skip();
                        let expr = parser.expression_assign::<LAMBDA>()?;
                        Some((Expression::AssignMul, Some(lhs), Some(expr)))
                    }
                    Token::Symbol(Symbol::SlashEquals) => {
                        parser.skip();
                        let expr = parser.expression_assign::<LAMBDA>()?;
                        Some((Expression::AssignDiv, Some(lhs), Some(expr)))
                    }
                    Token::Symbol(Symbol::PercentEquals) => {
                        parser.skip();
                        let expr = parser.expression_assign::<LAMBDA>()?;
                        Some((Expression::AssignMod, Some(lhs), Some(expr)))
                    }
                    _ => None,
                })
            },
        )
    }
    fn expression_range<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.left_rec(Self::expression_equality::<LAMBDA>, |parser, peek| {
            Ok(match peek {
                Token::Symbol(Symbol::DotDot) => {
                    parser.skip();
                    let expr = parser.expression_equality::<LAMBDA>()?;
                    Some((Expression::Range, Some(expr)))
                }
                _ => None,
            })
        })
    }
    fn expression_equality<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.left_rec(Self::expression_compare::<LAMBDA>, |parser, peek| {
            Ok(match peek {
                Token::Symbol(Symbol::EqualsEquals) => {
                    parser.skip();
                    let expr = parser.expression_compare::<LAMBDA>()?;
                    Some((Expression::Equals, Some(expr)))
                }
                Token::Symbol(Symbol::BangEquals) => {
                    parser.skip();
                    let expr = parser.expression_compare::<LAMBDA>()?;
                    Some((Expression::NotEquals, Some(expr)))
                }
                _ => None,
            })
        })
    }
    fn expression_compare<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.left_rec(Self::expression_addition::<LAMBDA>, |parser, peek| {
            Ok(match peek {
                Token::Symbol(Symbol::Less) => {
                    parser.skip();
                    let expr = parser.expression_addition::<LAMBDA>()?;
                    Some((Expression::Less, Some(expr)))
                }
                Token::Symbol(Symbol::Greater) => {
                    parser.skip();
                    let expr = parser.expression_addition::<LAMBDA>()?;
                    Some((Expression::Greater, Some(expr)))
                }
                Token::Symbol(Symbol::LessEquals) => {
                    parser.skip();
                    let expr = parser.expression_addition::<LAMBDA>()?;
                    Some((Expression::LessEquals, Some(expr)))
                }
                Token::Symbol(Symbol::GreaterEquals) => {
                    parser.skip();
                    let expr = parser.expression_addition::<LAMBDA>()?;
                    Some((Expression::GreaterEquals, Some(expr)))
                }
                _ => None,
            })
        })
    }
    fn expression_addition<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.left_rec(Self::expression_multiplication::<LAMBDA>, |parser, peek| {
            Ok(match peek {
                Token::Symbol(Symbol::Plus) => {
                    parser.skip();
                    let expr = parser.expression_multiplication::<LAMBDA>()?;
                    Some((Expression::Add, Some(expr)))
                }
                Token::Symbol(Symbol::Dash) => {
                    parser.skip();
                    let expr = parser.expression_multiplication::<LAMBDA>()?;
                    Some((Expression::Sub, Some(expr)))
                }
                _ => None,
            })
        })
    }
    fn expression_multiplication<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.left_rec(Self::expression_typed::<LAMBDA>, |parser, peek| {
            Ok(match peek {
                Token::Symbol(Symbol::Star) => {
                    parser.skip();
                    let expr = parser.expression_typed::<LAMBDA>()?;
                    Some((Expression::Mul, Some(expr)))
                }
                Token::Symbol(Symbol::Slash) => {
                    parser.skip();
                    let expr = parser.expression_typed::<LAMBDA>()?;
                    Some((Expression::Div, Some(expr)))
                }
                Token::Symbol(Symbol::Percent) => {
                    parser.skip();
                    let expr = parser.expression_typed::<LAMBDA>()?;
                    Some((Expression::Mod, Some(expr)))
                }
                _ => None,
            })
        })
    }
    fn expression_typed<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.left_rec(Self::expression_pre::<LAMBDA>, |parser, peek| match peek {
            Token::Symbol(Symbol::Colon) => {
                parser.skip();
                let typ = parser.type_()?;
                Ok(Some((Expression::Typed, Some(typ))))
            }
            _ => Ok(None),
        })
    }
    fn expression_pre<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.peeked(
            NodeVariant::Expression,
            Self::expression_post::<LAMBDA>,
            |parser, peek| {
                Ok(match peek {
                    Token::Symbol(Symbol::Ampersand) => {
                        parser.skip();
                        let lhs = parser.expression_pre::<LAMBDA>()?;
                        Some((Expression::Reference, Some(lhs), None))
                    }
                    Token::Symbol(Symbol::PlusPlus) => {
                        parser.skip();
                        let lhs = parser.expression_pre::<LAMBDA>()?;
                        Some((Expression::PreIncrement, Some(lhs), None))
                    }
                    Token::Symbol(Symbol::DashDash) => {
                        parser.skip();
                        let lhs = parser.expression_pre::<LAMBDA>()?;
                        Some((Expression::PreDecrement, Some(lhs), None))
                    }
                    Token::Symbol(Symbol::Plus) => {
                        parser.skip();
                        let lhs = parser.expression_pre::<LAMBDA>()?;
                        Some((Expression::Plus, Some(lhs), None))
                    }
                    Token::Symbol(Symbol::Dash) => {
                        parser.skip();
                        let lhs = parser.expression_pre::<LAMBDA>()?;
                        Some((Expression::Negate, Some(lhs), None))
                    }
                    _ => None,
                })
            },
        )
    }
    fn expression_post<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.left_rec(Self::expression_top::<LAMBDA>, |parser, peek| {
            Ok(match peek {
                Token::Symbol(Symbol::Dot) => {
                    parser.skip();
                    let id = parser.identifier()?;
                    Some((Expression::Member, Some(id)))
                }
                Token::Open(Group::Bracket) => {
                    let exprs = parser.grouped_delimited(
                        List::Expressions,
                        Group::Bracket,
                        Symbol::Comma,
                        Self::expression,
                    )?;
                    Some((Expression::Index, Some(exprs)))
                }
                Token::Symbol(Symbol::Caret) => {
                    parser.skip();
                    Some((Expression::Dereference, None))
                }
                Token::Symbol(Symbol::PlusPlus) => {
                    parser.skip();
                    Some((Expression::PostIncrement, None))
                }
                Token::Symbol(Symbol::DashDash) => {
                    parser.skip();
                    Some((Expression::PostDecrement, None))
                }
                Token::Open(Group::Parenthesis) | Token::Open(Group::Brace)
                    if LAMBDA || !parser.token_check(Token::Open(Group::Brace)) =>
                {
                    let arguments = parser.node(NodeVariant::Arguments, |parser| {
                        let exprs =
                            parser.check_then(Token::Open(Group::Parenthesis), |parser| {
                                parser.grouped_delimited(
                                    List::Expressions,
                                    Group::Parenthesis,
                                    Symbol::Comma,
                                    Parser::expression,
                                )
                            })?;
                        let lambdas = (LAMBDA && parser.token_check(Token::Open(Group::Brace)))
                            .then(|| {
                                parser.many(List::Lambdas, |parser| {
                                    parser.check_then(Token::Open(Group::Brace), |parser| {
                                        parser.lambda()
                                    })
                                })
                            })
                            .transpose()?;
                        Ok((exprs, lambdas))
                    })?;
                    Some((Expression::Call, Some(arguments)))
                }
                _ => None,
            })
        })
    }
    fn expression_top<const LAMBDA: bool>(&mut self) -> Result<NonZeroU32> {
        self.peeked(
            NodeVariant::Expression,
            |parser| {
                parser.wrap(
                    NodeVariant::Expression(Expression::Constant),
                    Self::constant,
                )
            },
            |parser, peek| {
                Ok(match peek {
                    Token::Open(Group::Brace) => {
                        let expr = parser.grouped_delimited(
                            List::Expressions,
                            Group::Brace,
                            Symbol::Semicolon,
                            Parser::expression,
                        )?;
                        Some((Expression::Block, Some(expr), None))
                    }
                    Token::Open(Group::Parenthesis) => {
                        let expr = parser.grouped_delimited(
                            List::Expressions,
                            Group::Parenthesis,
                            Symbol::Comma,
                            Parser::expression,
                        )?;
                        Some((Expression::Struct, Some(expr), None))
                    }
                    Token::Open(Group::Bracket) if !parser.in_array_type() => {
                        let expr = parser.grouped_delimited(
                            List::Expressions,
                            Group::Bracket,
                            Symbol::Comma,
                            Parser::expression,
                        )?;
                        Some((Expression::Array, Some(expr), None))
                    }
                    Token::Literal(Literal::Identifier) => {
                        let id = parser.identifier()?;
                        Some((Expression::Path, Some(id), None))
                    }
                    Token::Keyword(Keyword::Cast) => {
                        parser.skip();
                        let lhs = parser.expression_pre::<LAMBDA>()?;
                        Some((Expression::Cast, Some(lhs), None))
                    }
                    Token::Keyword(Keyword::Case) => {
                        parser.skip();
                        let expr = parser.expression_assign::<false>()?;
                        let cases = parser.grouped_delimited(
                            List::ExpressionCases,
                            Group::Brace,
                            Symbol::Comma,
                            Self::expression_case,
                        )?;
                        Some((Expression::Case, Some(expr), Some(cases)))
                    }
                    Token::Keyword(Keyword::Loop) => {
                        parser.skip();
                        let lhs = parser.expression()?;
                        Some((Expression::Loop, Some(lhs), None))
                    }
                    Token::Keyword(Keyword::Try) => {
                        parser.skip();
                        let lhs = parser.expression()?;

                        let handlers =
                            parser.check_then(Token::Keyword(Keyword::With), |parser| {
                                parser.many(List::Handlers, |parser| {
                                    parser.consume_then(
                                        Token::Keyword(Keyword::With),
                                        Parser::handler,
                                    )
                                })
                            })?;
                        Some((Expression::TryWith, Some(lhs), handlers))
                    }
                    Token::Keyword(Keyword::If) => {
                        parser.skip();

                        let cond = parser.expression_assign::<false>()?;

                        let lhs = if parser.token_consume(Token::Keyword(Keyword::Then)) {
                            parser.expression()?
                        } else if parser.in_lambda_params() {
                            parser.lambda()?
                        } else {
                            parser.wrap(NodeVariant::Expression(Expression::Block), |parser| {
                                parser.grouped_delimited(
                                    List::Expressions,
                                    Group::Brace,
                                    Symbol::Semicolon,
                                    Parser::expression,
                                )
                            })?
                        };

                        if parser.token_consume(Token::Keyword(Keyword::Else)) {
                            let rhs = parser.expression()?;

                            let start = parser.nodes[cond].location.start;
                            let data = &parser.nodes[lhs];
                            let stmt = parser.nodes.push(NodeData {
                                variant: Some(NodeVariant::Expression(Expression::If)),
                                location: Location {
                                    start,
                                    end: data.location.end,
                                },
                                left: Some(cond),
                                right: Some(lhs),
                            });

                            Some((Expression::Else, Some(stmt), Some(rhs)))
                        } else {
                            Some((Expression::If, Some(cond), Some(lhs)))
                        }
                    }
                    Token::Keyword(Keyword::Let) => {
                        parser.skip();
                        let mutable = parser.token_consume(Token::Keyword(Keyword::Mut));
                        let id = parser.typed_identifier()?;
                        parser.token_expect(Token::Symbol(Symbol::Equals))?;
                        let val = parser.expression()?;
                        Some((Expression::Let { mutable }, Some(id), Some(val)))
                    }
                    Token::Keyword(Keyword::Do) => {
                        parser.skip();
                        let expr = parser.expression()?;
                        Some((Expression::Do, Some(expr), None))
                    }
                    Token::Keyword(Keyword::Break) => {
                        parser.skip();
                        if parser.token_peek().is_some_and(|t| {
                            !matches!(
                                t.token,
                                Token::Symbol(Symbol::Comma)
                                    | Token::Symbol(Symbol::Semicolon)
                                    | Token::Close(_)
                            )
                        }) {
                            let expr = parser.expression()?;
                            Some((Expression::Break, Some(expr), None))
                        } else {
                            Some((Expression::Break, None, None))
                        }
                    }
                    _ => None,
                })
            },
        )
    }
    fn type_(&mut self) -> Result<NonZeroU32> {
        self.peeked(
            NodeVariant::Type,
            |parser| parser.wrap(NodeVariant::Type(Type::Path), Self::full_identifier),
            |parser, peek| {
                Ok(match peek {
                    Token::Symbol(Symbol::Bang) => {
                        parser.skip();
                        Some((Type::Never, None, None))
                    }
                    Token::Keyword(Keyword::Type) => {
                        parser.skip();
                        Some((Type::Type, None, None))
                    }
                    Token::Keyword(Keyword::Effect) => {
                        parser.skip();
                        Some((Type::Effect, None, None))
                    }
                    Token::Keyword(Keyword::Typeof) => {
                        parser.skip();
                        let constant = parser.constant()?;
                        Some((Type::Typeof, Some(constant), None))
                    }
                    Token::Open(Group::Bracket) => {
                        parser.skip();
                        if parser.token_consume(Token::Close(Group::Bracket)) {
                            let typ = parser.type_()?;
                            Some((Type::Slice, Some(typ), None))
                        } else {
                            let size = parser.constant()?;
                            parser.token_expect(Token::Close(Group::Bracket))?;
                            let typ = parser.type_()?;
                            Some((Type::Array, Some(size), Some(typ)))
                        }
                    }
                    Token::Symbol(Symbol::Caret) => {
                        parser.skip();
                        let typ = parser.type_()?;
                        Some((Type::Pointer { maybe: false }, Some(typ), None))
                    }
                    Token::Symbol(Symbol::Question) => {
                        parser.skip();
                        parser.token_expect(Token::Symbol(Symbol::Caret))?;
                        let typ = parser.type_()?;
                        Some((Type::Pointer { maybe: true }, Some(typ), None))
                    }
                    Token::Keyword(Keyword::Struct) => {
                        parser.skip();
                        let members = parser.grouped_delimited(
                            List::Members,
                            Group::Parenthesis,
                            Symbol::Comma,
                            Self::member,
                        )?;
                        Some((Type::Struct, Some(members), None))
                    }
                    _ => None,
                })
            },
        )
    }
    fn lambda(&mut self) -> Result<NonZeroU32> {
        let params = self.in_lambda_params();
        let group = self.grouped(Group::Brace, |parser| {
            parser.node(NodeVariant::Lambda, |parser| {
                let params = if params {
                    let ids = parser.delimited(
                        List::Identifiers,
                        Symbol::Comma,
                        |t| t == Token::Symbol(Symbol::Arrow),
                        Self::identifier,
                    );
                    parser.token_expect(Token::Symbol(Symbol::Arrow))?;
                    Some(ids)
                } else {
                    None
                };
                let exprs = parser.delimited(
                    List::Expressions,
                    Symbol::Semicolon,
                    |t| t == Token::Close(Group::Brace),
                    Self::expression,
                );
                Ok((params, Some(exprs)))
            })
        })?;
        let group = group.unwrap(); // TODO
        Ok(group)
    }
    fn handler(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::Handler, |parser| {
            let id = parser.generic_identifier()?;
            let definitions = parser.handler_impl()?;
            Ok((Some(id), definitions))
        })
    }
    fn handler_impl(&mut self) -> Result<Option<NonZeroU32>> {
        self.check_then(Token::Open(Group::Brace), |parser| {
            if parser.in_lambda_params() {
                parser.lambda()
            } else {
                parser.grouped_delimited(
                    List::ConstrainedDefinitions,
                    Group::Brace,
                    Symbol::Semicolon,
                    Self::definition,
                )
            }
        })
    }
    fn identifier(&mut self) -> Result<NonZeroU32> {
        self.leaf(
            NodeVariant::Identifier(Identifier::Identifier),
            Token::Literal(Literal::Identifier),
        )
    }
    fn constant_case(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::ConstantCase, |parser| {
            let cases = if parser.token_consume(Token::Keyword(Keyword::Else)) {
                None
            } else {
                Some(parser.delimited(
                    List::Constants,
                    Symbol::Comma,
                    |t| t == Token::Symbol(Symbol::Arrow),
                    Self::constant,
                ))
            };
            parser.token_expect(Token::Symbol(Symbol::Arrow))?;
            let value = parser.constant()?;
            Ok((cases, Some(value)))
        })
    }
    fn expression_case(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::ExpressionCase, |parser| {
            let cases = if parser.token_consume(Token::Keyword(Keyword::Else)) {
                None
            } else {
                Some(parser.delimited(
                    List::Constants,
                    Symbol::Comma,
                    |t| t == Token::Symbol(Symbol::Arrow),
                    Self::constant,
                ))
            };
            parser.token_expect(Token::Symbol(Symbol::Arrow))?;
            let value = parser.expression()?;
            Ok((cases, Some(value)))
        })
    }
    fn constant(&mut self) -> Result<NonZeroU32> {
        self.peeked(
            NodeVariant::Constant,
            |parser| parser.wrap(NodeVariant::Constant(Constant::Type), Self::type_),
            |parser, peek| {
                Ok(match peek {
                    Token::Keyword(Keyword::Case) => {
                        parser.skip();
                        let constant = parser.constant()?;
                        let cases = parser.grouped_delimited(
                            List::ConstantCases,
                            Group::Brace,
                            Symbol::Comma,
                            Self::constant_case,
                        )?;
                        Some((Constant::Case, Some(constant), Some(cases)))
                    }
                    Token::Symbol(Symbol::DashDashDash) => {
                        parser.skip();
                        Some((Constant::Uninit, None, None))
                    }
                    Token::Keyword(Keyword::Alignof) => {
                        parser.skip();
                        let typ = parser.type_()?;
                        Some((Constant::Alignof, Some(typ), None))
                    }
                    Token::Keyword(Keyword::Sizeof) => {
                        parser.skip();
                        let typ = parser.type_()?;
                        Some((Constant::Sizeof, Some(typ), None))
                    }
                    Token::Open(Group::Bracket) if !parser.in_array_type() => {
                        let constants = parser.grouped_delimited(
                            List::Constants,
                            Group::Bracket,
                            Symbol::Comma,
                            Self::constant,
                        )?;
                        Some((Constant::Array, Some(constants), None))
                    }
                    Token::Open(Group::Parenthesis) => {
                        let constants = parser.grouped_delimited(
                            List::Constants,
                            Group::Parenthesis,
                            Symbol::Comma,
                            Self::constant,
                        )?;
                        Some((Constant::Struct, Some(constants), None))
                    }
                    Token::Literal(Literal::Integer) => {
                        parser.skip();
                        Some((Constant::Integer, None, None))
                    }
                    Token::Symbol(Symbol::Zero) => {
                        parser.skip();
                        Some((Constant::Zero, None, None))
                    }
                    Token::Literal(Literal::String) => {
                        parser.skip();
                        Some((Constant::String, None, None))
                    }
                    Token::Literal(Literal::Character) => {
                        parser.skip();
                        Some((Constant::Character, None, None))
                    }
                    Token::Literal(Literal::Identifier) => {
                        let id = parser.full_identifier()?;
                        Some((Constant::Path, Some(id), None))
                    }
                    _ => None,
                })
            },
        )
    }
    fn packaged_identifier(&mut self) -> Result<NonZeroU32> {
        let start = self.position();
        let id = self.identifier()?;
        if self.token_consume(Token::Symbol(Symbol::Dot)) {
            let package = id;
            let id = self.identifier()?;
            Ok(self.nodes.push(NodeData {
                variant: Some(NodeVariant::Identifier(Identifier::PackagedIdentifier)),
                location: Location {
                    start,
                    end: self.position(),
                },
                left: Some(package),
                right: Some(id),
            }))
        } else {
            Ok(id)
        }
    }
    fn full_identifier(&mut self) -> Result<NonZeroU32> {
        let start = self.position();
        let id = self.packaged_identifier()?;
        if self.token_check(Token::Open(Group::Bracket)) {
            let types = self.grouped_delimited(
                List::Constants,
                Group::Bracket,
                Symbol::Comma,
                Self::constant,
            )?;

            if self.nodes[types].left.is_none() {
                // empty list
                // TODO: give error
                panic!();
            }

            Ok(self.nodes.push(NodeData {
                variant: Some(NodeVariant::Identifier(Identifier::FullIdentifier)),
                location: Location {
                    start,
                    end: self.position(),
                },
                left: Some(id),
                right: Some(types),
            }))
        } else {
            Ok(id)
        }
    }
    fn generic_identifier(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::GenericIdentifier, |parser| {
            let generics = parser.check_then(Token::Open(Group::Bracket), |parser| {
                parser.grouped_delimited(
                    List::TypedNames,
                    Group::Bracket,
                    Symbol::Comma,
                    Self::typed_name,
                )
            })?;
            let id = parser.full_identifier()?;
            Ok((generics, Some(id)))
        })
    }
    fn name(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::Name, |parser| {
            let name = parser.identifier()?;
            let generics = parser.check_then(Token::Open(Group::Bracket), |parser| {
                parser.grouped_delimited(
                    List::TypedNames,
                    Group::Bracket,
                    Symbol::Comma,
                    Self::typed_name,
                )
            })?;
            Ok((Some(name), generics))
        })
    }
    fn constraints(&mut self) -> Option<NonZeroU32> {
        if !self.token_consume(Token::Keyword(Keyword::With)) {
            return None;
        }
        let constraints = self.delimited(
            List::Constraints,
            Symbol::Comma,
            |t| {
                matches!(
                    t,
                    Token::Symbol(Symbol::Semicolon)
                        | Token::Open(Group::Brace)
                        | Token::Keyword(Keyword::Const)
                        | Token::Keyword(Keyword::Type)
                        | Token::Keyword(Keyword::Fun)
                        | Token::Keyword(Keyword::Effect)
                        | Token::Keyword(Keyword::With)
                        | Token::Keyword(Keyword::Default)
                )
            },
            Self::constraint,
        );
        self.token_consume(Token::Symbol(Symbol::Semicolon));
        Some(constraints)
    }
    fn constraint(&mut self) -> Result<NonZeroU32> {
        let start = self.position();

        let constant = self.constant()?;

        if self.token_consume(Token::Symbol(Symbol::Tilde)) {
            // unify constants
            let other = self.constant()?;
            Ok(self.nodes.push(NodeData {
                variant: Some(NodeVariant::Constraint(Constraint::Unify)),
                location: Location {
                    start,
                    end: self.position(),
                },
                left: Some(constant),
                right: Some(other),
            }))
        } else {
            // handled effect / boolean constant
            Ok(self.nodes.push(NodeData {
                variant: Some(NodeVariant::Constraint(Constraint::Constant)),
                location: Location {
                    start,
                    end: self.position(),
                },
                left: Some(constant),
                right: None,
            }))
        }
    }
    fn typed_name(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::TypedName, |parser| {
            let name = parser.name()?;
            let typ = parser.consume_then(Token::Symbol(Symbol::Colon), Self::type_)?;
            Ok((Some(name), typ))
        })
    }
    fn typed_identifier(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::TypedIdentifier, |parser| {
            let name = parser.identifier()?;
            let typ = parser.consume_then(Token::Symbol(Symbol::Colon), Self::type_)?;
            Ok((Some(name), typ))
        })
    }
    fn member(&mut self) -> Result<NonZeroU32> {
        self.node(NodeVariant::TypedName, |parser| {
            let name = parser.identifier()?;
            parser.token_expect(Token::Symbol(Symbol::Colon))?;
            let typ = parser.type_()?;
            Ok((Some(name), Some(typ)))
        })
    }
    fn lucu(&mut self) -> NonZeroU32 {
        let imports = self.delimited(
            List::Imports,
            Symbol::Semicolon,
            |t| t != Token::Keyword(Keyword::Import),
            Self::import,
        );
        let definitions = self.delimited(
            List::ConstrainedDefinitions,
            Symbol::Semicolon,
            |_| false,
            Self::definition,
        );
        self.nodes.push(NodeData {
            variant: Some(NodeVariant::Lucu),
            location: Location {
                start: 0,
                end: self.position(),
            },
            left: Some(imports),
            right: Some(definitions),
        })
    }
}
