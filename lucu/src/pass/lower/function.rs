use std::iter;
use std::sync::Arc;

use compact_str::ToCompactString;
use itertools::Either;

use crate::ast;
use crate::error::{Problems, Result};
use crate::header::{FunctionDefinition, IntrinsicFunction, ItemDecl};
use crate::module::Module;
use crate::mu::{self, ExpressionTable as _, TypeTable as _};
use crate::pass::defs::Definitions;
use crate::pass::imports::Imports;
use crate::pass::lower::{HeaderQuery, Lower};
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionSignature,
    GenericArgument, IntSize, Integer, SimpleKind, Term, Type, TypeEnum, TypeTable,
};

#[derive(Clone, Copy, Debug)]
enum Var<'a> {
    Named(&'a str, FunctionParameter),
    Effect(Effect),
    Raise(Type),
    Unit,
}

struct MuLower<'a, 'scope> {
    lower: Lower<'a, 'scope>,
    tt: &'a mu::table::TypeTable,
    et: &'a mu::table::ExpressionTable,
    vars: im::Vector<Var<'a>>,
    markers: im::Vector<Effect>,
}

impl<'a, 'scope> MuLower<'a, 'scope> {
    fn reborrow<'short>(&'short mut self) -> MuLower<'a, 'short> {
        MuLower {
            lower: self.lower.reborrow(),
            tt: self.tt,
            et: self.et,
            vars: self.vars.clone(),
            markers: self.markers.clone(),
        }
    }
}

impl mu::Module {
    pub fn from(
        query: &impl HeaderQuery,
        module: &Module,
        ast: &ast::Module,
        imports: &Imports,
        defs: &Definitions,
        tt: &TypeTable,
        mu_tt: &mu::table::TypeTable,
        mu_et: &mu::table::ExpressionTable,
    ) -> Result<Self> {
        let mut used_underscore = false;
        let mut lower = MuLower {
            lower: Lower {
                tt,
                module,
                imports,
                query,

                generics: im::HashMap::new(),
                used_underscore: &mut used_underscore,
                next_implicit_region: None,
                implicit_region_offset: 0,
                implicit_effects: None,
            },
            tt: mu_tt,
            et: mu_et,
            vars: im::Vector::new(),
            markers: im::Vector::new(),
        };
        query
            .header(module, tt)
            .expect("ICE: could not query own header")
            .items()
            .filter_map(|(name, decl)| {
                // TODO: effect functions
                let &ItemDecl::Function(sig, None, FunctionDefinition::Other(node)) = decl else {
                    return None;
                };
                let ast::Item::Function(decl, Some((_, def))) = defs.item(node, ast) else {
                    return None;
                };
                Some(lower.function(name, sig, decl, def))
            })
            .collect::<Result<_>>()
            .map(|functions| mu::Module { functions })
    }
}

struct UseArg<'a> {
    params: Option<&'a ast::Separated<ast::LambdaParameter>>,
    block: &'a ast::Separated<Box<ast::Expression>>,
}

enum PathType {
    Data(Type),
    Function(FunctionSignature, Arc<[GenericArgument]>),
}

impl From<FunctionParameter> for PathType {
    fn from(value: FunctionParameter) -> Self {
        match value {
            FunctionParameter::Data(ty) => Self::Data(ty),
            FunctionParameter::Lambda(sig) => Self::Function(sig, Arc::new([])),
        }
    }
}

impl<'a, 'scope> MuLower<'a, 'scope> {
    fn function(
        &mut self,
        name: &'scope str,
        sig: FunctionSignature,
        decl: &'a ast::FunctionDeclaration,
        def: &'a ast::FunctionDefinition,
    ) -> Result<mu::Function> {
        match def {
            ast::FunctionDefinition::Expression(body) => {
                let ty = self.function_type(sig, Some(decl));
                self.abstraction(
                    sig,
                    decl.parameters
                        .iter()
                        .flat_map(|params| params.inner.iter())
                        .map(|param| (param.name(), None)),
                    iter::once(&**body),
                )
                .map(|lambda| {
                    let mu::ExpressionEnum::Abstract(_, body) = self.et[lambda] else {
                        panic!("ICE: abstraction did not give lambda expression")
                    };
                    mu::Function {
                        item: mu::Item {
                            module: self.lower.module.clone(),
                            item: name.into(),
                        },
                        ty,
                        body,
                        // TODO: specify this in the language
                        linkage: if name == "_start" {
                            Some(mu::Linkage::External)
                        } else {
                            None
                        },
                    }
                })
            }
            ast::FunctionDefinition::Intrinsic(_) => todo!("error"),
        }
    }
    fn abstraction(
        &mut self,
        sig: FunctionSignature,
        params: impl IntoIterator<Item = (&'a ast::Identifier, Option<&'a ast::Type>)>,
        body: impl IntoIterator<IntoIter = impl ExactSizeIterator<Item = &'a ast::Expression>>,
    ) -> Result<mu::Expression> {
        let mut me = self.reborrow();
        let sig_val = &me.lower.tt[sig];
        let from = me.tt.insert_tuple(Iterator::chain(
            sig_val
                .params
                .iter()
                .flat_map(|params| params.iter().copied())
                .map(|param| me.function_param(param)),
            sig_val
                .thunk
                .effect
                .effects(me.lower.tt)
                .filter_map(|e| me.effect(e).map(|(_, t)| t)),
        ));
        let params = Iterator::zip(
            params.into_iter().map(|(param, _ty)| {
                // TODO: check user given type
                param.as_str()
            }),
            sig_val
                .params
                .iter()
                .flat_map(|params| params.iter().copied()),
        )
        .map(|(name, param)| Var::Named(name, param));
        for param in params {
            me.vars.push_front(param);
        }
        for effect in sig_val.thunk.effect.effects(me.lower.tt) {
            if effect.is_marker(me.lower.tt) {
                me.markers.push_front(effect);
            } else {
                me.vars.push_front(Var::Effect(effect));
            }
        }
        me.statements(body, Some(sig_val.thunk.returns))
            .map(|(expr, _)| self.et.lambda(from, expr))
    }
    fn find_named(&self, name: &str) -> Option<(u32, FunctionParameter)> {
        self.vars
            .iter()
            .enumerate()
            .find_map(|(index, &var)| match var {
                Var::Named(n, ty) if n == name => Some((index as u32, ty)),
                _ => None,
            })
    }
    fn has_marker_effect(&self, effect: Effect) -> bool {
        self.markers.contains(&effect)
    }
    fn find_effect(&self, effect: Effect) -> Option<u32> {
        self.vars
            .iter()
            .enumerate()
            .find_map(|(index, &var)| match var {
                Var::Effect(e) if e == effect => Some(index as u32),
                _ => None,
            })
    }
    fn find_raise(&self) -> Option<(u32, Type)> {
        self.vars
            .iter()
            .enumerate()
            .find_map(|(index, &var)| match var {
                Var::Raise(ty) => Some((index as u32, ty)),
                _ => None,
            })
    }
    fn path(
        &mut self,
        path: &'a ast::Path,
    ) -> Result<(Either<mu::Expression, IntrinsicFunction>, PathType)> {
        if let ast::PathOrigin::Local(local) = &path.origin
            && let Some((index, ty)) = self.find_named(local.as_str())
        {
            if let Some(_generics) = &path.generics {
                todo!("generic local function")
            }
            let mu_ty = self.function_param(ty);
            Result::new((Either::Left(self.et.reference(mu_ty, index)), ty.into()))
        } else {
            let (module, name, item) = match self.lower.item_ref(path) {
                Ok((module, name, item)) => (module, name, item),
                Err(problems) => return problems.error(),
            };
            match *item {
                ItemDecl::Alias(kind, term) => self
                    .lower
                    .apply(kind, term, path.generics.as_ref())
                    .and_then(|(kind, term)| {
                        self.lower
                            .apply(kind, term, path.generics.as_ref())
                            .and_then(|(kind, term)| {
                                let kind_enum = &self.lower.tt[kind];
                                if kind_enum.params.is_some() {
                                    todo!("error")
                                }
                                let SimpleKind::Constant(ty) = kind_enum.output else {
                                    todo!("error")
                                };
                                let Term::Constant(c) = term else {
                                    panic!("ICE: constant kind but not constant term")
                                };
                                Result::new((
                                    Either::Left(self.constant(ty, c)),
                                    PathType::Data(ty),
                                ))
                            })
                    }),
                ItemDecl::Struct(_, _) => todo!("struct constructor"),
                ItemDecl::Effect(_, _) => todo!("error"),
                ItemDecl::Function(sig, effect, def) => {
                    let module = module.clone();
                    self.lower
                        .apply_sig(sig, effect, path.generics.as_ref())
                        .and_then(|(sig, effect, generics)| {
                            let ty = PathType::Function(sig, generics);
                            match effect {
                                Some(e) => match self.find_effect(e) {
                                    Some(_index) => todo!(),
                                    None => todo!("error: effect not on stack"),
                                },
                                None => Result::new((
                                    match def {
                                        FunctionDefinition::Intrinsic(i) => Either::Right(i),
                                        FunctionDefinition::Other(_) => {
                                            let item = mu::Item {
                                                module,
                                                item: name.to_compact_string(),
                                            };
                                            let ty = self.function_type(sig, None);
                                            Either::Left(self.et.operation(
                                                mu::Operation::Callable(
                                                    mu::Callable::ModuleFunction { item, ty },
                                                ),
                                            ))
                                        }
                                    },
                                    ty,
                                )),
                            }
                        })
                }
            }
        }
    }
    fn call(
        &mut self,
        call: &'a ast::Call,
        use_arg: Option<UseArg<'a>>,
    ) -> Result<(mu::Expression, Type)> {
        self.path(&call.fun).and_then(|(fun, fun_ty)| {
            let PathType::Function(sig, generics) = fun_ty else {
                todo!("error")
            };
            let sig_val = &self.lower.tt[sig];
            if let Some(_generics) = &sig_val.type_params {
                todo!("error: must specify generics right now")
            }
            // FIXME: we need to infer region generics
            if let Some(params) = &sig_val.params {
                if params.len() != call.count_args() + use_arg.is_some() as usize {
                    todo!("error: incorrect amount of arguments")
                }
                let mut problems = Problems::ok();
                let mut args = Iterator::zip(params.iter().copied(), call.args())
                    .map(|(param, arg)| {
                        problems
                            .append(match param {
                                FunctionParameter::Data(ty) => {
                                    self.expression(arg, Some(ty)).map(|(mu, _)| mu)
                                }
                                FunctionParameter::Lambda(sig) => {
                                    let sig_val = &self.lower.tt[sig];
                                    if sig_val.type_params.as_ref().is_some_and(|ps| {
                                        ps.iter()
                                            .any(|&k| self.lower.tt[k].output != SimpleKind::Region)
                                    }) {
                                        todo!("error: no support for generics yet")
                                    }
                                    if let ast::Expression::Block(block) = arg {
                                        if block
                                            .inner
                                            .params
                                            .as_ref()
                                            .map(|(params, _)| params.elements.len())
                                            != sig_val.params.as_ref().map(|params| params.len())
                                        {
                                            todo!("error")
                                        }
                                        self.abstraction(
                                            sig,
                                            block
                                                .inner
                                                .params
                                                .iter()
                                                .flat_map(|(lambda, _)| lambda.iter())
                                                .map(|lambda| (&lambda.var, lambda.ty.as_deref())),
                                            block.inner.stmts.iter().map(|e| &**e),
                                        )
                                    } else if sig_val.params.is_some() {
                                        todo!("error")
                                    } else {
                                        self.abstraction(sig, [], [arg])
                                    }
                                }
                            })
                            .unwrap_or_else(|| self.et.unreachable())
                    })
                    .collect::<Vec<_>>();
                if let Some(arg) = use_arg {
                    args.push({
                        let param = params.last().copied().unwrap();
                        let FunctionParameter::Lambda(sig) = param else {
                            todo!("error")
                        };
                        let sig_val = &self.lower.tt[sig];
                        if sig_val.type_params.as_ref().is_some_and(|ps| {
                            ps.iter()
                                .any(|&k| self.lower.tt[k].output != SimpleKind::Region)
                        }) {
                            todo!("error: no support for generics yet")
                        }
                        if arg.params.map(|params| params.elements.len())
                            != sig_val.params.as_ref().map(|params| params.len())
                        {
                            todo!("error")
                        }
                        problems
                            .append(
                                self.abstraction(
                                    sig,
                                    arg.params
                                        .into_iter()
                                        .flat_map(|lambda| lambda.iter())
                                        .map(|lambda| (&lambda.var, lambda.ty.as_deref())),
                                    arg.block.iter().map(|e| &**e),
                                ),
                            )
                            .unwrap_or_else(|| self.et.unreachable())
                    });
                }
                // FIXME: supply effect handlers too
                let mu = match fun {
                    Either::Left(fun) => self.et.apply(fun, args),
                    Either::Right(i) => self.intrinsic(i, generics, args),
                };
                problems.with((mu, sig_val.thunk.returns))
            } else if call.args.is_some() || call.block.is_some() {
                todo!("error: function has no arguments")
            } else {
                match fun {
                    Either::Left(fun) => {
                        Result::new((self.et.apply(fun, []), sig_val.thunk.returns))
                    }
                    Either::Right(_) => todo!(),
                }
            }
        })
    }
    fn intrinsic(
        &self,
        i: IntrinsicFunction,
        generics: Arc<[GenericArgument]>,
        args: impl IntoIterator<Item = mu::Expression>,
    ) -> mu::Expression {
        match i {
            IntrinsicFunction::Ref => {
                let Term::Type(ty) = generics[0].term else {
                    panic!()
                };
                let Term::Type(to) = generics[1].term else {
                    panic!()
                };
                let mut args = args.into_iter();
                let val = args.next().unwrap();
                let lambda = args.next().unwrap();
                let ty = self.r#type(ty);
                let to = self.r#type(to);
                self.et
                    .call(mu::Callable::LetReference { ty, to }, [val, lambda])
            }
            IntrinsicFunction::Alloca => {
                let Term::Type(ty) = generics[0].term else {
                    panic!()
                };
                let Term::Type(to) = generics[1].term else {
                    panic!()
                };
                let mut args = args.into_iter();
                let val = args.next().unwrap();
                let lambda = args.next().unwrap();
                let ty = self.r#type(ty);
                let to = self.r#type(to);
                self.et
                    .call(mu::Callable::LetAlloca { ty, to }, [val, lambda])
            }
            IntrinsicFunction::Link => todo!(),
            IntrinsicFunction::Asm | IntrinsicFunction::AsmPure => {
                let Term::Constant(assembly) = generics[0].term else {
                    panic!()
                };
                let ConstantEnum::String(assembly) = &self.lower.tt[assembly] else {
                    panic!()
                };
                let Term::Constant(constraints) = generics[1].term else {
                    panic!()
                };
                let ConstantEnum::String(constraints) = &self.lower.tt[constraints] else {
                    panic!()
                };
                let Term::Type(from) = generics[2].term else {
                    panic!()
                };
                let Term::Type(to) = generics[3].term else {
                    panic!()
                };
                self.et.call(
                    mu::Callable::Asm {
                        assembly: assembly.clone(),
                        constraints: constraints.clone(),
                        side_effects: i == IntrinsicFunction::Asm,
                        from: self.r#type(from),
                        to: self.r#type(to),
                    },
                    args,
                )
            }
            IntrinsicFunction::LocationPath => todo!(),
            IntrinsicFunction::LocationLine => todo!(),
            IntrinsicFunction::LocationColumn => todo!(),
            IntrinsicFunction::Len => {
                let Term::Type(ty) = generics[0].term else {
                    panic!()
                };
                self.et.call(
                    mu::Callable::Len {
                        ty: self.r#type(ty),
                    },
                    args,
                )
            }
            IntrinsicFunction::Unreachable => self.et.operation(mu::Operation::Unreachable),
            IntrinsicFunction::Loop => {
                let mut args = args.into_iter();
                let body = args.next().unwrap();
                // let _div = args.next().unwrap();
                self.et.call(mu::Callable::Loop, [body])
            }
            IntrinsicFunction::Unfounded => {
                let mu::ExpressionEnum::Abstract(_, body) =
                    self.et[args.into_iter().next().unwrap()]
                else {
                    panic!("ICE: unfounded arg is not a function")
                };
                body
            }
            IntrinsicFunction::Trace => {
                let mut args = args.into_iter();
                let slice = args.next().unwrap();
                // let _read = args.next().unwrap();
                let mu_usize = self.tt.base(mu::Base::SIZE);
                let mu_uptr = self.tt.base(mu::Base::ADDR);
                let mu_u8 = self.tt.base(mu::Base::U8);
                let mu_u8_ptr = self.tt.base(mu::Base::Pointer(mu_u8));
                let mu_u8_slice = self.tt.base(mu::Base::PointerSlice(mu_u8));
                self.et.let_chain(
                    [slice],
                    self.et.call(
                        mu::Callable::Syscall { args: 3 },
                        [
                            self.et.constant(mu_uptr, mu::Constant::Integer(1)),
                            self.et.constant(mu_uptr, mu::Constant::Integer(0)),
                            self.et.cast(
                                mu_u8_ptr,
                                mu_uptr,
                                ast::Cast::Transmute,
                                self.et.call(
                                    mu::Callable::PointerSliceIndex { ty: mu_u8 },
                                    [
                                        self.et.reference(mu_u8_slice, 0),
                                        self.et.constant(mu_usize, mu::Constant::Zero),
                                    ],
                                ),
                            ),
                            self.et.cast(
                                mu_usize,
                                mu_uptr,
                                ast::Cast::Extend,
                                self.et.call(
                                    mu::Callable::Len { ty: mu_u8 },
                                    [self.et.reference(mu_u8_slice, 0)],
                                ),
                            ),
                        ],
                    ),
                )
            }
        }
    }
    fn constant(&self, ty: Type, c: Constant) -> mu::Expression {
        match self.lower.tt[c] {
            ConstantEnum::Generic(_) => todo!(),
            ConstantEnum::True => {
                let bool = self.tt.bool();
                self.et.push_expression(mu::ExpressionEnum::Variant(
                    bool.into_sum(self.tt),
                    1,
                    self.et.construct_unit(self.tt),
                ))
            }
            ConstantEnum::False => {
                let bool = self.tt.bool();
                self.et.push_expression(mu::ExpressionEnum::Variant(
                    bool.into_sum(self.tt),
                    0,
                    self.et.construct_unit(self.tt),
                ))
            }
            ConstantEnum::Integer(int) => self
                .et
                .constant(self.r#type(ty), mu::Constant::Integer(int)),
            ConstantEnum::String(ref str) => {
                // FIXME: if the type has a sentinel we need to add that to the end
                self.et
                    .constant(self.r#type(ty), mu::Constant::String(str.clone()))
            }
            ConstantEnum::Character(ref str) => {
                let TypeEnum::Integer(i) = self.lower.tt[ty] else {
                    panic!("ICE: character constant is not of integer type");
                };
                let mu_ty = self.tt.base(mu::Base::Integer(i));
                let value = match i {
                    Integer::CChar | Integer::Integer(_, IntSize::Exact(8) | IntSize::CChar) => {
                        let &[byte] = str.as_bytes() else {
                            panic!("ICE: character constant is not a single byte")
                        };
                        byte as u64
                    }
                    Integer::Integer(_, IntSize::Exact(32)) => {
                        let mut chars = str.chars();
                        let Some(char) = chars.next() else {
                            panic!("ICE: character constant does not contain a codepoint");
                        };
                        let None = chars.next() else {
                            panic!("ICE: character constant contains multiple codepoints");
                        };
                        char as u64
                    }
                    _ => panic!("ICE: unknown character constant integer size"),
                };
                self.et.constant(mu_ty, mu::Constant::Integer(value))
            }
            ConstantEnum::Zero => self.et.constant(self.r#type(ty), mu::Constant::Zero),
        }
    }
    fn expression(
        &mut self,
        expr: &'a ast::Expression,
        expected: Option<Type>,
    ) -> Result<(mu::Expression, Type)> {
        match expr {
            ast::Expression::Let { .. } => {
                panic!("ICE: let expressions should be managed by MuLower::statements")
            }
            ast::Expression::Constant(constant) => {
                let Some(ty) = expected else {
                    todo!("error: not enough info")
                };
                self.lower
                    .constant(constant, ty)
                    .map(|c| (self.constant(ty, c), ty))
            }
            ast::Expression::Uninit(_) => {
                // TODO: check if uninit is allowed for this type
                let Some(ty) = expected else {
                    todo!("error: not enough info")
                };
                Result::new((self.et.constant(self.r#type(ty), mu::Constant::Uninit), ty))
            }
            ast::Expression::Path(path) => {
                if let ast::PathOrigin::Package(lhs, _, _rhs) = &path.origin
                    && let Some((_index, _ty)) = self.find_named(lhs.as_str())
                {
                    if let Some(_generics) = &path.generics {
                        todo!("error")
                    }
                    // TODO: this does not include member access of local constant right now
                    todo!("member access")
                } else {
                    self.path(path).and_then(|(e, p)| match p {
                        PathType::Data(ty) => Result::new((e.unwrap_left(), ty)),
                        PathType::Function(sig, generics) => {
                            let sig_val = &self.lower.tt[sig];
                            if let Some(_params) = &sig_val.params {
                                todo!("error")
                            }
                            Result::new((
                                match e {
                                    Either::Left(e) => self.et.apply(e, []),
                                    Either::Right(i) => self.intrinsic(i, generics, []),
                                },
                                sig_val.thunk.returns,
                            ))
                        }
                    })
                }
            }
            ast::Expression::Block(block) => {
                if let Some(_params) = &block.inner.params {
                    todo!("error")
                }
                let stmts = block.inner.stmts.iter().map(|e| &**e);
                self.reborrow().statements(stmts, expected)
            }
            ast::Expression::Enclosed(expr) => self.expression(&expr.inner, expected),
            ast::Expression::Cast { op, expr, .. } => {
                let Some(to) = expected else {
                    todo!("error: not enough info")
                };
                self.expression(expr, None).map(|(value, from)| {
                    (
                        self.et.cast(self.r#type(from), self.r#type(to), *op, value),
                        to,
                    )
                })
            }
            ast::Expression::If {
                condition,
                branch_true,
                branch_false,
                ..
            } => self
                .expression(
                    condition,
                    Some(self.lower.tt.insert_type(TypeEnum::Boolean)),
                )
                .and_then(|(condition, _)| {
                    // this is a match expression under the hood
                    // so we need to push the unit bool variant on the var stack
                    let mut self_inner = self.reborrow();
                    self_inner.vars.push_front(Var::Unit);
                    self_inner
                        .expression(&branch_true.1, expected)
                        .and_then(|(then_branch, ty)| match branch_false {
                            Some((_, branch_false)) => self_inner
                                .expression(branch_false, Some(ty))
                                .map(|(else_branch, _)| {
                                    (
                                        self_inner.et.if_else(condition, then_branch, else_branch),
                                        ty,
                                    )
                                }),
                            None if ty != self_inner.lower.tt.insert_type(TypeEnum::Unit) => {
                                todo!("error")
                            }
                            None => Result::new((
                                self_inner.et.if_stmt(self_inner.tt, condition, then_branch),
                                ty,
                            )),
                        })
                }),
            ast::Expression::Discard { expr, .. } => self
                .expression(expr, None)
                .map(|(mu, _)| (mu, self.lower.tt.insert_type(TypeEnum::Unit))),
            ast::Expression::AssignOp(op, lhs, _, rhs) => {
                let ast::Expression::Dereference { expr, .. } = &**lhs else {
                    todo!("error")
                };
                self.expression(expr, None).and_then(|(lhs, ty)| {
                    let TypeEnum::Pointer(inner, _) = self.lower.tt[ty] else {
                        todo!("error")
                    };
                    self.expression(rhs, Some(inner)).and_then(|(rhs, _)| {
                        let mu_inner = self.r#type(inner);
                        let val = match op {
                            &ast::AssignOp::Math(op) => {
                                // TODO: check for read effect
                                self.et.call(
                                    mu::Callable::MathOp { ty: mu_inner, op },
                                    [
                                        self.et.call(mu::Callable::Read { ty: mu_inner }, [lhs]),
                                        rhs,
                                    ],
                                )
                            }
                            ast::AssignOp::Assign => rhs,
                        };
                        // TODO: check for write effect
                        Result::new((
                            self.et
                                .call(mu::Callable::Write { ty: mu_inner }, [lhs, val]),
                            self.lower.tt.insert_type(TypeEnum::Unit),
                        ))
                    })
                })
            }
            ast::Expression::PredicateOp(op, lhs, _, rhs) => {
                self.expression(lhs, None).and_then(|(lhs, ty)| {
                    self.expression(rhs, Some(ty)).map(|(rhs, _)| {
                        (
                            self.et.call(
                                mu::Callable::PredicateOp {
                                    ty: self.r#type(ty),
                                    op: *op,
                                },
                                [lhs, rhs],
                            ),
                            self.lower.tt.insert_type(TypeEnum::Boolean),
                        )
                    })
                })
            }
            ast::Expression::MathOp(op, lhs, _, rhs) => {
                self.expression(lhs, expected).and_then(|(lhs, ty)| {
                    self.expression(rhs, Some(ty)).map(|(rhs, _)| {
                        (
                            self.et.call(
                                mu::Callable::MathOp {
                                    ty: self.r#type(ty),
                                    op: *op,
                                },
                                [lhs, rhs],
                            ),
                            ty,
                        )
                    })
                })
            }
            ast::Expression::UnOp { op, expr, .. } => {
                self.expression(expr, expected).map(|(e, ty)| {
                    (
                        self.et.call(
                            mu::Callable::UnOp {
                                ty: self.r#type(ty),
                                op: *op,
                            },
                            [e],
                        ),
                        ty,
                    )
                })
            }
            ast::Expression::Dereference { expr, .. } => {
                self.expression(expr, None).and_then(|(e, ty)| {
                    let TypeEnum::Pointer(inner, _region) = self.lower.tt[ty] else {
                        todo!("error")
                    };
                    // TODO: check for read effect
                    Result::new((
                        self.et.call(
                            mu::Callable::Read {
                                ty: self.r#type(inner),
                            },
                            [e],
                        ),
                        inner,
                    ))
                })
            }
            ast::Expression::Index { array, index } => {
                self.expression(array, None).and_then(|(array, ty)| {
                    match (&self.lower.tt[ty], &index.inner) {
                        (
                            &TypeEnum::PointerSlice(ty, region, sentinel_ty),
                            ast::Index::Single(expr),
                        ) => self
                            .expression(expr, Some(self.lower.tt.insert_type(TypeEnum::SIZE)))
                            .map(|(index, _)| match sentinel_ty {
                                Some(_) => (
                                    self.et.call(
                                        mu::Callable::MultiPointerIndex {
                                            ty: self.r#type(ty),
                                        },
                                        [array, index],
                                    ),
                                    self.lower.tt.insert_type(TypeEnum::Pointer(ty, region)),
                                ),
                                None => (
                                    self.et.call(
                                        mu::Callable::PointerSliceIndex {
                                            ty: self.r#type(ty),
                                        },
                                        [array, index],
                                    ),
                                    self.lower.tt.insert_type(TypeEnum::Pointer(ty, region)),
                                ),
                            }),
                        (
                            &TypeEnum::PointerSlice(ty, _, sentinel_ty),
                            ast::Index::Range {
                                from, to, sentinel, ..
                            },
                        ) => todo!("slice slice"),
                        (
                            &TypeEnum::Array(ty, size, sentinel_ty),
                            ast::Index::Single(expression),
                        ) => {
                            todo!("index array")
                        }
                        (
                            &TypeEnum::Array(ty, size, sentinel_ty),
                            ast::Index::Range {
                                from, to, sentinel, ..
                            },
                        ) => todo!("slice array"),
                        (&TypeEnum::Pointer(pointee, region), ast::Index::Single(expr))
                            if let TypeEnum::Array(ty, size, sentinel_ty) =
                                self.lower.tt[pointee] =>
                        {
                            self.expression(expr, Some(self.lower.tt.insert_type(TypeEnum::SIZE)))
                                .map(|(index, _)| {
                                    let size = self.array_size(size) + sentinel_ty.is_some() as u32;
                                    (
                                        self.et.call(
                                            mu::Callable::PointerArrayIndex {
                                                ty: self.r#type(ty),
                                                size,
                                            },
                                            [array, index],
                                        ),
                                        self.lower.tt.insert_type(TypeEnum::Pointer(ty, region)),
                                    )
                                })
                        }
                        (
                            &TypeEnum::Pointer(pointee, region),
                            ast::Index::Range {
                                from, to, sentinel, ..
                            },
                        ) if let TypeEnum::Array(ty, size, sentinel_ty) =
                            self.lower.tt[pointee] =>
                        {
                            let max = self.array_size(size);
                            let size = max + sentinel_ty.is_some() as u32;
                            let usize_t = self.lower.tt.insert_type(TypeEnum::SIZE);
                            let mu_usize = self.r#type(usize_t);
                            let from_index = from
                                .as_ref()
                                .map(|expr| {
                                    self.expression(expr, Some(usize_t)).map(|(expr, _)| expr)
                                })
                                .unwrap_or_else(|| {
                                    Result::new(self.et.constant(mu_usize, mu::Constant::Zero))
                                });
                            let to_index = to
                                .as_ref()
                                .map(|expr| {
                                    self.expression(expr, Some(usize_t)).map(|(expr, _)| expr)
                                })
                                .unwrap_or_else(|| {
                                    Result::new(
                                        self.et
                                            .constant(mu_usize, mu::Constant::Integer(max as u64)),
                                    )
                                });
                            from_index.and_then(|from_index| {
                                to_index.map(|to_index| {
                                    (
                                        self.et.call(
                                            mu::Callable::PointerArraySlice {
                                                ty: self.r#type(ty),
                                                size,
                                            },
                                            [array, from_index, to_index],
                                        ),
                                        self.lower.tt.insert_type(TypeEnum::PointerSlice(
                                            ty,
                                            region,
                                            sentinel_ty.filter(|_| to.is_none()),
                                        )),
                                    )
                                })
                            })
                        }
                        _ => todo!("error"),
                    }
                })
            }
            ast::Expression::Array(exprs) => {
                let Some(ty) = expected else {
                    todo!("error: not enough info")
                };
                match self.lower.tt[ty] {
                    TypeEnum::PointerSlice(_, _, _) => todo!(),
                    TypeEnum::Array(inner, constant, s) => {
                        if let Some(s) = s {
                            todo!("add sentinel value");
                        }
                        let size = self.array_size(constant);
                        if exprs.inner.elements.len() != size as usize {
                            todo!("error");
                        }

                        let mut problems = Problems::ok();
                        let mu_inner = self.r#type(inner);
                        let et = self.et;
                        let args = exprs.inner.iter().map(|elem| {
                            problems
                                .append(self.expression(elem, Some(inner)))
                                .map_or_else(|| self.et.unreachable(), |(e, _)| e)
                        });
                        let construct =
                            et.call(mu::Callable::ArrayConstruct { ty: mu_inner, size }, args);
                        problems.with((construct, ty))
                    }
                    _ => todo!("error"),
                }
            }
            ast::Expression::Call(call) => self.call(call, None),
            ast::Expression::Use {
                params,
                call,
                block,
                ..
            } => self.call(
                call,
                Some(UseArg {
                    params: params.as_ref().map(|(_, params, _)| params),
                    block,
                }),
            ),
            ast::Expression::Catch { expr, .. } => {
                let Some(ty) = expected else {
                    todo!("error: not enough info")
                };
                let mut self_inner = self.reborrow();
                self_inner.vars.push_front(Var::Raise(ty));
                self_inner
                    .expression(expr, expected)
                    .map(|(e, ty)| (self_inner.et.try_break(self_inner.r#type(ty), e), ty))
            }
            ast::Expression::Raise { expr, .. } => {
                let never = self.lower.tt.insert_type(TypeEnum::Never);
                let Some((index, ty)) = self.find_raise() else {
                    todo!("error")
                };
                let f = self.et.reference(
                    self.tt
                        .function(self.tt.insert_tuple([self.r#type(ty)]), self.tt.never()),
                    index,
                );
                match expr {
                    Some(expr) => self
                        .expression(expr, Some(ty))
                        .map(|(e, _)| (self.et.apply(f, [e]), never)),
                    None if ty.is_unit(self.lower.tt) => {
                        Result::new((self.et.apply(f, [self.et.construct_unit(self.tt)]), never))
                    }
                    None => todo!("error"),
                }
            }
        }
        .and_then(|(mu, found)| {
            if let Some(expected) = expected
                && found != expected
            {
                if !found.is_never(self.lower.tt) {
                    todo!(
                        "error: found {} expected {} at {expr:?}",
                        found.display(self.lower.tt),
                        expected.display(self.lower.tt)
                    );
                }
                Result::new((mu, expected))
            } else {
                Result::new((mu, found))
            }
        })
    }
    fn statements(
        &mut self,
        stmts: impl IntoIterator<IntoIter = impl ExactSizeIterator<Item = &'a ast::Expression>>,
        expected: Option<Type>,
    ) -> Result<(mu::Expression, Type)> {
        // TODO: manage Let expressions from here
        let unit_t = self.lower.tt.insert_type(TypeEnum::Unit);
        let stmts = stmts.into_iter();
        let len = stmts.len();
        stmts
            .enumerate()
            .map(|(i, expr)| {
                let expected = if i == len - 1 { expected } else { Some(unit_t) };
                self.expression(expr, expected)
            })
            .collect::<Result<Vec<_>>>()
            .map(|mut exprs| {
                let (last, ty) = exprs
                    .pop()
                    .unwrap_or_else(|| (self.et.construct_unit(self.tt), unit_t));
                (
                    self.et
                        .sequence(exprs.into_iter().map(|(expr, _)| expr), last),
                    ty,
                )
            })
    }
    // TODO: cache these ?
    fn function_param(&self, param: FunctionParameter) -> mu::Type {
        match param {
            FunctionParameter::Data(ty) => self.r#type(ty),
            FunctionParameter::Lambda(sig) => self
                .tt
                .insert_type(mu::TypeEnum::Function(self.function_type(sig, None))),
        }
    }
    fn function_type(
        &self,
        sig: FunctionSignature,
        decl: Option<&'a ast::FunctionDeclaration>,
    ) -> mu::FunctionType {
        let val = &self.lower.tt[sig];

        // TODO: support generics
        if val.type_params.as_ref().is_some_and(|ps| {
            ps.iter()
                .any(|&k| self.lower.tt[k].output != SimpleKind::Region)
        }) {
            todo!("error: no support for generics yet")
        }

        let effect_params = val
            .thunk
            .effect
            .effects(self.lower.tt)
            .filter_map(|e| self.effect(e));

        let params = val
            .params
            .iter()
            .flat_map(|params| params.iter().copied())
            .map(|param| match param {
                FunctionParameter::Data(ty) => self.r#type(ty),
                FunctionParameter::Lambda(sig) => self
                    .tt
                    .insert_type(mu::TypeEnum::Function(self.function_type(sig, None))),
            });
        let from = if let Some(decl) = decl {
            let name = decl.name.ident.as_str();
            self.tt.push_named_tuple(
                Iterator::zip(
                    decl.parameters
                        .iter()
                        .flat_map(|params| params.inner.iter())
                        .map(|param| param.name().as_str().to_compact_string()),
                    params,
                )
                .chain(effect_params.map(|(name, e)| (name.to_compact_string(), e))),
                name.into(),
            )
        } else {
            self.tt
                .insert_tuple(params.chain(effect_params.map(|(_, e)| e)))
        };

        let to = self.r#type(val.thunk.returns);

        mu::FunctionType::new(from, to, self.tt)
    }
    fn effect(&self, e: Effect) -> Option<(&'a str, mu::Type)> {
        match self.lower.tt[e] {
            EffectEnum::Generic(_) => todo!(),
            EffectEnum::Item(ref _item) => todo!(),
            EffectEnum::Read(_)
            | EffectEnum::Write(_)
            | EffectEnum::Divergent
            | EffectEnum::World => None,
            EffectEnum::Row(_) => panic!("ICE: trying to get type of effect ROW"),
        }
    }
    fn r#type(&self, ty: Type) -> mu::Type {
        match self.lower.tt[ty] {
            TypeEnum::Generic(_) => todo!(),
            TypeEnum::Item(ref _item) => todo!(),
            TypeEnum::Integer(integer) => self.tt.base(mu::Base::Integer(integer)),
            TypeEnum::Boolean => self.tt.bool(),
            TypeEnum::Unit => self.tt.unit(),
            TypeEnum::Never => self.tt.never(),
            TypeEnum::NullPointer => {
                // this MUST be an actual pointer, and not removed as a zero-sized type
                // so we do a pointer to u8
                // (technically any nonzero-sized type would work)
                self.tt.base(mu::Base::Pointer(self.tt.base(mu::Base::U8)))
            }
            TypeEnum::Pointer(ty, _) => self.tt.base(mu::Base::Pointer(self.r#type(ty))),
            TypeEnum::PointerSlice(ty, _, sentinel) => match sentinel {
                Some(_) => self.tt.base(mu::Base::MultiPointer(self.r#type(ty))),
                None => self.tt.base(mu::Base::PointerSlice(self.r#type(ty))),
            },
            TypeEnum::Array(ty, size, sentinel) => self.tt.base(mu::Base::Array(
                self.r#type(ty),
                self.array_size(size) + sentinel.is_some() as u32,
            )),
            TypeEnum::Maybe(ty) => self.tt.optional(self.r#type(ty)),
        }
    }
    fn array_size(&self, c: Constant) -> u32 {
        match self.lower.tt[c] {
            ConstantEnum::Generic(_) => todo!(),
            ConstantEnum::Integer(n) => n as u32,
            ConstantEnum::Zero => 0,
            _ => panic!("ICE: non-integer as array size"),
        }
    }
}
