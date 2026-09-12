use std::hash::{DefaultHasher, Hash, Hasher};
use std::iter;
use std::path::Path;
use std::sync::Arc;

use compact_str::{CompactString, ToCompactString, format_compact};
use do_notation::m;
use itertools::Either;

use crate::ast;
use crate::error::{ProblemKind, Problems, Result};
use crate::header::{EffectDecl, FunctionDefinition, IntrinsicFunction, ItemDecl, StructDecl};
use crate::module::Module;
use crate::mu::{self, Table as _};
use crate::pass::defs::Definitions;
use crate::pass::imports::Imports;
use crate::pass::lower::err::{MissingEffects, NotEnoughInfo, SignatureMismatch, TypeMismatch};
use crate::pass::lower::{HeaderQuery, Lower};
use crate::span::{HasSpan, Span};
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionSignature,
    FunctionSignatureValue, GenericArgument, IntSize, Integer, Item, Kind, RegionEnum, Sentinel,
    SimpleKind, Term, Thunk, Type, TypeEnum, TypeTable,
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

    table: &'a mu::table::Table,
    vars: im::Vector<Var<'a>>,
    markers: im::Vector<Effect>,

    path: Option<&'a Path>,
    source: &'a str,
    caller_location: Effect,
}

impl<'a, 'scope> MuLower<'a, 'scope> {
    fn reborrow<'short>(&'short mut self) -> MuLower<'a, 'short> {
        MuLower {
            lower: self.lower.reborrow(),

            table: self.table,
            vars: self.vars.clone(),
            markers: self.markers.clone(),

            path: self.path,
            source: self.source,
            caller_location: self.caller_location,
        }
    }
}

impl mu::Module {
    pub fn from(
        query: &impl HeaderQuery,
        module: &Module,
        path: Option<&Path>,
        source: &str,
        ast: &ast::Module,
        imports: &Imports,
        defs: &Definitions,
        tt: &TypeTable,
        table: &mu::table::Table,
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

            table,
            vars: im::Vector::new(),
            markers: im::Vector::new(),

            path,
            source,
            caller_location: tt.insert_effect(EffectEnum::Item(Item {
                module: Module::BUILTIN,
                name: CompactString::const_new("CallerLocation"),
                apply: None,
            })),
        };

        // global markers
        lower
            .markers
            .push_front(tt.insert_effect(EffectEnum::Read(tt.insert_region(RegionEnum::Static))));
        lower
            .markers
            .push_front(tt.insert_effect(EffectEnum::Read(tt.insert_region(RegionEnum::Heap))));
        lower
            .markers
            .push_front(tt.insert_effect(EffectEnum::Write(tt.insert_region(RegionEnum::Heap))));

        query
            .header(module, tt)
            .expect("ICE: could not query own header")
            .items()
            .filter_map(|(name, decl)| {
                // TODO: effect functions
                let &ItemDecl::Function(sig, None, node, FunctionDefinition::Other) = decl else {
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

#[derive(Clone, Copy)]
struct UseArg<'a> {
    params: Option<&'a ast::Separated<ast::LambdaParameter>>,
    block: &'a ast::Separated<Box<ast::Expression>>,
}

enum PathType {
    Data(Type),
    Function(FunctionSignature, Arc<[GenericArgument]>),
}

enum PathValue {
    Expression(mu::Expression),
    Intrinsic(IntrinsicFunction),
    EffectFunction(Effect, u32),
}

impl PathValue {
    fn unwrap_expression(self) -> mu::Expression {
        match self {
            PathValue::Expression(expression) => expression,
            _ => panic!(),
        }
    }
}

impl From<FunctionParameter> for PathType {
    fn from(value: FunctionParameter) -> Self {
        match value {
            FunctionParameter::Data(ty) => Self::Data(ty),
            FunctionParameter::Lambda(sig) => Self::Function(sig, Arc::new([])),
            FunctionParameter::Hole => panic!("ICE: function parameter hole"),
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
            ast::FunctionDefinition::Expression { body, inline } => {
                let ty = self.function_type(sig, Some(decl));
                self.abstraction(
                    sig,
                    decl.name.generics.as_ref(),
                    decl.parameters
                        .iter()
                        .flat_map(|params| params.inner.iter())
                        .map(|param| (param.name(), None)),
                    iter::once(&**body),
                )
                .map(|(lambda, _)| {
                    let mu::ExpressionEnum::Abstract(_, body) = self.table[lambda] else {
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
                        inline: inline.is_some(),
                    }
                })
            }
            ast::FunctionDefinition::Intrinsic(_) => todo!("error"),
        }
    }
    fn with_name<T>(
        &mut self,
        implicit_regions: usize,
        params: Option<&Arc<[Kind]>>,
        name: Option<&'a ast::GenericParameters>,
        inner: impl FnOnce(&mut MuLower<'a, '_>) -> T,
    ) -> T {
        let offset = implicit_regions + params.map_or(0, |kinds| kinds.len());
        if offset > 0 {
            self.lower
                .with_name(implicit_regions, params, name, |lower| {
                    let tt = lower.tt;
                    let mut mu = MuLower {
                        lower: lower.reborrow(),
                        table: self.table,
                        vars: self
                            .vars
                            .iter()
                            .map(|v| match v {
                                Var::Named(name, param) => {
                                    Var::Named(name, param.shift(tt, 0, offset))
                                }
                                Var::Effect(effect) => Var::Effect(effect.shift(tt, 0, offset)),
                                Var::Raise(ty) => Var::Raise(ty.shift(tt, 0, offset)),
                                Var::Unit => Var::Unit,
                            })
                            .collect(),
                        markers: self
                            .markers
                            .iter()
                            .map(|e| e.shift(tt, 0, offset))
                            .collect(),
                        path: self.path,
                        source: self.source,
                        caller_location: self.caller_location,
                    };
                    inner(&mut mu)
                })
        } else {
            let mut mu = self.reborrow();
            inner(&mut mu)
        }
    }
    fn abstraction(
        &mut self,
        sig: FunctionSignature,
        name: Option<&'a ast::GenericParameters>,
        params: impl IntoIterator<Item = (&'a ast::Identifier, Option<&'a ast::Type>)>,
        body: impl IntoIterator<IntoIter = impl ExactSizeIterator<Item = &'a ast::Expression>>,
    ) -> Result<(mu::Expression, Type)> {
        let sig_val = &self.lower.tt[sig];
        self.with_name(
            sig_val.implicit_regions,
            sig_val.type_params.as_ref(),
            name,
            |me| {
                let from = me.table.insert_tuple(Iterator::chain(
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
                me.statements(&mut body.into_iter().peekable(), sig_val.thunk.returns)
                    .map(|(expr, ty)| (self.table.lambda(from, expr), ty))
            },
        )
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
    fn check_marker_effect(&self, effect: Effect, at: &impl HasSpan) -> Problems {
        if self.has_marker_effect(effect) {
            Problems::ok()
        } else {
            ProblemKind::MissingEffects(MissingEffects(effect))
                .at(self.lower.module, at)
                .into()
        }
    }
    fn find_effect(&self, effect: Effect) -> Option<u32> {
        // TODO: global effect handlers
        // return either u32 index or some global handler
        self.vars
            .iter()
            .enumerate()
            .find_map(|(index, &var)| match var {
                Var::Effect(e) if e == effect || self.lower.tt[e] == EffectEnum::Hole => {
                    Some(index as u32)
                }
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
    fn path(&mut self, path: &'a ast::Path) -> Result<(PathValue, PathType)> {
        if let ast::PathOrigin::Local(local) = &path.origin
            && let Some((index, ty)) = self.find_named(local.as_str())
        {
            if let Some(_generics) = &path.generics {
                todo!("generic local function")
            }
            let mu_ty = self.function_param(ty);
            Result::new((
                PathValue::Expression(self.table.reference(mu_ty, index)),
                ty.into(),
            ))
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
                                let ty = match kind_enum.output {
                                    SimpleKind::Constant(ty) if kind_enum.params.is_none() => ty,
                                    _ => todo!("error"),
                                };
                                let Term::Constant(c) = term else {
                                    panic!("ICE: constant kind but not constant term")
                                };
                                Result::new((
                                    PathValue::Expression(self.constant(ty, c)),
                                    PathType::Data(ty),
                                ))
                            })
                    }),
                ItemDecl::Struct(_, _) => todo!("struct constructor"),
                ItemDecl::Effect(_, _) => todo!("error"),
                ItemDecl::Function(sig, effect, _, def) => {
                    let module = module.clone();
                    self.lower
                        .apply_sig(sig, effect, path.generics.as_ref())
                        .and_then(|(sig, effect, generics)| {
                            let ty = PathType::Function(sig, generics);
                            Result::new((
                                match effect {
                                    Some(e) => {
                                        let EffectEnum::Item(item) = &self.lower.tt[e] else {
                                            panic!("ICE: effect with body is not an item");
                                        };
                                        let effect_decl = self.effect_decl(item);
                                        let function_index = effect_decl
                                            .members
                                            .iter()
                                            .enumerate()
                                            .find(|(_, m)| m.name.as_str() == name)
                                            .expect("ICE: effect function not part of effect")
                                            .0;
                                        PathValue::EffectFunction(e, function_index as u32)
                                    }
                                    None => match def {
                                        FunctionDefinition::Intrinsic(i) => PathValue::Intrinsic(i),
                                        FunctionDefinition::Other => {
                                            let item = mu::Item {
                                                module,
                                                item: name.to_compact_string(),
                                            };
                                            let ty = self.function_type(sig, None);
                                            PathValue::Expression(self.table.operation(
                                                mu::Operation::Callable(
                                                    mu::Callable::ModuleFunction { item, ty },
                                                ),
                                            ))
                                        }
                                    },
                                },
                                ty,
                            ))
                        })
                }
            }
        }
    }
    fn caller_location_effect(&self, span: Span) -> mu::Expression {
        let ty = self
            .effect(self.caller_location)
            .expect("ICE: caller location effect has no type")
            .1;
        let mu::TypeEnum::VTable(tup) = self.table[ty] else {
            panic!("ICE: caller location effect is not a mu product type")
        };
        let mu::TypeEnum::Function(fun_ty) = self.table[self.table[tup][0]] else {
            panic!("ICE: caller location effect has no mu function type")
        };
        let mu::TypeEnum::Product(loc_tup) = self.table[fun_ty.to()] else {
            panic!("ICE: caller location effect function does not return a mu product")
        };

        let path = match self.path {
            Some(path) => path.to_string_lossy().to_compact_string(),
            None => self.lower.module.to_compact_string(),
        };
        let (line, column) = line_column::line_column(self.source, span.start as usize);

        self.table.construct_vtable(
            tup,
            [self.table.lambda(
                fun_ty.from(),
                self.table.construct(
                    loc_tup,
                    [
                        self.table
                            .constant(self.table[loc_tup][0], mu::Constant::String(path)),
                        self.table
                            .constant(self.table[loc_tup][1], mu::Constant::Integer(line as u64)),
                        self.table
                            .constant(self.table[loc_tup][2], mu::Constant::Integer(column as u64)),
                    ],
                ),
            )],
        )
    }
    fn lambda_signature(
        &mut self,
        type_params: Option<Arc<[Kind]>>,
        implicit_regions: usize,
        ast: Option<&'a ast::Separated<ast::LambdaParameter>>,
    ) -> Result<FunctionSignature> {
        let thunk = Thunk {
            returns: self.lower.tt.insert_type(TypeEnum::Hole),
            effect: self.lower.tt.insert_effect(EffectEnum::Hole),
        };
        match ast {
            Some(ast_params) => ast_params
                .iter()
                .map(|ast_param| match &ast_param.ty {
                    Some(ty) => self.lower.r#type(ty, true).map(FunctionParameter::Data),
                    None => Result::new(FunctionParameter::Hole),
                })
                .collect::<Result<_>>()
                .map(|params| {
                    self.lower
                        .tt
                        .insert_function_signature(FunctionSignatureValue {
                            type_params,
                            implicit_regions,
                            params: Some(params),
                            thunk,
                        })
                }),
            None => Result::new(
                self.lower
                    .tt
                    .insert_function_signature(FunctionSignatureValue {
                        type_params,
                        implicit_regions,
                        params: None,
                        thunk,
                    }),
            ),
        }
    }
    fn call(
        &mut self,
        call: Either<&'a ast::Call, &'a ast::Path>,
        use_arg: Option<UseArg<'a>>,
        expected: Type,
    ) -> Result<(mu::Expression, Type)> {
        // TODO: also put non-call paths under here?
        // TODO: a big clean up of this function
        let path = match call {
            Either::Left(call) => &call.fun,
            Either::Right(path) => path,
        };
        self.path(path).and_then(|(fun, fun_ty)| {
            let mut problems = Problems::ok();

            // function signature with partially applied generics
            let PathType::Function(sig, generics) = fun_ty else {
                todo!("error")
            };
            let sig_val = &self.lower.tt[sig];

            let implicit_arity = sig_val.arity()
                // add parent effect generics too
                + match fun {
                    PathValue::EffectFunction(effect, _) => {
                        let EffectEnum::Item(item) = &self.lower.tt[effect] else {
                            panic!("ICE: effect with body is not an item");
                        };
                        item.apply.as_deref().map_or(0, |args| args.len())
                    }
                    _ => 0,
                };
            let mut mono_args =
                iter::repeat_n(GenericArgument::Hole, implicit_arity).collect::<Box<_>>();

            // infer from expected type
            sig_val
                .thunk
                .returns
                .infer(expected, self.lower.tt, 0, &mut mono_args);

            // infer from lambda block types
            // TODO: also other lambda blocks plz
            if let Some(use_arg) = use_arg {
                let param = sig_val
                    .params
                    .as_ref()
                    .unwrap_or_else(|| todo!())
                    .last()
                    .copied()
                    .unwrap_or_else(|| todo!());
                if let FunctionParameter::Lambda(sig) = param {
                    let user_sig = problems.append(self.lambda_signature(
                        self.lower.tt[sig].type_params.clone(),
                        self.lower.tt[sig].implicit_regions,
                        use_arg.params,
                    ));

                    if let Some(user_sig) = user_sig {
                        sig.infer(user_sig, self.lower.tt, 0, &mut mono_args);
                    }
                }
            }

            let mut sig_mono = sig.apply(self.lower.tt, &mono_args);
            let mut sig_mono_val = &self.lower.tt[sig_mono];

            // get all arguments
            let (mut args, _params) = if let Some(sig_mono_params) = &sig_mono_val.params {
                let mut sig_mono_params = sig_mono_params;
                macro_rules! infer_step {
                    ($old:expr, $new:expr) => {
                        if implicit_arity > 0 {
                            let old_hash = {
                                let mut hasher = DefaultHasher::new();
                                mono_args.hash(&mut hasher);
                                hasher.finish()
                            };
                            ($old).infer($new, self.lower.tt, 0, &mut mono_args);
                            let new_hash = {
                                let mut hasher = DefaultHasher::new();
                                mono_args.hash(&mut hasher);
                                hasher.finish()
                            };
                            #[allow(unused_assignments)]
                            if old_hash != new_hash {
                                sig_mono = sig.apply(self.lower.tt, &mono_args);
                                sig_mono_val = &self.lower.tt[sig_mono];
                                sig_mono_params = sig_mono_val
                                    .params
                                    .as_ref()
                                    .expect("ICE: new inferred sig has no params");
                            }
                        }
                    };
                }

                if sig_mono_params.len()
                    != call.left().map_or(0, ast::Call::count_args) + use_arg.is_some() as usize
                {
                    problems +=
                        ProblemKind::Other(format_compact!("Incorrect number of arguments"))
                            .at(self.lower.module, path);
                    return problems.error();
                }
                let mut args = Vec::new();
                let mut params = Vec::new();
                for (param_index, (param, arg)) in Iterator::zip(
                    sig_val
                        .params
                        .as_ref()
                        .expect("ICE: sigval has no params but mono does")
                        .iter()
                        .copied(),
                    call.unwrap_left().args(),
                )
                .enumerate()
                {
                    // lower argument
                    let mono_param = sig_mono_params[param_index];
                    let (mu_arg, user_param) = match mono_param {
                        FunctionParameter::Data(ty) => problems
                            .append(
                                self.expression(arg, ty)
                                    .map(|(mu, ty)| (mu, FunctionParameter::Data(ty))),
                            )
                            .unwrap_or_else(|| {
                                (self.table.unreachable(), FunctionParameter::Data(ty))
                            }),
                        FunctionParameter::Lambda(sig) => {
                            let sig_val = &self.lower.tt[sig];
                            if sig_val.type_params.as_ref().is_some_and(|ps| {
                                ps.iter()
                                    .any(|&k| self.lower.tt[k].output != SimpleKind::Region)
                            }) {
                                todo!("error: no support for generics yet")
                            }
                            let e = if let ast::Expression::Block(block) = arg {
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
                                    None,
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
                                self.abstraction(sig, None, [], [arg])
                            };
                            (
                                problems
                                    .append(e)
                                    .map(|(lambda, _)| lambda)
                                    .unwrap_or_else(|| self.table.unreachable()),
                                {
                                    if sig.no_holes(self.lower.tt) {
                                        FunctionParameter::Lambda(sig)
                                    } else {
                                        problems += ProblemKind::Other(format_compact!(
                                            "holes in {}",
                                            sig.display(self.lower.tt)
                                        ))
                                        .at(self.lower.module, arg);
                                        FunctionParameter::Hole
                                    }
                                },
                            )
                        }
                        FunctionParameter::Hole => todo!(),
                    };
                    params.push(user_param);
                    args.push(mu_arg);

                    // infer more generics
                    infer_step!(param, user_param);
                }
                if let Some(arg) = use_arg {
                    let mono_param = sig_mono_params.last().copied().unwrap();
                    let FunctionParameter::Lambda(mono_sig) = mono_param else {
                        todo!("error")
                    };
                    let mono_sig_val = &self.lower.tt[mono_sig];
                    if mono_sig_val.type_params.as_ref().is_some_and(|ps| {
                        ps.iter()
                            .any(|&k| self.lower.tt[k].output != SimpleKind::Region)
                    }) {
                        todo!("error: no support for generics yet")
                    }
                    if arg.params.map(|params| params.elements.len())
                        != mono_sig_val.params.as_ref().map(|params| params.len())
                    {
                        todo!("error")
                    }

                    let mono_param = sig_mono_val
                        .params
                        .as_ref()
                        .unwrap()
                        .last()
                        .copied()
                        .unwrap();
                    let FunctionParameter::Lambda(mono_sig) = mono_param else {
                        panic!()
                    };

                    let (user_arg, user_returns) = problems
                        .append(
                            self.abstraction(
                                mono_sig,
                                None,
                                arg.params
                                    .into_iter()
                                    .flat_map(|lambda| lambda.iter())
                                    .map(|lambda| (&lambda.var, lambda.ty.as_deref())),
                                arg.block.iter().map(|e| &**e),
                            ),
                        )
                        .unwrap_or_else(|| {
                            (
                                self.table.unreachable(),
                                self.lower.tt.insert_type(TypeEnum::Hole),
                            )
                        });

                    // FIXME: hmmm we are doing this twice now
                    let param = sig_val.params.as_ref().unwrap().last().copied().unwrap();
                    let FunctionParameter::Lambda(sig) = param else {
                        panic!()
                    };
                    let mut user_sig = problems
                        .append(self.lambda_signature(
                            mono_sig_val.type_params.clone(),
                            mono_sig_val.implicit_regions,
                            arg.params,
                        ))
                        .unwrap_or_else(|| todo!());
                    let mut user_sig_val = self.lower.tt[user_sig].clone();
                    user_sig_val.thunk.returns = user_returns;
                    user_sig = self.lower.tt.insert_function_signature(user_sig_val);

                    infer_step!(sig, user_sig);

                    params.push(FunctionParameter::Lambda(user_sig));
                    args.push(user_arg);
                }
                (args, params)
            } else if call.left().is_some_and(|call| {
                call.args.is_some() || call.block.is_some() || use_arg.is_some()
            }) {
                todo!("error: function has no arguments")
            } else {
                (Vec::new(), Vec::new())
            };

            if !sig_mono.no_holes(self.lower.tt) {
                return problems.and_then(|()| {
                    Result::error(
                        ProblemKind::Other(format_compact!(
                            "ambiguous generics for {}",
                            sig_mono.display(self.lower.tt)
                        ))
                        .at(self.lower.module, path),
                    )
                });
            }
            // FIXME: check if args are subtypes of inferred params

            // effects
            let mut missing = Vec::new();
            for effect in sig_mono_val.thunk.effect.effects(self.lower.tt) {
                if effect.is_marker(self.lower.tt) {
                    if !self.has_marker_effect(effect) {
                        missing.push(effect);
                    }
                } else if let Some(idx) = self.find_effect(effect) {
                    let effect_ty = self
                        .effect(effect)
                        .expect("ICE: non-marker effect has no type")
                        .1;
                    args.push(self.table.reference(effect_ty, idx));
                } else if effect == self.caller_location {
                    args.push(self.caller_location_effect(match call {
                        Either::Left(call) => call.span(),
                        Either::Right(path) => path.span(),
                    }));
                } else {
                    missing.push(effect);
                }
            }
            let mut missing_check = |missing: Vec<Effect>| {
                if !missing.is_empty() {
                    problems += ProblemKind::MissingEffects(MissingEffects(
                        self.lower.tt.insert_effect(EffectEnum::Row(missing.into())),
                    ))
                    .at(self.lower.module, path);
                }
            };

            // call expression
            let mu = match fun {
                PathValue::Expression(fun) => {
                    missing_check(missing);
                    self.table.apply(fun, args)
                }
                PathValue::Intrinsic(i) => {
                    missing_check(missing);
                    let all_generics = mono_args
                        .into_iter()
                        .chain(generics.iter().copied())
                        .collect();
                    self.intrinsic(i, all_generics, args)
                }
                PathValue::EffectFunction(effect, function_index) => {
                    let EffectEnum::Item(item) = &self.lower.tt[effect] else {
                        panic!("ICE: effect with body is not an item");
                    };
                    let effect_args = mono_args
                        .into_iter()
                        .chain(generics.iter().copied())
                        .take(item.apply.as_deref().map_or(0, |args| args.len()))
                        .collect::<Arc<_>>();
                    let effect_mono = effect.subst(self.lower.tt, 0, &effect_args);
                    match self.find_effect(effect_mono) {
                        Some(idx) => {
                            missing_check(missing);
                            self.table.apply(
                                self.table.member(
                                    self.table
                                        .reference(self.effect(effect_mono).unwrap().1, idx),
                                    function_index,
                                ),
                                args,
                            )
                        }
                        None => {
                            missing.push(effect_mono);
                            missing_check(missing);
                            self.table.unreachable()
                        }
                    }
                }
            };
            problems.with((mu, sig_mono_val.thunk.returns))
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
                let Term::Type(ty) = generics[0].term() else {
                    panic!()
                };
                let Term::Type(to) = generics[1].term() else {
                    panic!()
                };
                let mut args = args.into_iter();
                let val = args.next().unwrap();
                let lambda = args.next().unwrap();
                let ty = self.r#type(ty);
                let to = self.r#type(to);
                self.table
                    .call(mu::Callable::LetReference { ty, to }, [val, lambda])
            }
            IntrinsicFunction::Alloca => {
                let Term::Type(ty) = generics[0].term() else {
                    panic!()
                };
                let Term::Type(to) = generics[1].term() else {
                    panic!()
                };
                let mut args = args.into_iter();
                let val = args.next().unwrap();
                let lambda = args.next().unwrap();
                let ty = self.r#type(ty);
                let to = self.r#type(to);
                self.table
                    .call(mu::Callable::LetAlloca { ty, to }, [val, lambda])
            }
            IntrinsicFunction::Link => {
                let Term::Constant(lib) = generics[0].term() else {
                    panic!()
                };
                let ConstantEnum::String(lib) = &self.lower.tt[lib] else {
                    panic!()
                };
                let Term::Effect(effect) = generics[1].term() else {
                    panic!()
                };
                let EffectEnum::Item(item) = &self.lower.tt[effect] else {
                    todo!("return error")
                };
                let effect_decl = self.effect_decl(item);

                let mu::ExpressionEnum::Abstract(_, body) =
                    self.table[args.into_iter().next().unwrap()]
                else {
                    panic!("ICE: link arg is not a function")
                };

                let effect_ty = self
                    .effect(effect)
                    .expect("ICE: effect with body with no type")
                    .1;
                let mu::TypeEnum::VTable(effect_tys) = self.table[effect_ty] else {
                    panic!("ICE: effect with body is not a product type");
                };

                self.table.let_chain(
                    [self.table.construct_vtable(
                        effect_tys,
                        effect_decl.members.iter().map(|member| {
                            if self.lower.tt[member.signature].params.is_none() {
                                // external value
                                let ty = self.lower.tt[member.signature].thunk.returns;
                                let TypeEnum::Pointer(ty, _) = self.lower.tt[ty] else {
                                    todo!("return error")
                                };
                                let ty = self.r#type(ty);
                                self.table.lambda(
                                    self.table.insert_tuple([]),
                                    self.table.operation(mu::Operation::ForeignGlobal {
                                        lib: lib.clone(),
                                        name: member.name.clone(),
                                        ty,
                                    }),
                                )
                            } else {
                                // external function
                                let ty = self.function_type(member.signature, None);
                                self.table.lambda(
                                    ty.from(),
                                    self.table.call(
                                        mu::Callable::ForeignFunction {
                                            lib: lib.clone(),
                                            name: member.name.clone(),
                                            ty,
                                        },
                                        self.table[ty.from()]
                                            .iter()
                                            .copied()
                                            .rev()
                                            .enumerate()
                                            .rev()
                                            .map(|(i, ty)| self.table.reference(ty, i as u32)),
                                    ),
                                )
                            }
                        }),
                    )],
                    body,
                )
            }
            IntrinsicFunction::Asm | IntrinsicFunction::AsmPure => {
                let Term::Constant(assembly) = generics[0].term() else {
                    panic!()
                };
                let ConstantEnum::String(assembly) = &self.lower.tt[assembly] else {
                    panic!()
                };
                let Term::Constant(constraints) = generics[1].term() else {
                    panic!()
                };
                let ConstantEnum::String(constraints) = &self.lower.tt[constraints] else {
                    panic!()
                };
                let Term::Type(from) = generics[2].term() else {
                    panic!()
                };
                let Term::Type(to) = generics[3].term() else {
                    panic!()
                };
                self.table.call(
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
            IntrinsicFunction::Len => {
                let Term::Type(ty) = generics[1].term() else {
                    panic!()
                };
                self.table.call(
                    mu::Callable::Len {
                        ty: self.r#type(ty),
                    },
                    args,
                )
            }
            IntrinsicFunction::Unreachable => self.table.operation(mu::Operation::Unreachable),
            IntrinsicFunction::Loop => {
                let mut args = args.into_iter();
                let body = args.next().unwrap();
                // let _div = args.next().unwrap();
                self.table.call(mu::Callable::Loop, [body])
            }
            IntrinsicFunction::Unfounded => {
                let mu::ExpressionEnum::Abstract(_, body) =
                    self.table[args.into_iter().next().unwrap()]
                else {
                    panic!("ICE: unfounded arg is not a function")
                };
                body
            }
            IntrinsicFunction::Trace => {
                let mut args = args.into_iter();
                let slice = args.next().unwrap();
                // let _read = args.next().unwrap();
                let mu_size = self.table.base(mu::Base::SIZE);
                let mu_addr = self.table.base(mu::Base::ADDR);
                let mu_i8 = self.table.base(mu::Base::I8);
                let mu_i8_ptr = self.table.base(mu::Base::Pointer(mu_i8));
                let mu_i8_slice = self.table.base(mu::Base::PointerSlice(mu_i8));
                self.table.let_chain(
                    [slice],
                    self.table.call(
                        mu::Callable::Syscall { args: 3 },
                        [
                            self.table.constant(mu_addr, mu::Constant::Integer(1)),
                            self.table.constant(mu_addr, mu::Constant::Integer(2)),
                            self.table.cast(
                                mu_i8_ptr,
                                mu_addr,
                                ast::Cast::Transmute,
                                self.table.call(
                                    mu::Callable::PointerSliceIndex { ty: mu_i8 },
                                    [
                                        self.table.reference(mu_i8_slice, 0),
                                        self.table.constant(mu_size, mu::Constant::Zero),
                                    ],
                                ),
                            ),
                            self.table.cast(
                                mu_size,
                                mu_addr,
                                ast::Cast::Extend,
                                self.table.call(
                                    mu::Callable::Len { ty: mu_i8 },
                                    [self.table.reference(mu_i8_slice, 0)],
                                ),
                            ),
                        ],
                    ),
                )
            }
            IntrinsicFunction::Trap => {
                let mu_addr = self.table.base(mu::Base::ADDR);
                self.table.sequence(
                    [self.table.call(
                        mu::Callable::Syscall { args: 1 },
                        [
                            self.table.constant(mu_addr, mu::Constant::Integer(60)),
                            self.table.constant(mu_addr, mu::Constant::Integer(1)),
                        ],
                    )],
                    self.table.unreachable(),
                )
            }
            IntrinsicFunction::SliceFromRawParts => {
                let Term::Type(ty) = generics[1].term() else {
                    panic!()
                };
                let ty = self.r#type(ty);
                let size = self.table.base(mu::Base::SIZE);

                let mut args = args.into_iter();
                let ptr = args.next().unwrap();
                let len = args.next().unwrap();

                self.table.call(
                    mu::Callable::MultiPointerSlice { ty },
                    [ptr, self.table.constant(size, mu::Constant::Zero), len],
                )
            }
            IntrinsicFunction::None => {
                let Term::Type(ty) = generics[0].term() else {
                    panic!()
                };
                let ty = self.r#type(ty);
                self.table.push_expression(mu::ExpressionEnum::Variant(
                    self.table.insert_enum([self.table.unit(), ty]),
                    0,
                    self.table.construct_unit(),
                ))
            }
            IntrinsicFunction::Some => {
                let Term::Type(ty) = generics[0].term() else {
                    panic!()
                };
                let ty = self.r#type(ty);
                self.table.push_expression(mu::ExpressionEnum::Variant(
                    self.table.insert_enum([self.table.unit(), ty]),
                    1,
                    args.into_iter().next().unwrap(),
                ))
            }
        }
    }
    fn constant(&self, ty: Type, c: Constant) -> mu::Expression {
        match self.lower.tt[c] {
            ConstantEnum::Generic(_) => todo!(),
            ConstantEnum::True => {
                let bool = self.table.bool();
                self.table.push_expression(mu::ExpressionEnum::Variant(
                    bool.into_sum(self.table).unwrap(),
                    1,
                    self.table.construct_unit(),
                ))
            }
            ConstantEnum::False => {
                let bool = self.table.bool();
                self.table.push_expression(mu::ExpressionEnum::Variant(
                    bool.into_sum(self.table).unwrap(),
                    0,
                    self.table.construct_unit(),
                ))
            }
            ConstantEnum::Integer(int) => self
                .table
                .constant(self.r#type(ty), mu::Constant::Integer(int)),
            ConstantEnum::String(ref str) => {
                // FIXME: if the type has a sentinel we need to add that to the end
                self.table
                    .constant(self.r#type(ty), mu::Constant::String(str.clone()))
            }
            ConstantEnum::Character(ref str) => {
                let TypeEnum::Integer(i) = self.lower.tt[ty] else {
                    panic!("ICE: character constant is not of integer type");
                };
                let mu_ty = self.table.base(mu::Base::Integer(i));
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
                self.table.constant(mu_ty, mu::Constant::Integer(value))
            }
            ConstantEnum::Zero => self.table.constant(self.r#type(ty), mu::Constant::Zero),
            ConstantEnum::Hole => self.table.unreachable(),
        }
    }
    fn handler_function(
        &mut self,
        sig: FunctionSignature,
        parent_module: &'a Module,
        parent_decl: Span,
        decl: &'a ast::FunctionDeclaration,
        def: &'a ast::FunctionDefinition,
    ) -> Result<mu::Expression> {
        self.lower
            .function_signature(decl)
            .and_then(|user_sig| {
                if !sig.subtype(user_sig, self.lower.tt) {
                    return Result::error(
                        ProblemKind::SignatureMismatch(SignatureMismatch {
                            defined_module: parent_module.clone(),
                            defined_span: parent_decl,
                        })
                        .at(self.lower.module, decl),
                    );
                }
                match def {
                    ast::FunctionDefinition::Expression { body, .. } => self.abstraction(
                        user_sig,
                        decl.name.generics.as_ref(),
                        decl.parameters
                            .iter()
                            .flat_map(|params| params.inner.iter())
                            .map(|param| (param.name(), None)),
                        [&**body],
                    ),
                    ast::FunctionDefinition::Intrinsic(_) => todo!("error"),
                }
            })
            .map(|(e, _)| e)
    }
    fn handler(
        &mut self,
        effect: Effect,
        ast: &'a ast::Separated<ast::Item>,
        error_pos: &'a ast::Path,
    ) -> Result<mu::Expression> {
        let EffectEnum::Item(item) = &self.lower.tt[effect] else {
            return Result::error(
                ProblemKind::Other(format_compact!(
                    "error: handler effect is not an item: {}",
                    effect.display(self.lower.tt)
                ))
                .at(self.lower.module, error_pos),
            );
        };
        let effect_decl = self.effect_decl(item);

        // TODO: error on not a function
        // TODO: error on no definition
        // TODO: error on too many functions
        // TODO: error on same name

        let effect_ty = self
            .effect(effect)
            .expect("ICE: effect with body with no type")
            .1;
        let mu::TypeEnum::VTable(effect_tys) = self.table[effect_ty] else {
            panic!("ICE: effect with body is not a product type");
        };

        let mut problems = Problems::ok();
        let constructed = self.table.construct_vtable(
            effect_tys,
            effect_decl.members.iter().map(|member| {
                let Some((decl, def)) = ast
                    .iter()
                    .filter_map(|i| match i {
                        ast::Item::Function(decl, Some((_, def))) => Some((decl, def)),
                        _ => None,
                    })
                    .find(|(decl, _)| decl.name.ident.as_str() == member.name.as_str())
                else {
                    problems += ProblemKind::Other(format_compact!(
                        "handler lacks member function '{}'",
                        member.name.as_str()
                    ))
                    .at(self.lower.module, error_pos);
                    return self.table.unreachable();
                };
                let args: &[GenericArgument] = item.apply.as_ref().map_or(&[], |args| &**args);
                let sig_val = self.lower.tt[member.signature].clone();
                let partial = self
                    .lower
                    .tt
                    .insert_function_signature(FunctionSignatureValue {
                        // TODO: if we have dependent kinds these need to be substituted too
                        type_params: sig_val
                            .type_params
                            .map(|params| params.iter().copied().skip(args.len()).collect()),
                        implicit_regions: sig_val.implicit_regions,
                        params: sig_val.params.subst(self.lower.tt, 0, args),
                        thunk: sig_val.thunk.subst(self.lower.tt, 0, args),
                    });
                problems
                    .append(self.handler_function(partial, &item.module, member.span, decl, def))
                    .unwrap_or_else(|| self.table.unreachable())
            }),
        );
        problems.with(constructed)
    }
    fn expression(
        &mut self,
        expr: &'a ast::Expression,
        expected: Type,
    ) -> Result<(mu::Expression, Type)> {
        let expr_outer = expr;
        match expr {
            ast::Expression::Let { .. } => {
                panic!("ICE: let expressions should be managed by MuLower::statements")
            }
            ast::Expression::Constant(constant) => self
                .lower
                .constant(constant, expected)
                .map(|(c, ty)| (self.constant(ty, c), ty)),
            ast::Expression::Uninit(_) => {
                // TODO: check if uninit is allowed for this type
                if !expected.no_holes(self.lower.tt) {
                    Result::error(
                        ProblemKind::NotEnoughInfo(NotEnoughInfo(Term::Type(expected)))
                            .at(self.lower.module, expr_outer),
                    )
                } else {
                    Result::new((
                        self.table
                            .constant(self.r#type(expected), mu::Constant::Uninit),
                        expected,
                    ))
                }
            }
            ast::Expression::Member { lhs, rhs, .. } => self
                .expression(lhs, self.lower.tt.insert_type(TypeEnum::Hole))
                .and_then(|(val, ty)| self.member_access(val, ty, rhs)),
            ast::Expression::Path(path) => {
                if let ast::PathOrigin::Package(lhs, _, rhs) = &path.origin
                    && let Some((index, ty)) = self.find_named(lhs.as_str())
                {
                    if let Some(_generics) = &path.generics {
                        todo!("error")
                    }
                    let FunctionParameter::Data(ty) = ty else {
                        todo!("evaluate 0-arity function")
                    };
                    // TODO: this does not include member access of local constant / function output right now
                    self.member_access(self.table.reference(self.r#type(ty), index), ty, rhs)
                } else {
                    self.path(path).and_then(|(e, p)| match p {
                        PathType::Data(ty) => Result::new((e.unwrap_expression(), ty)),
                        PathType::Function(_, _) => self.call(Either::Right(path), None, expected),
                    })
                }
            }
            ast::Expression::Block(block) => {
                if let Some(_params) = &block.inner.params {
                    todo!("error")
                }
                let stmts = block.inner.stmts.iter().map(|e| &**e);
                self.reborrow().statements(&mut stmts.peekable(), expected)
            }
            ast::Expression::Enclosed(expr) => self.expression(&expr.inner, expected),
            ast::Expression::Cast { op, expr, .. } => {
                if expected.no_holes(self.lower.tt) {
                    self.expression(expr, self.lower.tt.insert_type(TypeEnum::Hole))
                        .map(|(value, from)| {
                            (
                                self.table.cast(
                                    self.r#type(from),
                                    self.r#type(expected),
                                    *op,
                                    value,
                                ),
                                expected,
                            )
                        })
                } else {
                    Result::error(
                        ProblemKind::NotEnoughInfo(NotEnoughInfo(Term::Type(expected)))
                            .at(self.lower.module, expr_outer),
                    )
                }
            }
            ast::Expression::If {
                condition,
                branch_true,
                branch_false,
                ..
            } => self.if_expression(
                expected,
                condition,
                &branch_true.1,
                branch_false.as_ref().map(|(_, branch)| &**branch),
            ),
            ast::Expression::Discard { expr, .. } => self
                .expression(expr, self.lower.tt.insert_type(TypeEnum::Hole))
                .map(|(mu, _)| (mu, self.lower.tt.insert_type(TypeEnum::Unit))),
            ast::Expression::AssignOp(op, lhs, tk_op, rhs) => {
                let ast::Expression::Dereference { expr, tk_caret } = &**lhs else {
                    todo!("error")
                };
                self.expression(
                    expr,
                    self.lower.tt.insert_type(TypeEnum::Pointer(
                        self.lower.tt.insert_type(TypeEnum::Hole),
                        self.lower.tt.insert_region(RegionEnum::Hole),
                    )),
                )
                .and_then(|(lhs, ty)| {
                    let TypeEnum::Pointer(inner, region) = self.lower.tt[ty] else {
                        panic!("ICE: not a poiner :(")
                    };
                    self.expression(rhs, inner).and_then(|(rhs, _)| {
                        let mut problems = Problems::ok();
                        let mu_inner = self.r#type(inner);
                        let val = match op {
                            &ast::AssignOp::Math(op) => {
                                problems += self.check_marker_effect(
                                    self.lower.tt.insert_effect(EffectEnum::Read(region)),
                                    tk_caret,
                                );
                                self.table.call(
                                    mu::Callable::MathOp { ty: mu_inner, op },
                                    [
                                        self.table.call(mu::Callable::Read { ty: mu_inner }, [lhs]),
                                        rhs,
                                    ],
                                )
                            }
                            ast::AssignOp::Assign => rhs,
                        };
                        problems += self.check_marker_effect(
                            self.lower.tt.insert_effect(EffectEnum::Write(region)),
                            tk_op,
                        );
                        problems.with((
                            self.table
                                .call(mu::Callable::Write { ty: mu_inner }, [lhs, val]),
                            self.lower.tt.insert_type(TypeEnum::Unit),
                        ))
                    })
                })
            }
            ast::Expression::PredicateOp(op, lhs, _, rhs) => self
                .expression(lhs, self.lower.tt.insert_type(TypeEnum::Hole))
                .and_then(|(lhs, ty)| {
                    self.expression(rhs, ty).map(|(rhs, _)| {
                        (
                            self.table.call(
                                mu::Callable::PredicateOp {
                                    ty: self.r#type(ty),
                                    op: *op,
                                },
                                [lhs, rhs],
                            ),
                            self.lower.tt.insert_type(TypeEnum::Boolean),
                        )
                    })
                }),
            ast::Expression::MathOp(op, lhs, _, rhs) => {
                // TODO: check if type valid
                self.expression(lhs, expected).and_then(|(lhs, ty)| {
                    self.expression(rhs, ty).map(|(rhs, _)| {
                        (
                            self.table.call(
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
                // TODO: check if type valid
                self.expression(expr, expected).map(|(e, ty)| {
                    (
                        self.table.call(
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
            ast::Expression::Dereference { expr, tk_caret } => {
                let expected_inner = self.lower.tt.insert_type(TypeEnum::Pointer(
                    expected,
                    self.lower.tt.insert_region(RegionEnum::Hole),
                ));
                self.expression(expr, expected_inner).and_then(|(e, ty)| {
                    let TypeEnum::Pointer(inner, region) = self.lower.tt[ty] else {
                        panic!("ICE: not a poiner :(")
                    };
                    self.check_marker_effect(
                        self.lower.tt.insert_effect(EffectEnum::Read(region)),
                        tk_caret,
                    )
                    .with((
                        self.table.call(
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
                // NOTE: if T is not 0-able and array has sentinel, should indexing return ?T instead of T ..?
                self.expression(array, self.lower.tt.insert_type(TypeEnum::Hole))
                    .and_then(|(array, ty)| {
                        match (&self.lower.tt[ty], &index.inner) {
                            // ^[]T
                            (
                                &TypeEnum::PointerSlice(ty, region, sentinel_ty),
                                ast::Index::Single(expr),
                            ) => self
                                .expression(expr, self.lower.tt.insert_type(TypeEnum::SIZE))
                                .map(|(index, _)| match sentinel_ty {
                                    Some(_) => (
                                        self.table.call(
                                            mu::Callable::MultiPointerIndex {
                                                ty: self.r#type(ty),
                                            },
                                            [array, index],
                                        ),
                                        self.lower.tt.insert_type(TypeEnum::Pointer(ty, region)),
                                    ),
                                    None => (
                                        self.table.call(
                                            mu::Callable::PointerSliceIndex {
                                                ty: self.r#type(ty),
                                            },
                                            [array, index],
                                        ),
                                        self.lower.tt.insert_type(TypeEnum::Pointer(ty, region)),
                                    ),
                                }),
                            (
                                &TypeEnum::PointerSlice(ty, region, sentinel_ty),
                                ast::Index::Range {
                                    from, to, sentinel, ..
                                },
                            ) => {
                                // FIXME: sentinel
                                let usize_t = self.lower.tt.insert_type(TypeEnum::SIZE);
                                let mu_usize = self.r#type(usize_t);
                                let mu_ty = self.r#type(ty);
                                let from_index = from
                                    .as_ref()
                                    .map(|expr| {
                                        self.expression(expr, usize_t).map(|(expr, _)| expr)
                                    })
                                    .unwrap_or_else(|| {
                                        Result::new(
                                            self.table.constant(mu_usize, mu::Constant::Zero),
                                        )
                                    });
                                if let Some(Sentinel) = sentinel_ty
                                    && to.is_none()
                                {
                                    from_index.map(|from_index| {
                                        (
                                            self.table.call(
                                                mu::Callable::MultiPointerOffset { ty: mu_ty },
                                                [array, from_index],
                                            ),
                                            self.lower.tt.insert_type(TypeEnum::PointerSlice(
                                                ty,
                                                region,
                                                sentinel_ty,
                                            )),
                                        )
                                    })
                                } else {
                                    let to_index = to
                                        .as_ref()
                                        .map(|expr| {
                                            self.expression(expr, usize_t).map(|(expr, _)| expr)
                                        })
                                        .unwrap_or_else(|| {
                                            Result::new(
                                                self.table
                                                    .call(mu::Callable::Len { ty: mu_ty }, [array]),
                                            )
                                        });
                                    from_index.and_then(|from_index| {
                                        to_index.map(|to_index| {
                                            (
                                                self.table.call(
                                                    sentinel_ty.map_or_else(
                                                        || mu::Callable::PointerSliceSlice {
                                                            ty: mu_ty,
                                                        },
                                                        |_| mu::Callable::MultiPointerSlice {
                                                            ty: mu_ty,
                                                        },
                                                    ),
                                                    [array, from_index, to_index],
                                                ),
                                                self.lower.tt.insert_type(TypeEnum::PointerSlice(
                                                    ty, region, None,
                                                )),
                                            )
                                        })
                                    })
                                }
                            }

                            // [N]T
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

                            // ^[N]T
                            (&TypeEnum::Pointer(pointee, region), ast::Index::Single(expr))
                                if let TypeEnum::Array(ty, size, sentinel_ty) =
                                    self.lower.tt[pointee] =>
                            {
                                self.expression(expr, self.lower.tt.insert_type(TypeEnum::SIZE))
                                    .map(|(index, _)| {
                                        let size =
                                            self.array_size(size) + sentinel_ty.is_some() as u32;
                                        (
                                            self.table.call(
                                                mu::Callable::PointerArrayIndex {
                                                    ty: self.r#type(ty),
                                                    size,
                                                },
                                                [array, index],
                                            ),
                                            self.lower
                                                .tt
                                                .insert_type(TypeEnum::Pointer(ty, region)),
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
                                // FIXME: sentinel
                                let max = self.array_size(size);
                                let size = max + sentinel_ty.is_some() as u32;
                                let usize_t = self.lower.tt.insert_type(TypeEnum::SIZE);
                                let mu_usize = self.r#type(usize_t);
                                let from_index = from
                                    .as_ref()
                                    .map(|expr| {
                                        self.expression(expr, usize_t).map(|(expr, _)| expr)
                                    })
                                    .unwrap_or_else(|| {
                                        Result::new(
                                            self.table.constant(mu_usize, mu::Constant::Zero),
                                        )
                                    });
                                let to_index =
                                    to.as_ref()
                                        .map(|expr| {
                                            self.expression(expr, usize_t).map(|(expr, _)| expr)
                                        })
                                        .unwrap_or_else(|| {
                                            Result::new(self.table.constant(
                                                mu_usize,
                                                mu::Constant::Integer(max as u64),
                                            ))
                                        });
                                from_index.and_then(|from_index| {
                                    to_index.map(|to_index| {
                                        (
                                            self.table.call(
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

                            // ???
                            (_, _) => Result::error(
                                ProblemKind::Other(format_compact!(
                                    "indexing {}",
                                    ty.display(self.lower.tt)
                                ))
                                .at(self.lower.module, expr_outer),
                            ),
                        }
                    })
            }
            ast::Expression::Array(exprs) => {
                // TODO: we can infer stuff, we don't need to check for holes here
                if expected.no_holes(self.lower.tt) {
                    match self.lower.tt[expected] {
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
                            let et = self.table;
                            let args = exprs.inner.iter().map(|elem| {
                                problems
                                    .append(self.expression(elem, inner))
                                    .map_or_else(|| self.table.unreachable(), |(e, _)| e)
                            });
                            let construct =
                                et.call(mu::Callable::ArrayConstruct { ty: mu_inner, size }, args);
                            problems.with((construct, expected))
                        }
                        _ => todo!("error"),
                    }
                } else {
                    Result::error(
                        ProblemKind::NotEnoughInfo(NotEnoughInfo(Term::Type(expected)))
                            .at(self.lower.module, expr_outer),
                    )
                }
            }
            ast::Expression::Call(call) => self.call(Either::Left(call), None, expected),
            ast::Expression::Use {
                params,
                call,
                block,
                ..
            } => self.call(
                Either::Left(call),
                Some(UseArg {
                    params: params.as_ref().map(|(_, params, _)| params),
                    block,
                }),
                expected,
            ),
            ast::Expression::Handle { expr, handlers, .. } => {
                // TODO: OnceLock on Var::Raise so we don't have to already know it here
                if expected.no_holes(self.lower.tt) {
                    let mut self_inner = self.reborrow();
                    self_inner.vars.push_front(Var::Raise(expected));

                    if let Some((_, handlers)) = handlers {
                        let [(handler, _)] = handlers.elements.as_slice() else {
                            todo!("error: not yet supported")
                        };
                        self_inner.lower.effect(&handler.effect).and_then(|effect| {
                            self_inner
                                .handler(effect, &handler.items.inner, &handler.effect)
                                .and_then(|effect_mu| {
                                    self_inner.vars.push_front(Var::Effect(effect));
                                    self_inner.expression(expr, expected).map(|(e, t)| {
                                        (self_inner.table.let_chain([effect_mu], e), t)
                                    })
                                })
                        })
                    } else {
                        self_inner.expression(expr, expected)
                    }
                    .map(|(e, _)| {
                        (
                            self_inner.table.try_break(self_inner.r#type(expected), e),
                            expected,
                        )
                    })
                } else {
                    Result::error(
                        ProblemKind::NotEnoughInfo(NotEnoughInfo(Term::Type(expected)))
                            .at(self.lower.module, expr_outer),
                    )
                }
            }
            ast::Expression::Raise { expr, .. } => {
                let never = self.lower.tt.insert_type(TypeEnum::Never);
                let Some((index, ty)) = self.find_raise() else {
                    todo!("error")
                };
                let f = self.table.reference(
                    self.table.function(
                        self.table.insert_tuple([self.r#type(ty)]),
                        self.table.never(),
                    ),
                    index,
                );
                match expr {
                    Some(expr) => self
                        .expression(expr, ty)
                        .map(|(e, _)| (self.table.apply(f, [e]), never)),
                    None if ty.is_unit(self.lower.tt) => {
                        Result::new((self.table.apply(f, [self.table.construct_unit()]), never))
                    }
                    None => {
                        todo!("error: expected {}", ty.display(self.lower.tt));
                    }
                }
            }
        }
        .and_then(|(mu, found)| {
            if !found.subtype(expected, self.lower.tt) {
                ProblemKind::TypeMismatch(TypeMismatch { expected, found })
                    .at(self.lower.module, expr)
                    .with((mu, expected))
            } else {
                Result::new((mu, found))
            }
        })
        .recover_with(|| (self.table.unreachable(), expected))
    }
    fn if_expression(
        &mut self,
        expected: Type,
        condition: &'a ast::Expression,
        branch_true: &'a ast::Expression,
        branch_false: Option<&'a ast::Expression>,
    ) -> Result<(mu::Expression, Type)> {
        if let ast::Expression::Block(block) = branch_true
            && let Some(params) = &block.inner.params
        {
            let [(param, _)] = params.0.elements.as_slice() else {
                todo!("error")
            };
            // TODO: use param type

            // maybe unwrap
            self.expression(
                condition,
                self.lower
                    .tt
                    .insert_type(TypeEnum::Maybe(self.lower.tt.insert_type(TypeEnum::Hole))),
            )
            .and_then(|(maybe_mu, maybe_ty)| {
                let TypeEnum::Maybe(ty) = self.lower.tt[maybe_ty] else {
                    panic!("ICE: not a maybe :(")
                };
                let mut self_inner = self.reborrow();
                self_inner
                    .vars
                    .push_front(Var::Named(param.var.as_str(), FunctionParameter::Data(ty)));
                self_inner
                    .statements(
                        &mut block.inner.stmts.iter().map(|e| &**e).peekable(),
                        expected,
                    )
                    .recover_with(|| (self_inner.table.unreachable(), expected))
                    .and_then(|(then_branch, ty)| {
                        let unit_t = self_inner.lower.tt.insert_type(TypeEnum::Unit);
                        match branch_false {
                            Some(branch_false) => {
                                self_inner
                                    .expression(branch_false, ty)
                                    .map(|(else_branch, _)| {
                                        (
                                            self_inner
                                                .table
                                                .r#match(maybe_mu, [else_branch, then_branch]),
                                            ty,
                                        )
                                    })
                            }
                            None if !ty.subtype(unit_t, self_inner.lower.tt) => {
                                ProblemKind::TypeMismatch(TypeMismatch {
                                    expected: unit_t,
                                    found: ty,
                                })
                                .at(self_inner.lower.module, branch_true)
                                .with((self_inner.table.unreachable(), unit_t))
                            }
                            None => Result::new((
                                self_inner.table.r#match(
                                    maybe_mu,
                                    [self_inner.table.construct_unit(), then_branch],
                                ),
                                ty,
                            )),
                        }
                    })
            })
        } else {
            // boolean condition
            self.expression(condition, self.lower.tt.insert_type(TypeEnum::Boolean))
                .and_then(|(condition, _)| {
                    // this is a match expression under the hood
                    // so we need to push the unit bool variant on the var stack
                    let mut self_inner = self.reborrow();
                    self_inner.vars.push_front(Var::Unit);
                    self_inner
                        .expression(branch_true, expected)
                        .and_then(|(then_branch, ty)| {
                            let unit_t = self_inner.lower.tt.insert_type(TypeEnum::Unit);
                            match branch_false {
                                Some(branch_false) => self_inner.expression(branch_false, ty).map(
                                    |(else_branch, _)| {
                                        (
                                            self_inner.table.if_else(
                                                condition,
                                                then_branch,
                                                else_branch,
                                            ),
                                            ty,
                                        )
                                    },
                                ),
                                None if !ty.subtype(unit_t, self_inner.lower.tt) => {
                                    ProblemKind::TypeMismatch(TypeMismatch {
                                        expected: unit_t,
                                        found: ty,
                                    })
                                    .at(self_inner.lower.module, branch_true)
                                    .with((self_inner.table.unreachable(), unit_t))
                                }
                                None => Result::new((
                                    self_inner.table.if_stmt(condition, then_branch),
                                    ty,
                                )),
                            }
                        })
                })
        }
    }
    fn member_access(
        &mut self,
        lhs: mu::Expression,
        ty: Type,
        rhs: &ast::Identifier,
    ) -> Result<(mu::Expression, Type)> {
        if let TypeEnum::Pointer(inner, region) = self.lower.tt[ty] {
            let TypeEnum::Item(item) = &self.lower.tt[inner] else {
                todo!("error")
            };
            let decl = self.struct_decl(item);
            let mu_ty = self.r#type(inner);
            let mu::TypeEnum::Product(mu_tys) = self.table[mu_ty] else {
                panic!("ICE: item does not have product type");
            };
            let Some((idx, member)) = decl
                .members
                .iter()
                .enumerate()
                .find(|(_, m)| m.name.as_str() == rhs.as_str())
            else {
                todo!("error")
            };
            Result::new((
                self.table.call(
                    mu::Callable::PointerMember {
                        tys: mu_tys,
                        member: idx as u32,
                    },
                    [lhs],
                ),
                self.lower
                    .tt
                    .insert_type(TypeEnum::Pointer(member.ty, region)),
            ))
        } else {
            let TypeEnum::Item(item) = &self.lower.tt[ty] else {
                todo!("error")
            };
            let decl = self.struct_decl(item);
            let Some((idx, member)) = decl
                .members
                .iter()
                .enumerate()
                .find(|(_, m)| m.name.as_str() == rhs.as_str())
            else {
                todo!("error")
            };
            Result::new((self.table.member(lhs, idx as u32), member.ty))
        }
    }
    fn statements(
        &mut self,
        stmts: &mut iter::Peekable<impl Iterator<Item = &'a ast::Expression>>,
        expected: Type,
    ) -> Result<(mu::Expression, Type)> {
        let unit_t = self.lower.tt.insert_type(TypeEnum::Unit);

        let mut problems = Problems::ok();
        let mut exprs = Vec::new();
        while let Some(next) = stmts.next() {
            let expr = problems.append(if let ast::Expression::Let { var, ty, value, .. } = next {
                let self_ = &mut *self;
                let stmts_ = &mut *stmts;
                m! {
                    ty <- ty.as_ref().map_or_else(|| Result::new(self_.lower.tt.insert_type(TypeEnum::Hole)), |ty| self_.lower.r#type(ty, true));
                    outer <- self_.expression(value, ty);
                    inner <- {
                        let mut self_inner = self_.reborrow();
                        self_inner.vars.push_front(Var::Named(var.as_str(), FunctionParameter::Data(outer.1)));
                        self_inner.statements(stmts_, expected)
                    };
                    return (
                        self_.table.push_expression(mu::ExpressionEnum::Let(outer.0, inner.0)),
                        inner.1,
                    );
                }
            } else {
                let expected = if stmts.peek().is_some() {
                    unit_t
                } else {
                    expected
                };
                self.expression(next, expected)
            });
            if let Some(e) = expr {
                exprs.push(e);
            }
        }

        let (last, ty) = exprs
            .pop()
            .unwrap_or_else(|| (self.table.construct_unit(), unit_t));
        problems.with((
            self.table
                .sequence(exprs.into_iter().map(|(expr, _)| expr), last),
            ty,
        ))
    }
    // TODO: cache these ?
    fn function_param(&self, param: FunctionParameter) -> mu::Type {
        match param {
            FunctionParameter::Data(ty) => self.r#type(ty),
            FunctionParameter::Lambda(sig) => self
                .table
                .insert_type(mu::TypeEnum::Function(self.function_type(sig, None))),
            FunctionParameter::Hole => self.table.never(),
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
            .map(|param| self.function_param(param));
        let from = if let Some(decl) = decl {
            let name = decl.name.ident.as_str();
            self.table.push_named_tuple(
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
            self.table
                .insert_tuple(params.chain(effect_params.map(|(_, e)| e)))
        };

        let to = self.r#type(val.thunk.returns);

        mu::FunctionType::new(from, to, self.table)
    }
    fn effect(&self, e: Effect) -> Option<(&'a str, mu::Type)> {
        match self.lower.tt[e] {
            EffectEnum::Generic(_) => todo!(),
            EffectEnum::Item(ref item) => {
                // TODO: make these named, and cache results
                let name = item.name.as_str();
                let decl = self.effect_decl(item);
                let args: &[GenericArgument] = item.apply.as_ref().map_or(&[], |args| &**args);
                let members = decl.members.iter().map(|member| {
                    let sig_val = self.lower.tt[member.signature].clone();
                    let partial = self
                        .lower
                        .tt
                        .insert_function_signature(FunctionSignatureValue {
                            // TODO: if we have dependent kinds these need to be substituted too
                            type_params: sig_val
                                .type_params
                                .map(|params| params.iter().copied().skip(args.len()).collect()),
                            implicit_regions: sig_val.implicit_regions,
                            params: sig_val.params.subst(self.lower.tt, 0, args),
                            thunk: sig_val.thunk.subst(self.lower.tt, 0, args),
                        });
                    self.table
                        .insert_type(mu::TypeEnum::Function(self.function_type(partial, None)))
                });
                Some((
                    name,
                    self.table
                        .insert_type(mu::TypeEnum::VTable(self.table.insert_tuple(members))),
                ))
            }
            EffectEnum::Read(_)
            | EffectEnum::Write(_)
            | EffectEnum::Divergent
            | EffectEnum::World
            | EffectEnum::Hole => None,
            EffectEnum::Row(_) => panic!("ICE: trying to get type of effect ROW"),
        }
    }
    fn r#type(&self, ty: Type) -> mu::Type {
        match self.lower.tt[ty] {
            TypeEnum::Generic(_) => self.table.never(),
            TypeEnum::Item(ref item) => {
                // TODO: make these named, and cache results
                let decl = self.struct_decl(item);
                let args: &[GenericArgument] = item.apply.as_ref().map_or(&[], |args| &**args);
                let members = decl
                    .members
                    .iter()
                    .map(|member| self.r#type(member.ty.subst(self.lower.tt, 0, args)));
                self.table
                    .insert_type(mu::TypeEnum::Product(self.table.insert_tuple(members)))
            }
            TypeEnum::Integer(integer) => self.table.base(mu::Base::Integer(integer)),
            TypeEnum::Boolean => self.table.bool(),
            TypeEnum::Unit => self.table.unit(),
            TypeEnum::Never => self.table.never(),
            TypeEnum::NullPointer => {
                // this MUST be an actual pointer, and not removed as a zero-sized type
                // so we do a pointer to i8
                // (technically any nonzero-sized type would work)
                self.table
                    .base(mu::Base::Pointer(self.table.base(mu::Base::I8)))
            }
            TypeEnum::Pointer(ty, _) => self.table.base(mu::Base::Pointer(self.r#type(ty))),
            TypeEnum::PointerSlice(ty, _, sentinel) => match sentinel {
                Some(_) => self.table.base(mu::Base::MultiPointer(self.r#type(ty))),
                None => self.table.base(mu::Base::PointerSlice(self.r#type(ty))),
            },
            TypeEnum::Array(ty, size, sentinel) => self.table.base(mu::Base::Array(
                self.r#type(ty),
                self.array_size(size) + sentinel.is_some() as u32,
            )),
            TypeEnum::Maybe(ty) => self.table.optional(self.r#type(ty)),
            TypeEnum::Hole => self.table.never(),
        }
    }
    fn struct_decl(&self, item: &Item) -> &'scope StructDecl {
        let header = self
            .lower
            .query
            .header(&item.module, self.lower.tt)
            .expect("ICE: cannot get header of item module");
        let Some(ItemDecl::Struct(_, decl)) = header.get(&item.name) else {
            panic!("ICE: type item does not have struct item decl")
        };
        decl.get().expect("ICE: struct decl is uninitialized")
    }
    fn effect_decl(&self, item: &Item) -> &'scope EffectDecl {
        let header = self
            .lower
            .query
            .header(&item.module, self.lower.tt)
            .expect("ICE: cannot get header of item module");
        let Some(ItemDecl::Effect(_, decl)) = header.get(&item.name) else {
            panic!("ICE: effect item does not have effect item decl")
        };
        decl.get().expect("ICE: effect decl is uninitialized")
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
