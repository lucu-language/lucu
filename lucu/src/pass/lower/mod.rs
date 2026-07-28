use std::iter;
use std::sync::Arc;

use compact_str::ToCompactString;
use do_notation::m;

use crate::ast;
use crate::ast::visit::{Ast, Visitor};
use crate::error::{Problems, Result};
use crate::header::{
    Header, ItemDecl,
};
use crate::module::Module;
use crate::pass::imports::Imports;
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionSignature, FunctionSignatureValue, GenericArgument, GenericParameter, Item, Kind, KindEnum, Region, RegionEnum, Sentinel, SimpleKind, Term, Thunk, Type, TypeEnum, TypeTable,
};

mod header;
mod function;

struct Lower<'a, 'scope> {
    tt: &'a TypeTable,
    module: &'a Module,
    imports: &'a Imports,

    query: &'scope dyn HeaderQuery,
    generics: im::HashMap<&'a str, (usize, Kind)>,
    used_underscore: &'scope mut bool,

    next_implicit_region: Option<usize>,
    implicit_region_offset: usize,
    implicit_effects: Option<&'scope mut Vec<Effect>>,
}

impl<'a, 'scope> Lower<'a, 'scope> {
    fn reborrow<'short>(&'short mut self) -> Lower<'a, 'short> {
        Lower {
            tt: self.tt,
            module: self.module,
            imports: self.imports,
            query: self.query,

            generics: self.generics.clone(),
            used_underscore: self.used_underscore,

            next_implicit_region: self.next_implicit_region,
            implicit_region_offset: 0,
            implicit_effects: self.implicit_effects.as_deref_mut(),
        }
    }
}

pub trait HeaderQuery {
    fn header(&self, module: &Module, tt: &TypeTable) -> Option<&Header>;
}

impl<'a, 'b> Lower<'a, 'b> {
    fn with_arity<T>(&mut self, kinds: &[Kind], inner: impl FnOnce(&mut Lower<'a, '_>) -> T) -> T {
        let mut lower = self.reborrow();
        if !kinds.is_empty() {
            lower.generics = lower.generics.into_iter().map(|(ident, (index, kind))| (ident, (index + kinds.len(), kind))).collect();
            lower.generics.remove("_");
            lower.implicit_region_offset += kinds.len();
        }

        let mut used_underscore = false;
        if kinds.len() == 1 {
            lower.generics.insert("_", (0, kinds[0]));
            lower.used_underscore = &mut used_underscore;
        }

        inner(&mut lower)
    }
    fn with_generics<T>(&mut self, implicit_regions: usize, generics: impl ExactSizeIterator<Item = (&'a str, Kind)>, inner: impl FnOnce(&mut Lower<'a, '_>) -> T) -> T {
        let len = generics.len();
        let arity = implicit_regions + len;
        let mut lower = self.reborrow();
        if arity > 0 {
            lower.generics = lower.generics.into_iter().map(|(ident, (index, kind))| (ident, (index + arity, kind))).collect();
            lower.generics.remove("_");
        }
        for (index, (ident, kind)) in generics.enumerate() {
            // generics have *reversed* indices
            lower.generics.insert(ident, (len - (index + 1), kind));
        }
        inner(&mut lower)
    }
    fn with_name<T>(&mut self, implicit_regions: usize, params: Option<&Arc<[Kind]>>, name: Option<&'a ast::GenericParameters>, inner: impl FnOnce(&mut Lower<'a, '_>) -> T) -> T {
        match (params, name) {
            (Some(params), Some(generics)) => {
                assert_eq!(params.len(), generics.inner.elements.len());
                self.with_generics(
                    implicit_regions,
                    Iterator::zip(generics.inner.iter(), params.iter())
                        .map(|(ast, &kind)| (ast.ident().as_str(), kind)),
                     inner,
                 )
            }
            (None, None) => {
                let mut lower = self.reborrow();
                if implicit_regions > 0 {
                    lower.generics = lower.generics.into_iter().map(|(ident, (index, kind))| (ident, (index + implicit_regions, kind))).collect();
                    lower.generics.remove("_");
                    
                }
                inner(&mut lower)
            },
            _ => unreachable!(),
        }
    }

    fn get_generic(&self, ident: &str) -> Option<(usize, Kind)> {
        self.generics.get(ident).copied()
    }
    fn get_underscore(&mut self) -> Option<(usize, Kind)> {
        self.get_generic("_").inspect(|_| {
            *self.used_underscore = true;
        })
    }
    fn used_underscore(&self) -> bool {
        *self.used_underscore
    }

    fn next_implicit_region(&mut self) -> Option<(usize, usize)> {
        self.next_implicit_region.as_mut().map(|regions| {
            *regions -= 1;
            (*regions, *regions + self.implicit_region_offset)
        })
    }

    fn item_ref<'ast>(
        &self,
        path: &'ast ast::Path,
    ) -> std::result::Result<(&Module, &'ast str, &ItemDecl), Problems> {
        let (module, preamble, name) = match &path.origin {
            ast::PathOrigin::Package(pkg, _, name) => match self.imports.get(pkg.as_str()) {
                Some(module) => match self.query.header(module, self.tt) {
                    Some(ir) => ((module, ir), None, name.as_str()),
                    None => todo!("recover"),
                },
                None => todo!("error"),
            },
            ast::PathOrigin::Local(name) => (
                (self.module, self.query.header(self.module, self.tt).expect("ICE: cannot get own header")),
                self.imports
                    .preamble()
                    .and_then(|module| self.query.header(module, self.tt).map(|ir| (module, ir))),
                name.as_str(),
            ),
            ast::PathOrigin::Underscore(_) => todo!("error"),
        };

        for (module, ir) in iter::once(module).chain(preamble) {
            if let Some(item) = ir.get(name) {
                return Ok((module, name, item));
            }
        }

        todo!(
            "error: unknown {}, searched in {:?} and {:?}",
            name,
            module.0,
            preamble.map(|t| t.0)
        )
    }
    fn apply_sig(&mut self, sig: FunctionSignature, effect: Option<Effect>, ast: Option<&ast::GenericArguments>) -> Result<(FunctionSignature, Option<Effect>, Arc<[GenericArgument]>)> {
        match ast {
            Some(ast) => {
                let sig_val = self.tt[sig].clone();
                let Some(params) = &sig_val.type_params else {
                    todo!("error");
                };
                if params.len() != ast.inner.elements.len() {
                    todo!("error");
                }
                Iterator::zip(params.iter().copied(), ast.inner.iter())
                    .map(|(param, arg)| {
                        self.generic_argument(param, arg)
                    })
                    .collect::<Result<Arc<_>>>()
                    .map(|args| (self.tt.insert_function_signature(FunctionSignatureValue {
                        type_params: None,
                        implicit_regions: sig_val.implicit_regions,
                        params: sig_val.params.subst(self.tt, 0, &args),
                        thunk: sig_val.thunk.subst(self.tt, 0, &args),
                    }), effect.map(|e| {
                        let EffectEnum::Item(i) = &self.tt[e] else { panic!("ICE: function's parent effect is not an item") };
                        let effect_arg_count = i.apply.as_ref().map(|args| args.len()).unwrap_or(0);
                        e.subst(self.tt, 0, &args[0..effect_arg_count])
                    }), args))
            },
            None => Result::new((sig, effect, Arc::new([]))),
        }
    }
    fn apply(
        &mut self,
        kind: Kind,
        term: Term,
        ast: Option<&ast::GenericArguments>,
    ) -> Result<(Kind, Term)> {
        match ast {
            Some(ast) => {
                let kind = self.tt[kind].clone();
                let Some(params) = kind.params else {
                    todo!("error");
                };
                if params.len() != ast.inner.elements.len() {
                    todo!("error");
                }

                let output = self.tt.insert_kind(KindEnum {
                    params: None,
                    output: kind.output,
                });
                Iterator::zip(params.iter().copied(), ast.inner.iter())
                    .map(|(param, arg)| {
                        self.generic_argument(param, arg)
                    })
                    .collect::<Result<Arc<_>>>()
                    .map(|args| (output, term.subst(self.tt, 0, &args)))
            }
            None => Result::new((kind, term)),
        }
    }
    fn dummy_args(&mut self, kind: Kind) -> Option<Arc<[GenericArgument]>> {
        self.tt[kind].params.clone().map(|params| {
            params
                .iter()
                .copied()
                // generics have *reversed* indices
                .rev()
                .enumerate()
                .rev()
                .map(|(i, kind)| {
                    let apply = self.dummy_args(kind);
                    let arity = apply.as_ref().map(|params| params.len());
                    let param = GenericParameter {
                        index: i + arity.unwrap_or(0),
                        apply,
                    };
                    let term = match self.tt[kind].output {
                        SimpleKind::Type => {
                            Term::Type(self.tt.insert_type(TypeEnum::Generic(param)))
                        }
                        SimpleKind::Effect => {
                            Term::Effect(self.tt.insert_effect(EffectEnum::Generic(param)))
                        }
                        SimpleKind::Region => {
                            Term::Region(self.tt.insert_region(RegionEnum::Generic(param)))
                        }
                        SimpleKind::Thunk => Term::Thunk(Thunk {
                            returns: self.tt.insert_type(TypeEnum::Generic(param.clone())),
                            effect: self.tt.insert_effect(EffectEnum::Generic(param)),
                        }),
                        SimpleKind::Constant(_) => todo!(),
                    };
                    GenericArgument::Instance { term, arity }
                })
                .collect()
        })
    }
    fn term_path(
        &mut self,
        path: &ast::Path,
    ) -> Result<(Kind, Term)> {
        let (item_kind, term) = {
            if let ast::PathOrigin::Underscore(_) = path.origin {
                if let Some((index, kind)) = self.get_underscore() {
                    (kind, self.generic_parameter(index, kind))
                } else {
                    todo!("error")
                }
            } else if let ast::PathOrigin::Local(name) = &path.origin
                && let Some((index, kind)) = self.get_generic(name.as_str())
            {
                (kind, self.generic_parameter(index, kind))
            } else {
                // Module Item
                let (module, name, item) = match self.item_ref(path) {
                    Ok((module, name, item)) => (module, name, item),
                    Err(problems) => return problems.with(todo!("recovery value")),
                };
                match *item {
                    ItemDecl::Alias(item_kind, term) => (item_kind, term),
                    ItemDecl::Struct(item_kind, _) => {
                        let module = module.clone();
                        let generics = self.dummy_args(item_kind);
                        let base = self.tt.insert_type(TypeEnum::Item(Item {
                            module,
                            name: name.to_compact_string(),
                            apply: generics,
                        }));
                        (item_kind, Term::Type(base))
                    }
                    ItemDecl::Effect(item_kind, _) => {
                        let module = module.clone();
                        let generics = self.dummy_args(item_kind);
                        let base = self.tt.insert_effect(EffectEnum::Item(Item {
                            module,
                            name: name.to_compact_string(),
                            apply: generics,
                        }));
                        (item_kind, Term::Effect(base))
                    }
                    ItemDecl::Function(_, _, _) => todo!("error"),
                }
            }
        };

        self.apply(item_kind, term, path.generics.as_ref())
    }
    fn generic_parameter(&mut self, index: usize, kind: Kind) -> Term {
        let apply = self.dummy_args(kind);
        let arity = apply.as_ref().map(|params| params.len());
        let param = GenericParameter {
            index: index + arity.unwrap_or(0),
            apply,
        };
        match self.tt[kind].output {
            SimpleKind::Type => Term::Type(self.tt.insert_type(TypeEnum::Generic(param))),
            SimpleKind::Effect => Term::Effect(self.tt.insert_effect(EffectEnum::Generic(param))),
            SimpleKind::Region => Term::Region(self.tt.insert_region(RegionEnum::Generic(param))),
            SimpleKind::Thunk => Term::Thunk(Thunk {
                returns: self.tt.insert_type(TypeEnum::Generic(param.clone())),
                effect: self.tt.insert_effect(EffectEnum::Generic(param)),
            }),
            SimpleKind::Constant(_) => {
                Term::Constant(self.tt.insert_constant(ConstantEnum::Generic(param)))
            }
        }
    }
    fn generic_argument(
        &mut self,
        param: Kind,
        arg: &ast::GenericArgument,
    ) -> Result<GenericArgument> {
        let kinds = self.tt[param].params.as_deref().unwrap_or_default();
        let arity = self.tt[param].params.as_ref().map(|kinds| kinds.len());
        self.with_arity(kinds, |l| {
             // TODO: this could be refactored to be smaller, *surely*
            match arg {
                ast::GenericArgument::Path(path, effects) => match effects {
                    Some(effects) => {
                        let l2 = &mut *l;
                        m! {
                            thunk <- l2
                                .term_path(path)
                                .and_then(|(kind, term)| {
                                    match term {
                                        Term::Type(returns) if l2.tt[kind].params.is_none() =>
                                            Result::new(Thunk {
                                                returns,
                                                effect: Effect::empty(l2.tt)
                                            }),
                                        Term::Thunk(thunk) if l2.tt[kind].params.is_none() =>
                                            Result::new(thunk),
                                        _ => todo!("error"),
                                    }
                                });
                            effects <- effects.effects
                                .iter()
                                .map(|effect| l2.effect(effect))
                                .collect::<Result<Box<_>>>();
                            let effect = Effect::row(iter::once(&thunk.effect).chain(&effects), l2.tt);
                            return Term::Thunk(Thunk {
                                returns: thunk.returns,
                                effect,
                            });
                        }.and_then(|term| {
                            let expected = if arity == Some(1) && l.used_underscore() {
                                l.tt.insert_kind(KindEnum {
                                    params: None,
                                    output: l.tt[param].output,
                                })
                            } else {
                                param
                            };

                            if l.tt[expected] == KindEnum::THUNK {
                                Result::new(term)
                            } else {
                                todo!("error")
                            }
                        })
                    }
                    None => l
                        .term_path(path)
                        .and_then(|(kind, term)| {
                            let expected = if arity == Some(1) && l.used_underscore() {
                                l.tt.insert_kind(KindEnum {
                                    params: None,
                                    output: l.tt[param].output,
                                })
                            } else {
                                param
                            };

                            if kind == expected {
                                Result::new(term)
                            } else if let Term::Type(ty) = term
                                && l.tt[expected].params == l.tt[kind].params
                                && l.tt[expected].output == SimpleKind::Thunk
                            {
                                Result::new(Term::Thunk(Thunk {
                                    returns: ty,
                                    effect: Effect::empty(l.tt),
                                }))
                            } else if let Term::Effect(effect) = term
                                && l.tt[expected].params == l.tt[kind].params
                                && l.tt[expected].output == SimpleKind::Thunk
                            {
                                Result::new(Term::Thunk(Thunk {
                                    returns: l.tt.insert_type(TypeEnum::Unit),
                                    effect,
                                }))
                            } else {
                                todo!(
                                    "error: found '{}' expected '{}'",
                                    kind.display(l.tt),
                                    expected.display(l.tt)
                                )
                            }
                        }),
                },
                ast::GenericArgument::Type(ty, effects) => {
                    l.r#type(ty, false).and_then(|ty| {
                        // FIXME: we didn't lower the effects yet
                        let expected = if arity == Some(1) && l.used_underscore() {
                            l.tt.insert_kind(KindEnum {
                                params: None,
                                output: l.tt[param].output,
                            })
                        } else {
                            param
                        };
                        if l.tt[expected] == KindEnum::TYPE && effects.is_none() {
                            Result::new(Term::Type(ty))
                        } else if l.tt[expected] == KindEnum::THUNK {
                            m! {
                                effects <- effects
                                    .iter()
                                    .flat_map(|we| &we.effects)
                                    .map(|effect| l.effect(effect))
                                    .collect::<Result<Box<_>>>();
                                let effect = Effect::row(&effects, l.tt);
                                return Term::Thunk(Thunk {
                                    returns: ty,
                                    effect,
                                });
                            }
                        } else {
                            todo!("error")
                        }
                    })
                }
                ast::GenericArgument::Constant(constant) => {
                    // TODO: if we have dependent kinds then we also need to subst `ty` here
                    let SimpleKind::Constant(ty) = l.tt[param].output else {
                        todo!("error")
                    };
                    l.constant(constant, Some(ty)).and_then(|(constant, _)| {
                        let expected = if arity == Some(1) && l.used_underscore() {
                            l.tt.insert_kind(KindEnum {
                                params: None,
                                output: l.tt[param].output,
                            })
                        } else {
                            param
                        };
                        if l.tt[expected] == KindEnum::constant(ty) {
                            Result::new(Term::Constant(constant))
                        } else {
                            todo!("error")
                        }
                    })
                },
            }
            .map(|term| GenericArgument::Instance { term, arity })           
        })

    }
    fn region(
        &mut self,
        region: &ast::Path,
    ) -> Result<Region> {
        self.term_path(region)
            .and_then(|(kind, path)| match path {
                Term::Region(region) if self.tt[kind].params.is_none() => Result::new(region),
                _ => todo!("error"),
            })
    }
    fn effect(
        &mut self,
        effect: &ast::Path,
    ) -> Result<Effect> {
        self.term_path(effect)
            .and_then(|(kind, path)| match path {
                Term::Effect(effect) if self.tt[kind].params.is_none() => Result::new(effect),
                _ => todo!("error"),
            })
    }
    fn count_implicit_regions(&mut self, ast: &impl Ast) -> usize {
        #[derive(Clone, Copy)]
        struct ImplicitRegions;
        impl Visitor for ImplicitRegions {
            type Output<'a> = usize;
            fn visit_type(self, ty: &ast::Type) -> Self::Output<'_> {
                (match ty {
                    ast::Type::Pointer(_, None, _)
                    | ast::Type::Pointer(_, Some(ast::PointerRegion::Kind(_)), _) => 1,
                    _ => 0,
                }) + self.visit(ty)
            }
            fn visit_kind(self, _: &ast::Kind) -> Self::Output<'_> {
                // do not go inside kinds
                0
            }
            fn visit_function_declaration(self, _: &ast::FunctionDeclaration) -> Self::Output<'_> {
                // do not go inside function declarations
                0
            }
        }
        ast.visit(ImplicitRegions)
    }
    fn pointer_region(
        &mut self,
        ty: Option<&ast::PointerRegion>,
        allow_holes: bool
    ) -> Result<Region> {
        let kind = match ty {
            Some(ast::PointerRegion::At(_, path)) => return self.region(path),
            Some(ast::PointerRegion::Kind(kind)) => Some(kind),
            None => None,
        };

        let Some(next) = self.next_implicit_region() else {
            if allow_holes {
                return Result::new(self.tt.insert_region(RegionEnum::Hole));
            } else {
                todo!("error")
            }
        };

        self.implicit_region(kind, next)
    }
    fn implicit_region(
        &mut self,
        kind: Option<&ast::RegionKind>,
        index: (usize, usize),
    ) -> Result<Region> {

        let region = self
            .tt
            .insert_region(RegionEnum::Generic(GenericParameter { index: index.0, apply: None }));
        match kind {
            Some(ast::RegionKind::Mutable(_)) => {
                if let Some(effects) = self.implicit_effects.as_deref_mut() {
                    effects.push(self.tt.insert_effect(EffectEnum::Read(region)));
                    effects.push(self.tt.insert_effect(EffectEnum::Write(region)));
                } else {
                    todo!("error")
                }
            }
            None => {
                if let Some(effects) = self.implicit_effects.as_deref_mut() {
                    effects.push(self.tt.insert_effect(EffectEnum::Read(region)));
                }
            }
        }
        Result::new(self
            .tt
            .insert_region(RegionEnum::Generic(GenericParameter { index: index.1, apply: None })))
    }
    fn r#type(
        &mut self,
        ty: &ast::Type,
        allow_holes: bool,
    ) -> Result<Type> {
        match ty {
            ast::Type::Path(path) => {
                self.term_path(path)
                    .and_then(|(kind, path)| match path {
                        Term::Type(ty) if self.tt[kind].params.is_none() => Result::new(ty),
                        _ => todo!("error"),
                    })
            }
            ast::Type::Maybe(_, inner) => {
                self.r#type(inner, allow_holes).map(|ty| self.tt.insert_type(TypeEnum::Maybe(ty)))
            }
            ast::Type::Pointer(_, region, ty) => {
                if let ast::Type::Array(props, inner) = &**ty
                    && props.inner.size.is_none()
                {
                    // pointer to slice
                    m! {
                        let sentinel = props.inner.sentinel.is_some().then_some(Sentinel);
                        region <- self.pointer_region(region.as_ref(), allow_holes);
                        ty <- self.r#type(inner, allow_holes);
                        return self.tt.insert_type(TypeEnum::PointerSlice(ty, region, sentinel));
                    }
                } else {
                    // regular pointer
                    m! {
                        region <- self.pointer_region(region.as_ref(), allow_holes);
                        ty <- self.r#type(ty, allow_holes);
                        return self.tt.insert_type(TypeEnum::Pointer(ty, region));
                    }
                }
            }
            ast::Type::Array(props, ty) => {
                let Some(size) = &props.inner.size else {
                    todo!("error: naked slice")
                };

                let usize_ty = self.tt.insert_type(TypeEnum::SIZE);
                m! {
                    size <- self.constant(size, Some(usize_ty));
                    let sentinel = props.inner.sentinel.is_some().then_some(Sentinel);
                    ty <- self.r#type(ty, allow_holes);
                    return self.tt.insert_type(TypeEnum::Array(ty, size.0, sentinel));
                }
            }
        }
    }
    fn constant(
        &mut self,
        constant: &ast::Constant,
        expected: Option<Type>,
    ) -> Result<(Constant, Type)> {
        match constant {
            ast::Constant::Path(path) => {
                self.term_path(path)
                    .and_then(|(kind, term)| match (self.tt[kind].params.as_ref(), self.tt[kind].output, term) {
                        (None, SimpleKind::Constant(ty), Term::Constant(c)) => {
                            if let Some(e) = expected && ty.subtype(e, self.tt) {
                                Result::new((c, ty))
                            } else {
                                todo!("error")
                            }
                        },
                        _ => todo!("error"),
                    })
            }
            ast::Constant::Integer(integer) => {
                let ty = match expected {
                    Some(ty) if matches!(self.tt[ty], TypeEnum::Integer(_)) => ty,
                    Some(ty) if matches!(self.tt[ty], TypeEnum::Hole) => self.tt.insert_type(TypeEnum::INT),
                    None => self.tt.insert_type(TypeEnum::INT),
                    _ => todo!("error")
                };
                Result::new(
                    (self.tt
                        .insert_constant(ConstantEnum::Integer(integer.value)), ty),
                )
            },
            // TODO: escaping!
            ast::Constant::String(string) => {
                let ty = match expected {
                    Some(ty) if let TypeEnum::PointerSlice(inner, _, sentinel) = self.tt[ty] && inner.is_i8(self.tt) =>
                        self.tt.insert_type(TypeEnum::PointerSlice(inner, self.tt.insert_region(RegionEnum::Static), sentinel)),
                    Some(ty) if matches!(self.tt[ty], TypeEnum::Hole) =>
                        self.tt.insert_type(TypeEnum::PointerSlice(self.tt.insert_type(TypeEnum::I8), self.tt.insert_region(RegionEnum::Static), None)),
                    None =>
                        self.tt.insert_type(TypeEnum::PointerSlice(self.tt.insert_type(TypeEnum::I8), self.tt.insert_region(RegionEnum::Static), None)),
                    Some(ty) => todo!("error: string for {}", ty.display(self.tt)),
                };
                Result::new(
                    (self.tt
                        .insert_constant(ConstantEnum::String(string.value.clone())), ty),
                )
            },
            ast::Constant::Character(character) => {
                let ty = match expected {
                    Some(ty) if matches!(self.tt[ty], TypeEnum::Integer(_)) => ty,
                    Some(ty) if matches!(self.tt[ty], TypeEnum::Hole) => self.tt.insert_type(TypeEnum::I8),
                    None => self.tt.insert_type(TypeEnum::I8),
                    _ => todo!("error")
                };
                Result::new(
                    (self.tt
                        .insert_constant(ConstantEnum::Character(character.value.clone())), ty),
                )
            },
            // TODO: check if zeroable
            ast::Constant::Zero(_) => {
                let Some(ty) = expected else {
                    todo!("error")
                };
                if !ty.no_holes(self.tt) {
                    todo!("error")
                }
                Result::new((self.tt.insert_constant(ConstantEnum::Zero), ty))
            },
        }
    }
    fn simple_kind(&mut self, kind: &ast::Kind) -> Result<SimpleKind> {
        match kind {
            ast::Kind::Type(_) => Result::new(SimpleKind::Type),
            ast::Kind::Effect(_) => Result::new(SimpleKind::Effect),
            ast::Kind::Region(_) => Result::new(SimpleKind::Region),
            ast::Kind::Thunk(_) => Result::new(SimpleKind::Thunk),
            ast::Kind::Constant(ty) => {
                // TODO: allow constant with generic type?
                let mut l = self.reborrow();
                l.generics = im::HashMap::new();
                l.next_implicit_region = None;
                l.implicit_effects = None;
                l
                    .r#type(ty, false)
                    .map(SimpleKind::Constant)
            },
        }
    }
    fn kind_params(
        &mut self,
        name: Option<&ast::GenericParameters>,
    ) -> Result<Option<Arc<[Kind]>>> {
        match name {
            Some(params) => params
                .inner
                .iter()
                .rev()
                .enumerate()
                .rev()
                .map(|(index, param)| {
                    match param {
                        ast::GenericParameter::Type(_) => Result::new(SimpleKind::Type),
                        ast::GenericParameter::Region(kind, _) => {
                            self.implicit_region(
                                kind.as_ref(),
                                (index, index),
                            ).map(|_| SimpleKind::Region)
                        }
                        ast::GenericParameter::Other(_, kind) => self.simple_kind(kind),
                    }
                    .and_then(|output| self.kind(param.generics(), output))
                })
                .collect::<Result<_>>()
                .map(Some),
            None => Result::new(None),
        }
    }
    fn kind(
        &mut self,
        name: Option<&ast::GenericParameters>,
        output: SimpleKind,
    ) -> Result<Kind> {
        self.kind_params(name)
            .map(|params| self.tt.insert_kind(KindEnum { params, output }))
    }
    fn function_signature(
        &mut self,
        sig: &'a ast::FunctionDeclaration,
    ) -> Result<FunctionSignature> {
        let mut l = self.reborrow();
        let mut implicit_effects = Vec::new();
        l.implicit_effects = Some(&mut implicit_effects);
        l.kind_params(sig.name.generics.as_ref()).and_then(|type_params| {
            let implicit_regions = l.count_implicit_regions(sig);
            l.next_implicit_region = Some(implicit_regions + type_params.as_ref().map(|params| params.len()).unwrap_or(0));
            l.implicit_region_offset = 0;

            l.with_name(implicit_regions, type_params.clone().as_ref(), sig.name.generics.as_ref(), |l| m! {
                params <- match &sig.parameters {
                    Some(params) => params.inner
                        .iter()
                        .map(|param| l.function_param(param))
                        .collect::<Result<_>>()
                        .map(Some),
                    None => Result::new(None),
                };
                thunk <- l.thunk(sig.returns.as_ref());
                effects <- sig
                    .effects
                    .iter()
                    .flat_map(|we| &we.effects)
                    .map(|effect| l.effect(effect))
                    .collect::<Result<Box<_>>>();
                let effect = Effect::row(iter::once(&thunk.effect).chain(&effects).chain(l.implicit_effects.as_ref().map(|v| &***v).unwrap_or_default()), l.tt);
                return l.tt.insert_function_signature(FunctionSignatureValue {
                    type_params,
                    implicit_regions,
                    params,
                    thunk: Thunk {
                        returns: thunk.returns,
                        effect,
                    }
                });
            })
        })
    }
    fn thunk(
        &mut self,
        returns: Option<&ast::Returns>,
    ) -> Result<Thunk> {
        match returns {
            Some(returns) => match returns {
                ast::Returns::Path(path) => {
                    self.term_path(path)
                        .and_then(|(kind, term)| match term {
                            Term::Type(ty) if self.tt[kind].params.is_none() => {
                                Result::new(Thunk {
                                    returns: ty,
                                    effect: Effect::empty(self.tt),
                                })
                            }
                            Term::Effect(effect) if self.tt[kind].params.is_none() => {
                                Result::new(Thunk {
                                    returns: self.tt.insert_type(TypeEnum::Unit),
                                    effect,
                                })
                            }
                            Term::Thunk(thunk) if self.tt[kind].params.is_none() => {
                                Result::new(thunk)
                            }
                            _ => todo!("error"),
                        })
                }
                ast::Returns::Type(ty) => self.r#type(ty, false).map(|ty| Thunk {
                    returns: ty,
                    effect: Effect::empty(self.tt),
                }),
                ast::Returns::Never(_) => Result::new(Thunk {
                    returns: self.tt.insert_type(TypeEnum::Never),
                    effect: Effect::empty(self.tt),
                }),
            },
            None => Result::new(Thunk {
                returns: self.tt.insert_type(TypeEnum::Unit),
                effect: Effect::empty(self.tt),
            }),
        }
    }
    fn function_param(
        &mut self,
        param: &'a ast::Parameter,
    ) -> Result<FunctionParameter> {
        match param {
            ast::Parameter::Data(_, ty) => self
                .r#type(ty, false)
                .map(FunctionParameter::Data),
            ast::Parameter::Lambda(decl) => self
                .function_signature(decl)
                .map(FunctionParameter::Lambda),
        }
    }
}
