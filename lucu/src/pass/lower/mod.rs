use std::iter;
use std::sync::{Arc, OnceLock};

use compact_str::ToCompactString;
use do_notation::m;

use crate::ast;
use crate::ast::visit::{Ast, Visitor};
use crate::error::{Problems, Result};
use crate::header::{
    EffectDecl, EffectMember, HandlerDecl, Header, ItemDecl, StructDecl, StructMember,
};
use crate::module::Module;
use crate::pass::defs::Definitions;
use crate::pass::imports::Imports;
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionSignature,
    FunctionSignatureValue, GenericArgument, GenericParameter, IntSize, Integer, Item, Kind,
    KindEnum, Region, RegionEnum, Sentinel, SimpleKind, Term, Thunk, Type, TypeEnum, TypeTable,
};

struct Lower<'a> {
    tt: &'a TypeTable,
    module: &'a Module,

    ast: &'a ast::Module,
    imports: &'a Imports,
    definitions: &'a Definitions,

    query: &'a dyn HeaderQuery,
    header: Header,
}

pub trait HeaderQuery {
    fn header(&self, module: &Module) -> Option<&Header>;
}

#[derive(Clone, Default)]
struct Generics<'a>(im::HashMap<&'a str, (usize, Kind)>);

impl<'a> Generics<'a> {
    pub fn new() -> Self {
        Generics::default()
    }
    pub fn shifted(&self, arity: usize) -> Self {
        Self(
            self.0
                .iter()
                .map(|(&ident, &(index, kind))| (ident, (index + arity, kind)))
                .collect(),
        )
    }
    pub fn pushed(&self, generics: impl ExactSizeIterator<Item = (&'a str, Kind)>) -> Self {
        let len = generics.len();
        let mut shifted = self.shifted(len);
        for (index, (ident, kind)) in generics.enumerate() {
            // generics have *reversed* indices
            shifted.0.insert(ident, (len - (index + 1), kind));
        }
        shifted
    }
    pub fn get(&self, ident: &str) -> Option<(usize, Kind)> {
        self.0.get(ident).copied()
    }
}

#[derive(Default)]
struct Implicit {
    generics: usize,
    effects: Vec<Effect>,
}

impl Implicit {
    const fn new(generics: usize) -> Self {
        Self {
            generics,
            effects: Vec::new(),
        }
    }
}

impl Header {
    pub fn from(
        query: &impl HeaderQuery,
        module: &Module,
        ast: &ast::Module,
        imports: &Imports,
        definitions: &Definitions,
        tt: &TypeTable,
    ) -> Option<Result<Self>> {
        let lower = Lower {
            tt,
            module,
            ast,
            imports,
            definitions,
            query,
            header: Header::default(),
        };
        Some(lower.module())
    }
}

impl<'a> Lower<'a> {
    fn module(mut self) -> Result<Header> {
        let mut pass1_problems = Problems::ok();
        let defs = pass1_problems
            .append(
                self.definitions
                    .nodes_postorder()
                    .map(|node| self.definitions.item_with_parent(node, self.ast))
                    .map(|(def, parent)| self.pass1(def, parent))
                    .collect::<Result<Vec<_>>>(),
            )
            .expect("ICE: no definition list");
        assert_eq!(
            defs.len(),
            self.definitions.nodes().len(),
            "ICE: definition list has different size"
        );
        let pass2_problems = Iterator::zip(
            self.definitions
                .nodes_postorder()
                .map(|node| self.definitions.item(node, self.ast)),
            defs,
        )
        .map(|(def, lower)| self.pass2(def, lower))
        .collect::<Problems>();
        (pass1_problems + pass2_problems).with(self.header)
    }
    fn generics(
        &self,
        params: Option<&Arc<[Kind]>>,
        name: Option<&'a ast::GenericParameters>,
        base: &Generics<'a>,
    ) -> Generics<'a> {
        match (params, name) {
            (Some(params), Some(generics)) => {
                assert_eq!(params.len(), generics.inner.elements.len());
                base.pushed(
                    Iterator::zip(generics.inner.iter(), params.iter())
                        .map(|(ast, &kind)| (ast.ident().as_str(), kind)),
                )
            }
            (None, None) => base.clone(),
            _ => unreachable!(),
        }
    }
    fn pass2(&mut self, item: &'a ast::Item, partial: Option<ItemDecl>) -> Problems {
        let mut problems = Problems::ok();

        match item {
            ast::Item::Type(_, name, def) => {
                if let Some((_, ast::TypeDefinition::Struct(struc))) = def {
                    let Some(ItemDecl::Struct(kind, idx)) = partial else {
                        return problems;
                    };

                    let generics = self.generics(
                        self.tt[kind].params.as_ref(),
                        name.generics.as_ref(),
                        &Generics::new(),
                    );
                    let members = problems
                        .append(
                            struc
                                .members
                                .inner
                                .iter()
                                .map(|member| self.struct_member(member, &generics))
                                .collect::<Result<_>>(),
                        )
                        .expect("ICE: empty result when getting struct members");
                    idx.set(StructDecl { members })
                        .expect("ICE: struct already defined");
                }
            }
            ast::Item::Effect(_, _, defs) => {
                if let Some((_, ast::EffectDefinition::Body(body))) = defs {
                    let Some(ItemDecl::Effect(_, eff)) = partial else {
                        return problems;
                    };

                    let members = body
                        .items
                        .inner
                        .iter()
                        .filter_map(|def| {
                            // TODO: is there a way to get this without looking it up again?
                            let name = def.name()?;
                            let &ItemDecl::Function(sig, _) =
                                self.header.get(name.ident.as_str())?
                            else {
                                return None;
                            };
                            Some(EffectMember {
                                name: name.ident.as_str().to_compact_string(),
                                signature: sig,
                            })
                        })
                        .collect();
                    eff.set(EffectDecl { members })
                        .expect("ICE: effect already defined");
                }
            }
            ast::Item::Function(_, _) => {}
            ast::Item::Constant(_, _, _, _) => {}
            ast::Item::Handle(_, _, _) => {}
        }

        problems
    }
    fn pass1(
        &mut self,
        item: &'a ast::Item,
        parent: Option<&'a ast::Item>,
    ) -> Result<Option<ItemDecl>> {
        let mut problems = Problems::ok();

        match item {
            ast::Item::Type(_, name, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind =
                    problems.append(self.kind(name.generics.as_ref(), SimpleKind::Type, None));

                match def {
                    Some((_, ast::TypeDefinition::Type(ast))) => {
                        if let Some(kind) = kind {
                            let generics = self.generics(
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                &Generics::new(),
                            );
                            let ty = problems.append(self.r#type(ast, &generics, None));
                            if let Some(ty) = ty {
                                let item = ItemDecl::Alias(kind, Term::Type(ty));
                                self.header.insert(name.ident.as_str(), item.clone());
                                return problems.with(Some(item));
                            }
                        }
                    }
                    Some((_, ast::TypeDefinition::Struct(_))) => {
                        if let Some(kind) = kind {
                            let item = ItemDecl::Struct(kind, Arc::new(OnceLock::new()));
                            self.header.insert(name.ident.as_str(), item.clone());
                            return problems.with(Some(item));
                        }
                    }
                    Some((_, ast::TypeDefinition::Intrinsic(_))) => {
                        let ty = problems.append(self.intrinsic_type(name));
                        if let (Some(kind), Some(ty)) = (kind, ty) {
                            let item = ItemDecl::Alias(kind, Term::Type(ty));
                            self.header.insert(name.ident.as_str(), item.clone());
                            return problems.with(Some(item));
                        }
                    }
                    None => todo!("error"),
                }
            }
            ast::Item::Function(decl, def) => match parent {
                Some(parent) => {
                    // TODO: is there a way to get this without looking it up again?
                    let Some(name) = parent.name() else { todo!() };
                    let Some(item) = self.header.get(name.ident.as_str()) else {
                        todo!()
                    };
                    let &ItemDecl::Effect(kind, _) = item else {
                        todo!("error")
                    };

                    let generics = self.generics(
                        self.tt[kind].params.as_ref(),
                        name.generics.as_ref(),
                        &Generics::new(),
                    );
                    let sig = problems.append(self.function_signature(decl, &generics));
                    if let Some(sig) = sig {
                        let apply = self.dummy_args(kind);
                        let effect = self.tt.insert_effect(EffectEnum::Item(Item {
                            module: self.module.clone(),
                            name: name.ident.as_str().to_compact_string(),
                            apply,
                        }));

                        let item = ItemDecl::Function(sig, Some(effect));
                        self.header.insert(decl.name.ident.as_str(), item.clone());
                        return problems.with(Some(item));
                    }
                }
                None => {
                    let sig = problems.append(self.function_signature(decl, &Generics::new()));
                    if let Some(sig) = sig {
                        let item = ItemDecl::Function(sig, None);
                        self.header.insert(decl.name.ident.as_str(), item.clone());
                        return problems.with(Some(item));
                    }
                }
            },
            ast::Item::Effect(_, name, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind =
                    problems.append(self.kind(name.generics.as_ref(), SimpleKind::Effect, None));

                match def {
                    Some((_, ast::EffectDefinition::Body(_))) => {
                        if let Some(kind) = kind {
                            let item = ItemDecl::Effect(kind, Arc::new(OnceLock::new()));
                            self.header.insert(name.ident.as_str(), item.clone());
                            return problems.with(Some(item));
                        }
                    }
                    Some((_, ast::EffectDefinition::Alias(effects))) => {
                        if let Some(kind) = kind {
                            let generics = self.generics(
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                &Generics::new(),
                            );
                            let effects = problems.append(
                                effects
                                    .iter()
                                    .map(|path| self.effect(path, &generics, None))
                                    .collect::<Result<Arc<_>>>(),
                            );
                            if let Some(effects) = effects {
                                let effect = Effect::row(effects.iter(), self.tt);
                                let item = ItemDecl::Alias(kind, Term::Effect(effect));
                                self.header.insert(name.ident.as_str(), item.clone());
                                return problems.with(Some(item));
                            }
                        }
                    }
                    Some((_, ast::EffectDefinition::Intrinsic(_))) => {
                        let eff = problems.append(self.intrinsic_effect(name));
                        if let (Some(kind), Some(eff)) = (kind, eff) {
                            let item = ItemDecl::Alias(kind, Term::Effect(eff));
                            self.header.insert(name.ident.as_str(), item.clone());
                            return problems.with(Some(item));
                        }
                    }
                    None => todo!("error"),
                }
            }
            ast::Item::Constant(_, name, ty, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                // NOTE: if we eventually have dependent kinds this this might fail
                let ty = problems.append(self.r#type(ty, &Generics::new(), None));
                let kind = ty.and_then(|ty| {
                    problems.append(self.kind(
                        name.generics.as_ref(),
                        SimpleKind::Constant(ty),
                        None,
                    ))
                });

                match def {
                    Some((_, ast::ConstantDefinition::Constant(constant))) => {
                        if let (Some(ty), Some(kind)) = (ty, kind) {
                            let generics = self.generics(
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                &Generics::new(),
                            );
                            let constant =
                                problems.append(self.constant(constant, &generics, ty, None));
                            if let Some(constant) = constant {
                                let item = ItemDecl::Alias(kind, Term::Constant(constant));
                                self.header.insert(name.ident.as_str(), item.clone());
                                return problems.with(Some(item));
                            }
                        }
                    }
                    Some((_, ast::ConstantDefinition::Intrinsic(_))) => {
                        let constant = problems.append(self.intrinsic_constant(name));
                        if let (Some(kind), Some(constant)) = (kind, constant) {
                            let item = ItemDecl::Alias(kind, Term::Constant(constant));
                            self.header.insert(name.ident.as_str(), item.clone());
                            return problems.with(Some(item));
                        }
                    }
                    None => todo!("error"),
                }
            }
            ast::Item::Handle(_, params, handler) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let implicit_regions = self.implicit_regions(&handler.effect)
                    + handler
                        .with_effects
                        .as_ref()
                        .map(|es| self.implicit_regions(es))
                        .unwrap_or(0);
                let mut implicit = Implicit::new(implicit_regions);
                let type_params =
                    problems.append(self.kind_params(params.as_ref(), Some(&mut implicit)));
                if let Some(type_params) = type_params {
                    let generics = self
                        .generics(type_params.as_ref(), params.as_ref(), &Generics::new())
                        .shifted(implicit_regions);
                    let effect = problems.append(self.effect(
                        &handler.effect,
                        &generics,
                        Some(&mut implicit),
                    ));
                    let with_effects = problems.append(
                        handler
                            .with_effects
                            .iter()
                            .flat_map(|we| &we.effects)
                            .map(|effect| self.effect(effect, &generics, Some(&mut implicit)))
                            .collect::<Result<Box<_>>>(),
                    );
                    if let (Some(effect), Some(with_effects)) = (effect, with_effects) {
                        let with_effect = Effect::row(
                            with_effects.iter().chain(implicit.effects.iter()),
                            self.tt,
                        );
                        let handler = HandlerDecl {
                            type_params,
                            implicit_regions,
                            effect,
                            with_effect,
                        };
                        self.header.insert_global_handler(handler);
                        return problems.with(None);
                    }
                }
            }
        }

        problems.with(None)
    }
    fn struct_member(
        &mut self,
        member: &ast::StructMember,
        generics: &Generics,
    ) -> Result<StructMember> {
        match member {
            ast::StructMember::Data(name, ty) => {
                self.r#type(ty, generics, None).map(|ty| StructMember {
                    name: name.as_str().to_compact_string(),
                    ty,
                })
            }
        }
    }
    fn item(&self, path: &ast::Path) -> std::result::Result<(&Module, &ItemDecl), Problems> {
        let (module, preamble) = match &path.package {
            Some((pkg, _)) => match self.imports.get(pkg.as_str()) {
                Some(module) => match self.query.header(module) {
                    Some(ir) => ((module, ir), None),
                    None => todo!("recover"),
                },
                None => todo!("error"),
            },
            None => (
                (self.module, &self.header),
                self.imports
                    .preamble()
                    .and_then(|module| self.query.header(module).map(|ir| (module, ir))),
            ),
        };

        for (module, ir) in iter::once(module).chain(preamble) {
            if let Some(item) = ir.get(path.name.as_str()) {
                return Ok((module, item));
            }
        }

        todo!(
            "error: unknown {}, searched in {:?} and {:?}",
            path.name.as_str(),
            module.0,
            preamble.map(|t| t.0)
        )
    }
    fn apply(
        &mut self,
        kind: Kind,
        term: Term,
        ast: Option<&ast::GenericArguments>,
        generics: &Generics,
        mut implicit: Option<&mut Implicit>,
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
                        self.generic_argument(param, arg, generics, implicit.as_deref_mut())
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
                    GenericArgument { term, arity }
                })
                .collect()
        })
    }
    fn term_path(
        &mut self,
        path: &ast::Path,
        generics: &Generics,
        implicit: Option<&mut Implicit>,
    ) -> Result<(Kind, Term)> {
        let (item_kind, term) = {
            if path.package.is_none()
                && let Some((index, kind)) = generics.get(path.name.as_str())
            {
                // Generic Parameter
                let apply = self.dummy_args(kind);
                let arity = apply.as_ref().map(|params| params.len());
                let param = GenericParameter {
                    index: index + arity.unwrap_or(0),
                    apply,
                };
                let term = match self.tt[kind].output {
                    SimpleKind::Type => Term::Type(self.tt.insert_type(TypeEnum::Generic(param))),
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
                    SimpleKind::Constant(_) => {
                        Term::Constant(self.tt.insert_constant(ConstantEnum::Generic(param)))
                    }
                };
                (kind, term)
            } else {
                // Module Item
                let (module, item) = match self.item(path) {
                    Ok((module, item)) => (module, item),
                    Err(problems) => return problems.with(todo!("recovery value")),
                };
                match *item {
                    ItemDecl::Alias(item_kind, term) => (item_kind, term),
                    ItemDecl::Struct(item_kind, _) => {
                        let module = module.clone();
                        let generics = self.dummy_args(item_kind);
                        let base = self.tt.insert_type(TypeEnum::Item(Item {
                            module,
                            name: path.name.as_str().to_compact_string(),
                            apply: generics,
                        }));
                        (item_kind, Term::Type(base))
                    }
                    ItemDecl::Effect(item_kind, _) => {
                        let module = module.clone();
                        let generics = self.dummy_args(item_kind);
                        let base = self.tt.insert_effect(EffectEnum::Item(Item {
                            module,
                            name: path.name.as_str().to_compact_string(),
                            apply: generics,
                        }));
                        (item_kind, Term::Effect(base))
                    }
                    ItemDecl::Function(_, _) => todo!("error"),
                }
            }
        };

        self.apply(item_kind, term, path.generics.as_ref(), generics, implicit)
    }
    fn generic_argument(
        &mut self,
        param: Kind,
        arg: &ast::GenericArgument,
        generics: &Generics,
        mut implicit: Option<&mut Implicit>,
    ) -> Result<GenericArgument> {
        let arity = self.tt[param].params.as_ref().map(|params| params.len());
        let generics = generics.shifted(arity.unwrap_or(0));
        match arg {
            ast::GenericArgument::Path(path, effects) => match effects {
                Some(effects) => {
                    if self.tt[param] == KindEnum::THUNK {
                        m! {
                            thunk <- self
                                .term_path(path, &generics, implicit.as_deref_mut())
                                .and_then(|(kind, term)| {
                                    match term {
                                        Term::Type(returns) if self.tt[kind].params.is_none() =>
                                            Result::new(Thunk {
                                                returns,
                                                effect: Effect::empty(self.tt)
                                            }),
                                        Term::Thunk(thunk) if self.tt[kind].params.is_none() =>
                                            Result::new(thunk),
                                        _ => todo!("error"),
                                    }
                                });
                            effects <- effects.effects
                                .iter()
                                .map(|effect| self.effect(effect, &generics, implicit.as_deref_mut()))
                                .collect::<Result<Box<_>>>();
                            let effect = Effect::row(iter::once(&thunk.effect).chain(&effects), self.tt);
                            return Term::Thunk(Thunk {
                                returns: thunk.returns,
                                effect,
                            });
                        }
                    } else {
                        todo!("error")
                    }
                }
                None => self
                    .term_path(path, &generics, implicit)
                    .and_then(|(kind, term)| {
                        if kind == param {
                            Result::new(term)
                        } else if let Term::Type(ty) = term
                            && self.tt[param].params == self.tt[kind].params
                            && self.tt[param].output == SimpleKind::Thunk
                        {
                            Result::new(Term::Thunk(Thunk {
                                returns: ty,
                                effect: Effect::empty(self.tt),
                            }))
                        } else if let Term::Effect(effect) = term
                            && self.tt[param].params == self.tt[kind].params
                            && self.tt[param].output == SimpleKind::Thunk
                        {
                            Result::new(Term::Thunk(Thunk {
                                returns: self.tt.insert_type(TypeEnum::Unit),
                                effect,
                            }))
                        } else {
                            todo!(
                                "error: found '{}' expected '{}'",
                                kind.display(self.tt),
                                param.display(self.tt)
                            )
                        }
                    }),
            },
            ast::GenericArgument::Type(ty, effects) => {
                if self.tt[param] == KindEnum::TYPE && effects.is_none() {
                    self.r#type(ty, &generics, implicit).map(Term::Type)
                } else if self.tt[param] == KindEnum::THUNK {
                    m! {
                        returns <- self.r#type(ty, &generics, implicit.as_deref_mut());
                        effects <- effects
                            .iter()
                            .flat_map(|we| &we.effects)
                            .map(|effect| self.effect(effect, &generics, implicit.as_deref_mut()))
                            .collect::<Result<Box<_>>>();
                        let effect = Effect::row(&effects, self.tt);
                        return Term::Thunk(Thunk {
                            returns,
                            effect,
                        });
                    }
                } else {
                    todo!("error")
                }
            }
            ast::GenericArgument::Constant(constant) => todo!(),
        }
        .map(|term| GenericArgument { term, arity })
    }
    fn region(
        &mut self,
        region: &ast::Path,
        generics: &Generics,
        implicit: Option<&mut Implicit>,
    ) -> Result<Region> {
        self.term_path(region, generics, implicit)
            .and_then(|(kind, path)| match path {
                Term::Region(region) if self.tt[kind].params.is_none() => Result::new(region),
                _ => todo!("error"),
            })
    }
    fn effect(
        &mut self,
        effect: &ast::Path,
        generics: &Generics,
        implicit: Option<&mut Implicit>,
    ) -> Result<Effect> {
        self.term_path(effect, generics, implicit)
            .and_then(|(kind, path)| match path {
                Term::Effect(effect) if self.tt[kind].params.is_none() => Result::new(effect),
                _ => todo!("error"),
            })
    }
    fn implicit_regions(&mut self, ast: &impl Ast) -> usize {
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
        generics: &Generics,
        implicit: Option<&mut Implicit>,
    ) -> Result<Region> {
        let kind = match ty {
            Some(ast::PointerRegion::At(_, path)) => return self.region(path, generics, implicit),
            Some(ast::PointerRegion::Kind(kind)) => Some(kind),
            None => None,
        };

        let Some(implicit) = implicit else {
            todo!("error")
        };

        implicit.generics = implicit
            .generics
            .checked_sub(1)
            .expect("ICE: no implicit region generic left!");
        Result::new(self.implicit_region(kind, implicit.generics, &mut implicit.effects))
    }
    fn implicit_region(
        &mut self,
        kind: Option<&ast::RegionKind>,
        index: usize,
        effects: &mut Vec<Effect>,
    ) -> Region {
        let region = self
            .tt
            .insert_region(RegionEnum::Generic(GenericParameter { index, apply: None }));
        match kind {
            Some(ast::RegionKind::Mutable(_)) => {
                effects.push(self.tt.insert_effect(EffectEnum::Read(region)));
                effects.push(self.tt.insert_effect(EffectEnum::Write(region)));
            }
            None => {
                effects.push(self.tt.insert_effect(EffectEnum::Read(region)));
            }
        }
        region
    }
    fn r#type(
        &mut self,
        ty: &ast::Type,
        generics: &Generics,
        mut implicit: Option<&mut Implicit>,
    ) -> Result<Type> {
        match ty {
            ast::Type::Path(path) => {
                self.term_path(path, generics, implicit)
                    .and_then(|(kind, path)| match path {
                        Term::Type(ty) if self.tt[kind].params.is_none() => Result::new(ty),
                        _ => todo!("error"),
                    })
            }
            ast::Type::Pointer(_, region, ty) => {
                if let ast::Type::Array(props, inner) = &**ty
                    && props.inner.size.is_none()
                {
                    // pointer to slice
                    m! {
                        let sentinel = props.inner.sentinel.is_some().then_some(Sentinel);
                        region <- self.pointer_region(region.as_ref(), generics, implicit.as_deref_mut());
                        ty <- self.r#type(inner, generics, implicit);
                        return self.tt.insert_type(TypeEnum::PointerSlice(ty, region, sentinel));
                    }
                } else {
                    // regular pointer
                    m! {
                        region <- self.pointer_region(region.as_ref(), generics, implicit.as_deref_mut());
                        ty <- self.r#type(ty, generics, implicit);
                        return self.tt.insert_type(TypeEnum::Pointer(ty, region));
                    }
                }
            }
            ast::Type::Array(props, ty) => {
                let Some(size) = &props.inner.size else {
                    todo!("error: naked slice")
                };

                let usize_ty = self.tt.insert_type(TypeEnum::USIZE);
                m! {
                    size <- self.constant(size, generics, usize_ty, implicit.as_deref_mut());
                    let sentinel = props.inner.sentinel.is_some().then_some(Sentinel);
                    ty <- self.r#type(ty, generics, implicit);
                    return self.tt.insert_type(TypeEnum::Array(ty, size, sentinel));
                }
            }
        }
    }
    fn constant(
        &mut self,
        constant: &ast::Constant,
        generics: &Generics,
        ty: Type,
        implicit: Option<&mut Implicit>,
    ) -> Result<Constant> {
        match constant {
            ast::Constant::Path(path) => {
                let expected = self.tt.insert_kind(KindEnum::constant(ty));
                self.term_path(path, generics, implicit)
                    .and_then(|(kind, term)| match term {
                        Term::Constant(ty) if kind == expected => Result::new(ty),
                        _ => todo!("error"),
                    })
            }
            // TODO: mark somewhere that the type must be able to be created from these literals
            ast::Constant::Integer(integer) => Result::new(
                self.tt
                    .insert_constant(ConstantEnum::Integer(integer.value)),
            ),
            ast::Constant::String(string) => Result::new(
                self.tt
                    .insert_constant(ConstantEnum::String(string.value.clone())),
            ),
            ast::Constant::Character(character) => Result::new(
                self.tt
                    .insert_constant(ConstantEnum::Character(character.value.clone())),
            ),
            ast::Constant::Zero(_) => Result::new(self.tt.insert_constant(ConstantEnum::Zero)),
        }
    }
    fn simple_kind(&mut self, kind: &ast::Kind) -> Result<SimpleKind> {
        match kind {
            ast::Kind::Type(_) => Result::new(SimpleKind::Type),
            ast::Kind::Effect(_) => Result::new(SimpleKind::Effect),
            ast::Kind::Region(_) => Result::new(SimpleKind::Region),
            ast::Kind::Thunk(_) => Result::new(SimpleKind::Thunk),
            // TODO: allow constant with generic type?
            ast::Kind::Constant(ty) => self
                .r#type(ty, &Generics::new(), None)
                .map(SimpleKind::Constant),
        }
    }
    fn kind_params(
        &mut self,
        name: Option<&ast::GenericParameters>,
        mut implicit: Option<&mut Implicit>,
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
                            if let Some(implicit) = implicit.as_deref_mut() {
                                self.implicit_region(
                                    kind.as_ref(),
                                    index + implicit.generics,
                                    &mut implicit.effects,
                                );
                            } else if let Some(kind) = kind {
                                todo!("error")
                            }
                            Result::new(SimpleKind::Region)
                        }
                        ast::GenericParameter::Other(_, kind) => self.simple_kind(kind),
                    }
                    .and_then(|output| self.kind(param.generics(), output, None))
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
        implicit: Option<&mut Implicit>,
    ) -> Result<Kind> {
        self.kind_params(name, implicit)
            .map(|params| self.tt.insert_kind(KindEnum { params, output }))
    }

    fn intrinsic_type(&mut self, name: &ast::Name) -> Result<Type> {
        let module = self.module.to_compact_string();
        let ty = match (module.as_str(), name.ident.as_str()) {
            ("builtin:types", "u8") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(8))),
            ("builtin:types", "u16") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(16))),
            ("builtin:types", "u32") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(32))),
            ("builtin:types", "u64") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(64))),
            ("builtin:types", "uint") => TypeEnum::Integer(Integer::unsigned(IntSize::Register)),
            ("builtin:types", "uptr") => TypeEnum::Integer(Integer::unsigned(IntSize::Address)),
            ("builtin:types", "usize") => TypeEnum::Integer(Integer::unsigned(IntSize::Index)),
            ("builtin:types", "i8") => TypeEnum::Integer(Integer::signed(IntSize::Exact(8))),
            ("builtin:types", "i16") => TypeEnum::Integer(Integer::signed(IntSize::Exact(16))),
            ("builtin:types", "i32") => TypeEnum::Integer(Integer::signed(IntSize::Exact(32))),
            ("builtin:types", "i64") => TypeEnum::Integer(Integer::signed(IntSize::Exact(64))),
            ("builtin:types", "int") => TypeEnum::Integer(Integer::signed(IntSize::Register)),
            ("builtin:types", "iptr") => TypeEnum::Integer(Integer::signed(IntSize::Address)),
            ("builtin:types", "isize") => TypeEnum::Integer(Integer::signed(IntSize::Index)),
            ("builtin:types", "bool") => TypeEnum::Boolean,
            ("builtin:types", "unit") => TypeEnum::Unit,
            ("builtin:c", "char") => TypeEnum::Integer(Integer::CChar),
            ("builtin:c", "schar") => TypeEnum::Integer(Integer::signed(IntSize::CChar)),
            ("builtin:c", "uchar") => TypeEnum::Integer(Integer::unsigned(IntSize::CChar)),
            ("builtin:c", "short") => TypeEnum::Integer(Integer::signed(IntSize::CShort)),
            ("builtin:c", "ushort") => TypeEnum::Integer(Integer::unsigned(IntSize::CShort)),
            ("builtin:c", "int") => TypeEnum::Integer(Integer::signed(IntSize::CInt)),
            ("builtin:c", "uint") => TypeEnum::Integer(Integer::unsigned(IntSize::CInt)),
            ("builtin:c", "long") => TypeEnum::Integer(Integer::signed(IntSize::CLong)),
            ("builtin:c", "ulong") => TypeEnum::Integer(Integer::unsigned(IntSize::CLong)),
            ("builtin:c", "longlong") => TypeEnum::Integer(Integer::signed(IntSize::CLongLong)),
            ("builtin:c", "ulonglong") => TypeEnum::Integer(Integer::unsigned(IntSize::CLongLong)),
            _ => todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.ident.as_str()
            ),
        };
        Result::new(self.tt.insert_type(ty))
    }
    fn intrinsic_effect(&mut self, name: &ast::Name) -> Result<Effect> {
        let module = self.module.to_compact_string();
        let effect = match (module.as_str(), name.ident.as_str()) {
            ("builtin:builtin", "Div") => EffectEnum::Divergent,
            ("builtin:regions", "Read") => {
                let region = self.tt.insert_region(RegionEnum::Generic(GenericParameter {
                    index: 0,
                    apply: None,
                }));
                EffectEnum::Read(region)
            }
            ("builtin:regions", "Write") => {
                let region = self.tt.insert_region(RegionEnum::Generic(GenericParameter {
                    index: 0,
                    apply: None,
                }));
                EffectEnum::Write(region)
            }
            _ => todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.ident.as_str()
            ),
        };
        Result::new(self.tt.insert_effect(effect))
    }
    fn intrinsic_constant(&mut self, name: &ast::Name) -> Result<Constant> {
        let module = self.module.to_compact_string();
        let constant = match (module.as_str(), name.ident.as_str()) {
            ("builtin:types", "true") => ConstantEnum::True,
            ("builtin:types", "false") => ConstantEnum::False,
            _ => todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.ident.as_str()
            ),
        };
        Result::new(self.tt.insert_constant(constant))
    }

    fn function_signature(
        &mut self,
        sig: &'a ast::FunctionDeclaration,
        generics: &Generics<'a>,
    ) -> Result<FunctionSignature> {
        m! {
            let implicit_regions = self.implicit_regions(sig);
            let mut implicit = Implicit::new(implicit_regions);
            type_params <- self.kind_params(sig.name.generics.as_ref(), Some(&mut implicit));
            let generics = self.generics(type_params.as_ref(), sig.name.generics.as_ref(), generics).shifted(implicit_regions);
            params <- match &sig.parameters {
                Some(params) => params.inner
                    .iter()
                    .map(|param| self.function_param(param, &generics, Some(&mut implicit)))
                    .collect::<Result<_>>()
                    .map(Some),
                None => Result::new(None),
            };
            thunk <- self.thunk(sig.returns.as_ref(), &generics, Some(&mut implicit));
            effects <- sig
                .effects
                .iter()
                .flat_map(|we| &we.effects)
                .map(|effect| self.effect(effect, &generics, Some(&mut implicit)))
                .collect::<Result<Box<_>>>();
            let effect = Effect::row(iter::once(&thunk.effect).chain(&effects).chain(&implicit.effects), self.tt);
            return self.tt.insert_function_signature(FunctionSignatureValue {
                type_params,
                implicit_regions,
                params,
                thunk: Thunk {
                    returns: thunk.returns,
                    effect,
                }
            });
        }
    }
    fn thunk(
        &mut self,
        returns: Option<&ast::Returns>,
        generics: &Generics,
        implicit: Option<&mut Implicit>,
    ) -> Result<Thunk> {
        match returns {
            Some(returns) => match returns {
                ast::Returns::Path(path) => {
                    self.term_path(path, generics, implicit)
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
                ast::Returns::Type(ty) => self.r#type(ty, generics, implicit).map(|ty| Thunk {
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
        generics: &Generics<'a>,
        implicit: Option<&mut Implicit>,
    ) -> Result<FunctionParameter> {
        match param {
            ast::Parameter::Data(_, ty) => self
                .r#type(ty, generics, implicit)
                .map(FunctionParameter::Data),
            ast::Parameter::Lambda(decl) => self
                .function_signature(decl, generics)
                .map(FunctionParameter::Lambda),
        }
    }
}
