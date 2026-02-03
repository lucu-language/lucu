use std::iter;
use std::sync::Arc;

use compact_str::ToCompactString;
use do_notation::m;

use crate::ast;
use crate::error::{Problems, Result};
use crate::ir::{
    EffectDef, EffectDefinition, EffectMember, FunctionBody, FunctionBodyDefinition,
    HandlerBodyDefinition, HandlerDef, HandlerMember, IR, IntrinsicFunction, ItemDef,
    ItemDefinition, Parent, StructDefinition, StructMember,
};
use crate::module::Module;
use crate::pass::defs::Definitions;
use crate::pass::imports::Imports;
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, FunctionParameter, FunctionReturns,
    FunctionSignature, FunctionSignatureValue, GenericArgument, GenericParameter, IntSize, Integer,
    Item, Kind, KindEnum, Region, RegionEnum, Sentinel, SimpleKind, Term, Type, TypeEnum,
    TypeTable,
};

struct Lower<'a> {
    tt: &'a mut TypeTable,
    module: &'a Module,

    ast: &'a ast::Module,
    imports: &'a Imports,
    definitions: &'a Definitions,

    query: &'a dyn IRQuery,
    ir: IR,
}

enum LoweredDef {
    Item(ItemDef),
    Handler(HandlerDef),
    None,
}

pub trait IRQuery {
    fn untyped_ir(&self, module: &Module) -> Option<&IR>;
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

impl IR {
    pub fn from(
        query: &impl IRQuery,
        module: &Module,
        ast: &ast::Module,
        imports: &Imports,
        definitions: &Definitions,
        tt: &mut TypeTable,
    ) -> Option<Result<Self>> {
        let lower = Lower {
            tt,
            module,
            ast,
            imports,
            definitions,
            query,
            ir: IR::default(),
        };
        Some(lower.module())
    }
}

impl Lower<'_> {
    fn module(mut self) -> Result<IR> {
        let mut decl_problems = Problems::ok();
        let defs = decl_problems
            .append(
                self.definitions
                    .postorder_with_parent(self.ast)
                    .map(|(def, parent)| self.declaration(def, parent))
                    .collect::<Result<Vec<_>>>(),
            )
            .expect("ICE: no definition list");
        assert_eq!(
            defs.len(),
            self.definitions.indices().len(),
            "ICE: definition list has different size"
        );
        let def_problems = Iterator::zip(self.definitions.postorder(self.ast), defs)
            .map(|(def, lower)| self.definition(def, lower))
            .collect::<Problems>();
        (decl_problems + def_problems).with(self.ir)
    }
    fn generics<'a>(
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
                        .map(|(ast, &kind)| (ast.name.ident.as_str(), kind)),
                )
            }
            (None, None) => base.clone(),
            _ => unreachable!(),
        }
    }
    fn definition(&mut self, def: &ast::Item, lower: LoweredDef) -> Problems {
        let mut problems = Problems::ok();

        match def {
            ast::Item::Type(_, name, def) => {
                if let Some((_, ast::TypeDefinition::Struct(struc))) = def {
                    let LoweredDef::Item(ItemDef::Struct(kind, idx)) = lower else {
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

                    self.ir.realize_struct(idx, StructDefinition { members });
                }
            }
            ast::Item::Function(_, def) => {
                if let Some((_, ast::FunctionDefinition::Expression(body))) = def {
                    let LoweredDef::Item(ItemDef::Function(_, Parent::TopLevel(fun))) = lower
                    else {
                        return problems;
                    };

                    self.ir.realize_function_body(
                        fun,
                        FunctionBodyDefinition::Expression {
                            captures: 0,
                            body: (),
                        },
                    );
                }
            }
            ast::Item::Effect(_, _, defs) => {
                if let Some((_, ast::EffectDefinition::Body(body))) = defs {
                    let LoweredDef::Item(ItemDef::Effect(_, eff)) = lower else {
                        return problems;
                    };

                    let members = body
                        .items
                        .inner
                        .iter()
                        .filter_map(|def| {
                            // TODO: is there a way to get this without looking it up again?
                            let name = def.name()?;
                            let ItemDef::Function(sig, _) = self.ir.get(name.ident.as_str())?
                            else {
                                return None;
                            };
                            Some(EffectMember {
                                name: name.ident.as_str().to_compact_string(),
                                signature: sig,
                            })
                        })
                        .collect();

                    self.ir
                        .realize_effect(eff, EffectDefinition::Body { members });
                }
            }
            ast::Item::Constant(_, _, _, _) => {}
            ast::Item::Handle(_, params, handler) => {
                let LoweredDef::Handler(HandlerDef {
                    kind,
                    effect,
                    with_effect: _,
                    body,
                }) = lower
                else {
                    return problems;
                };

                let generics = self.generics(
                    self.tt[kind].params.as_ref(),
                    params.as_ref(),
                    &Generics::new(),
                );

                let EffectEnum::Item(effect_item) = &self.tt[effect] else {
                    todo!("error: effect is not a single item")
                };
                let effect_args = effect_item.apply.clone();

                let ItemDefinition::Effect(_, effect_def) = self.resolve_item(effect_item) else {
                    unreachable!("ICE: effect item is not an effect")
                };

                match effect_def {
                    EffectDefinition::Body { members } => {
                        let members = members
                            .clone()
                            .into_iter()
                            .map(|member| {
                                let expected_sig = match &effect_args {
                                    Some(args) => member.signature.subst(self.tt, 0, args),
                                    None => member.signature,
                                };

                                let Some(matching) = handler.items.inner.iter().find(|def| {
                                    def.name()
                                        .is_some_and(|name| name.ident.as_str() == member.name)
                                }) else {
                                    todo!(
                                        "error: no definition for '{}' inside handler",
                                        member.name
                                    )
                                };

                                let ast::Item::Function(fun_decl, fun_def) = matching else {
                                    todo!("error: definition '{}' is not a function", member.name)
                                };

                                let Some(signature) =
                                    problems.append(self.function_signature(fun_decl, &generics))
                                else {
                                    return HandlerMember {
                                        name: member.name,
                                        signature: expected_sig,
                                        body: None,
                                    };
                                };
                                if expected_sig != signature {
                                    todo!(
                                        "error: signature mismatch. Expected {}, got {}",
                                        expected_sig.display(self.tt),
                                        signature.display(self.tt)
                                    );
                                }

                                let Some((_, fun_def)) = fun_def else {
                                    todo!("error")
                                };

                                match fun_def {
                                    ast::FunctionDefinition::Expression(expr) => {
                                        let body = self.ir.push_function_body();
                                        self.ir.realize_function_body(
                                            body,
                                            FunctionBodyDefinition::Expression {
                                                captures: 0,
                                                body: (),
                                            },
                                        );
                                        HandlerMember {
                                            body: Some(body),
                                            name: member.name,
                                            signature,
                                        }
                                    }
                                    ast::FunctionDefinition::Intrinsic(_) => HandlerMember {
                                        body: problems
                                            .append(self.intrinsic_function(&fun_decl.name)),
                                        name: member.name,
                                        signature,
                                    },
                                }
                            })
                            .collect::<Vec<HandlerMember>>();

                        // TODO: check for duplicates
                        // TODO: check for unknown

                        self.ir
                            .realize_handler_body(body, HandlerBodyDefinition { members });
                    }
                    EffectDefinition::Intrinsic => todo!("error: effect is intrinsic"),
                }
            }
        }

        problems
    }
    fn declaration(&mut self, def: &ast::Item, parent: Option<&ast::Item>) -> Result<LoweredDef> {
        let mut problems = Problems::ok();

        match def {
            ast::Item::Type(_, name, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind = problems.append(self.kind(name.generics.as_ref(), SimpleKind::Type));

                match def {
                    Some((_, ast::TypeDefinition::Type(ast))) => {
                        if let Some(kind) = kind {
                            let generics = self.generics(
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                &Generics::new(),
                            );
                            let ty = problems.append(self.r#type(ast, &generics));
                            if let Some(ty) = ty {
                                let item = ItemDef::Alias(kind, Term::Type(ty));
                                self.ir.insert(name.ident.as_str(), item);
                                return problems.with(LoweredDef::Item(item));
                            }
                        }
                    }
                    Some((_, ast::TypeDefinition::Struct(_))) => {
                        if let Some(kind) = kind {
                            let struc = self.ir.push_struct();
                            let item = ItemDef::Struct(kind, struc);
                            self.ir.insert(name.ident.as_str(), item);
                            return problems.with(LoweredDef::Item(item));
                        }
                    }
                    Some((_, ast::TypeDefinition::Intrinsic(_))) => {
                        let ty = problems.append(self.intrinsic_type(name));
                        if let (Some(kind), Some(ty)) = (kind, ty) {
                            let item = ItemDef::Alias(kind, Term::Type(ty));
                            self.ir.insert(name.ident.as_str(), item);
                            return problems.with(LoweredDef::Item(item));
                        }
                    }
                    None => todo!("error"),
                }
            }
            ast::Item::Function(decl, def) => match parent {
                Some(parent) => {
                    // TODO: is there a way to get this without looking it up again?
                    let Some(name) = parent.name() else { todo!() };
                    let Some(item) = self.ir.get(name.ident.as_str()) else {
                        todo!()
                    };
                    let ItemDef::Effect(kind, _) = item else {
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

                        let item = ItemDef::Function(sig, Parent::Effect(effect));
                        self.ir.insert(decl.name.ident.as_str(), item);
                        return problems.with(LoweredDef::Item(item));
                    }
                }
                None => {
                    let sig = problems.append(self.function_signature(decl, &Generics::new()));
                    match def {
                        Some((_, ast::FunctionDefinition::Expression(_))) => {
                            if let Some(sig) = sig {
                                let fun = self.ir.push_function_body();
                                let item = ItemDef::Function(sig, Parent::TopLevel(fun));
                                self.ir.insert(decl.name.ident.as_str(), item);
                                return problems.with(LoweredDef::Item(item));
                            }
                        }
                        Some((_, ast::FunctionDefinition::Intrinsic(_))) => {
                            let fun = problems.append(self.intrinsic_function(&decl.name));
                            if let (Some(sig), Some(fun)) = (sig, fun) {
                                let item = ItemDef::Function(sig, Parent::TopLevel(fun));
                                self.ir.insert(decl.name.ident.as_str(), item);
                                return problems.with(LoweredDef::Item(item));
                            }
                        }
                        None => todo!("error"),
                    }
                }
            },
            ast::Item::Effect(_, name, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind = problems.append(self.kind(name.generics.as_ref(), SimpleKind::Effect));

                match def {
                    Some((_, ast::EffectDefinition::Body(_))) => {
                        if let Some(kind) = kind {
                            let effect = self.ir.push_effect();
                            let item = ItemDef::Effect(kind, effect);
                            self.ir.insert(name.ident.as_str(), item);
                            return problems.with(LoweredDef::Item(item));
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
                                    .map(|path| self.effect(path, &generics))
                                    .collect::<Result<Arc<_>>>(),
                            );
                            if let Some(effects) = effects {
                                let effect = Effect::row(effects.iter(), self.tt);
                                let item = ItemDef::Alias(kind, Term::Effect(effect));
                                self.ir.insert(name.ident.as_str(), item);
                                return problems.with(LoweredDef::Item(item));
                            }
                        }
                    }
                    Some((_, ast::EffectDefinition::Intrinsic(_))) => {
                        let eff = problems.append(self.intrinsic_effect(name));
                        if let (Some(kind), Some(eff)) = (kind, eff) {
                            let item = ItemDef::Effect(kind, eff);
                            self.ir.insert(name.ident.as_str(), item);
                            return problems.with(LoweredDef::Item(item));
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
                let ty = problems.append(self.r#type(ty, &Generics::new()));
                let kind = ty.and_then(|ty| {
                    problems.append(self.kind(name.generics.as_ref(), SimpleKind::Constant(ty)))
                });

                match def {
                    Some((_, ast::ConstantDefinition::Constant(constant))) => {
                        if let (Some(ty), Some(kind)) = (ty, kind) {
                            let generics = self.generics(
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                &Generics::new(),
                            );
                            let constant = problems.append(self.constant(constant, &generics, ty));
                            if let Some(constant) = constant {
                                let item = ItemDef::Alias(kind, Term::Constant(constant));
                                self.ir.insert(name.ident.as_str(), item);
                                return problems.with(LoweredDef::Item(item));
                            }
                        }
                    }
                    Some((_, ast::ConstantDefinition::Intrinsic(_))) => {
                        let constant = problems.append(self.intrinsic_constant(name));
                        if let (Some(kind), Some(constant)) = (kind, constant) {
                            let item = ItemDef::Alias(kind, Term::Constant(constant));
                            self.ir.insert(name.ident.as_str(), item);
                            return problems.with(LoweredDef::Item(item));
                        }
                    }
                    None => todo!("error"),
                }
            }
            ast::Item::Handle(_, params, handler) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind = problems.append(self.kind(params.as_ref(), SimpleKind::Effect));
                if let Some(kind) = kind {
                    let generics = self.generics(
                        self.tt[kind].params.as_ref(),
                        params.as_ref(),
                        &Generics::new(),
                    );
                    let effect = problems.append(self.effect(&handler.effect, &generics));
                    let with_effects = problems.append(
                        handler
                            .with_effects
                            .iter()
                            .flat_map(|we| &we.effects)
                            .map(|effect| self.effect(effect, &generics))
                            .collect::<Result<Arc<_>>>(),
                    );
                    if let (Some(effect), Some(with_effects)) = (effect, with_effects) {
                        let with_effect = Effect::row(with_effects.iter(), self.tt);
                        let body = self.ir.push_handler_body();
                        let handler = HandlerDef {
                            kind,
                            effect,
                            with_effect,
                            body,
                        };
                        self.ir.insert_global_handler(handler);
                        return problems.with(LoweredDef::Handler(handler));
                    }
                }
            }
        }

        problems.with(LoweredDef::None)
    }
    fn struct_member(
        &mut self,
        member: &ast::StructMember,
        generics: &Generics,
    ) -> Result<StructMember> {
        match member {
            ast::StructMember::Data(name, ty) => self.r#type(ty, generics).map(|ty| StructMember {
                name: name.as_str().to_compact_string(),
                ty,
            }),
        }
    }
    fn resolve_item<'a>(&'a self, item: &Item) -> ItemDefinition<'a> {
        let ir = if &item.module == self.module {
            &self.ir
        } else {
            self.query
                .untyped_ir(&item.module)
                .expect("ICE: module doesn't exist anymore")
        };
        ir.get(&item.name)
            .expect("ICE: item doesn't exist anymore")
            .resolve(ir)
    }
    fn item(&self, path: &ast::Path) -> std::result::Result<(&Module, ItemDef), Problems> {
        let (module, preamble) = match &path.package {
            Some((pkg, _)) => match self.imports.get(pkg.as_str()) {
                Some(module) => match self.query.untyped_ir(module) {
                    Some(ir) => ((module, ir), None),
                    None => todo!("recover"),
                },
                None => todo!("error"),
            },
            None => (
                (self.module, &self.ir),
                self.imports
                    .preamble()
                    .and_then(|module| self.query.untyped_ir(module).map(|ir| (module, ir))),
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
                    .map(|(param, arg)| self.generic_argument(param, arg, generics))
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
                        SimpleKind::Constant(_) => todo!(),
                    };
                    GenericArgument { term, arity }
                })
                .collect()
        })
    }
    fn term_path(&mut self, kind: Kind, path: &ast::Path, generics: &Generics) -> Result<Term> {
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
                match item {
                    ItemDef::Alias(item_kind, term) => (item_kind, term),
                    ItemDef::Struct(item_kind, _) => {
                        let module = module.clone();
                        let generics = self.dummy_args(item_kind);
                        let base = self.tt.insert_type(TypeEnum::Item(Item {
                            module,
                            name: path.name.as_str().to_compact_string(),
                            apply: generics,
                        }));
                        (item_kind, Term::Type(base))
                    }
                    ItemDef::Effect(item_kind, _) => {
                        let module = module.clone();
                        let generics = self.dummy_args(item_kind);
                        let base = self.tt.insert_effect(EffectEnum::Item(Item {
                            module,
                            name: path.name.as_str().to_compact_string(),
                            apply: generics,
                        }));
                        (item_kind, Term::Effect(base))
                    }
                    ItemDef::Function(_, _) => todo!("error"),
                }
            }
        };

        self.apply(item_kind, term, path.generics.as_ref(), generics)
            .and_then(|(applied_kind, path)| {
                if applied_kind == kind {
                    Result::new(path)
                } else {
                    todo!("error")
                }
            })
    }
    fn generic_argument(
        &mut self,
        param: Kind,
        arg: &ast::GenericArgument,
        generics: &Generics,
    ) -> Result<GenericArgument> {
        let arity = self.tt[param].params.as_ref().map(|params| params.len());
        let generics = generics.shifted(arity.unwrap_or(0));
        match arg {
            ast::GenericArgument::Path(path) => self.term_path(param, path, &generics),
            ast::GenericArgument::Type(ty) => {
                if self.tt[param] == KindEnum::TYPE {
                    self.r#type(ty, &generics).map(Term::Type)
                } else {
                    todo!("error")
                }
            }
            ast::GenericArgument::Constant(constant) => todo!(),
        }
        .map(|term| GenericArgument { term, arity })
    }
    fn region(&mut self, region: &ast::Path, generics: &Generics) -> Result<Region> {
        let kind = self.tt.insert_kind(KindEnum::REGION);
        self.term_path(kind, region, generics)
            .map(|path| match path {
                Term::Region(region) => region,
                _ => panic!("ICE: generic argument of kind Region is not actually a Region"),
            })
    }
    fn effect(&mut self, effect: &ast::Path, generics: &Generics) -> Result<Effect> {
        let kind = self.tt.insert_kind(KindEnum::EFFECT);
        self.term_path(kind, effect, generics)
            .map(|path| match path {
                Term::Effect(effect) => effect,
                _ => panic!("ICE: generic argument of kind Effect is not actually a Effect"),
            })
    }
    fn r#type(&mut self, ty: &ast::Type, generics: &Generics) -> Result<Type> {
        match ty {
            ast::Type::Path(path) => {
                let kind = self.tt.insert_kind(KindEnum::TYPE);
                self.term_path(kind, path, generics).map(|path| match path {
                    Term::Type(ty) => ty,
                    _ => panic!("ICE: generic argument of kind Type is not actually a Type"),
                })
            }
            ast::Type::Pointer(_, region, ty) => {
                if let ast::Type::Array(props, inner) = &**ty
                    && props.inner.size.is_none()
                {
                    // pointer to slice
                    m! {
                        let sentinel = props.inner.sentinel.is_some().then_some(Sentinel);
                        region <- self.region(&region.as_ref().expect("TODO: implied region").region, generics);
                        ty <- self.r#type(inner, generics);
                        return self.tt.insert_type(TypeEnum::PointerSlice(ty, region, sentinel));
                    }
                } else {
                    // regular pointer
                    m! {
                        region <- self.region(&region.as_ref().expect("TODO: implied region").region, generics);
                        ty <- self.r#type(ty, generics);
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
                    size <- self.constant(size, generics, usize_ty);
                    let sentinel = props.inner.sentinel.is_some().then_some(Sentinel);
                    ty <- self.r#type(ty, generics);
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
    ) -> Result<Constant> {
        match constant {
            ast::Constant::Path(path) => {
                let kind = self.tt.insert_kind(KindEnum::constant(ty));
                self.term_path(kind, path, generics).map(|path| match path {
                    Term::Constant(ty) => ty,
                    _ => {
                        panic!("ICE: generic argument of kind Constant is not actually a Constant")
                    }
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
            // TODO: allow constant with generic type?
            ast::Kind::Constant(ty) => self.r#type(ty, &Generics::new()).map(SimpleKind::Constant),
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
                .map(|param| {
                    match &param.kind {
                        Some(kind) => self.simple_kind(kind),
                        None => Result::new(SimpleKind::Type),
                    }
                    .and_then(|output| self.kind(param.name.generics.as_ref(), output))
                })
                .collect::<Result<_>>()
                .map(Some),
            None => Result::new(None),
        }
    }
    fn kind(&mut self, name: Option<&ast::GenericParameters>, output: SimpleKind) -> Result<Kind> {
        self.kind_params(name)
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
    fn intrinsic_function(&mut self, name: &ast::Name) -> Result<FunctionBody> {
        let module = self.module.to_compact_string();
        let value = match (module.as_str(), name.ident.as_str()) {
            ("builtin:ops", "len") => IntrinsicFunction::Len,
            ("builtin:regions", "local") => IntrinsicFunction::Local,
            ("builtin:regions", "alloca") => IntrinsicFunction::Alloca,
            ("builtin:preamble", "print_str") => IntrinsicFunction::PrintStr,
            ("builtin:preamble", "loop") => IntrinsicFunction::Loop,
            ("builtin:preamble", "unfounded") => IntrinsicFunction::Unfounded,

            ("builtin:ops", "index") => IntrinsicFunction::Index,

            _ => todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.ident.as_str()
            ),
        };
        let fun = self.ir.push_function_body();
        self.ir
            .realize_function_body(fun, FunctionBodyDefinition::Intrinsic(value));
        Result::new(fun)
    }
    fn intrinsic_effect(&mut self, name: &ast::Name) -> Result<EffectDef> {
        let module = self.module.to_compact_string();
        if !matches!(
            (module.as_str(), name.ident.as_str()),
            ("builtin:preamble", "Div")
                | ("builtin:regions", "Read")
                | ("builtin:regions", "Write"),
        ) {
            todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.ident.as_str()
            )
        }
        let eff = self.ir.push_effect();
        self.ir.realize_effect(eff, EffectDefinition::Intrinsic);
        Result::new(eff)
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

    fn function_signature<'a>(
        &mut self,
        sig: &'a ast::FunctionDeclaration,
        generics: &Generics<'a>,
    ) -> Result<FunctionSignature> {
        m! {
            type_params <- self.kind_params(sig.name.generics.as_ref());
            let generics = self.generics(type_params.as_ref(), sig.name.generics.as_ref(), generics);
            params <- match &sig.parameters {
                Some(params) => params.inner
                    .iter()
                    .map(|param| self.function_param(param, &generics))
                    .collect::<Result<_>>()
                    .map(Some),
                None => Result::new(None),
            };
            returns <- self.returns(sig.returns.as_ref(), &generics);
            effects <- sig
                .effects
                .iter()
                .flat_map(|we| &we.effects)
                .map(|effect| self.effect(effect, &generics))
                .collect::<Result<Arc<_>>>();
            let effect = Effect::row(effects.iter(), self.tt);
            return self.tt.insert_function_signature(FunctionSignatureValue {
                type_params,
                params,
                returns,
                effect,
            });
        }
    }
    fn returns(
        &mut self,
        returns: Option<&ast::Returns>,
        generics: &Generics,
    ) -> Result<FunctionReturns> {
        match returns {
            Some(returns) => match returns {
                ast::Returns::Never(_) => Result::new(FunctionReturns::Never),
                ast::Returns::Data(ty) => self.r#type(ty, generics).map(FunctionReturns::Data),
            },
            None => {
                let unit = self.tt.insert_type(TypeEnum::Unit);
                Result::new(FunctionReturns::Data(unit))
            }
        }
    }
    fn function_param<'a>(
        &mut self,
        param: &'a ast::Parameter,
        generics: &Generics<'a>,
    ) -> Result<FunctionParameter> {
        match param {
            ast::Parameter::Data(_, ty) => self.r#type(ty, generics).map(FunctionParameter::Data),
            ast::Parameter::Lambda(decl) => self
                .function_signature(decl, generics)
                .map(FunctionParameter::Lambda),
        }
    }
}
