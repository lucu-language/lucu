use std::sync::Arc;
use std::{iter, slice};

use compact_str::ToCompactString;
use do_notation::m;
use itertools::Itertools;

use crate::ast;
use crate::ast::inner;
use crate::error::{Problems, Result};
use crate::ir::{
    EffectDef, EffectDefinition, EffectMember, FunctionDef, FunctionDefinition, IR,
    IntrinsicFunction, ItemDef, Parent, StructDefinition, StructMember,
};
use crate::module::Module;
use crate::pass::defs::Definitions;
use crate::pass::imports::Imports;
use crate::span::Spanned;
use crate::type_table::substitute::Substitute;
use crate::type_table::{
    Effect, EffectEnum, FunctionParameter, FunctionReturns, FunctionSignature,
    FunctionSignatureValue, GenericArgument, GenericParameter, IntSize, Integer, Item, Kind,
    KindEnum, Region, RegionEnum, SimpleKind, Term, Type, TypeEnum, TypeTable,
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

pub trait IRQuery {
    fn untyped_ir(&self, module: &Module, tt: &mut TypeTable) -> Option<&IR>;
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
        let decl_problems = self
            .definitions
            .postorder_with_parent(self.ast)
            .map(|(def, parent)| self.declaration(def, parent))
            .collect::<Problems>();
        let def_problems = self
            .definitions
            .postorder(self.ast)
            .map(|def| self.definition(def))
            .collect::<Problems>();
        (decl_problems + def_problems).with(self.ir)
    }
    fn generics<'a>(
        &self,
        params: Option<&Arc<[Kind]>>,
        name: &'a ast::Name,
        base: &Generics<'a>,
    ) -> Generics<'a> {
        match (params, &name.generics) {
            (Some(params), Some(generics)) => {
                assert_eq!(params.len(), generics.len());
                base.pushed(
                    Iterator::zip(generics.iter(), params.iter())
                        .map(|(ast, &kind)| (ast.name.as_str(), kind)),
                )
            }
            (None, None) => base.clone(),
            _ => unreachable!(),
        }
    }
    fn definition(&mut self, def: &ast::Definition) -> Problems {
        let mut problems = Problems::ok();

        match &def.0 {
            inner::Definition::Type(name, def) => {
                if let Some(Spanned(inner::TypeDefinition::Struct(struc), _)) = def {
                    let Some(ItemDef::Struct(kind, idx)) = self.ir.get(name.as_str()) else {
                        return problems;
                    };

                    let generics =
                        self.generics(self.tt[kind].params.as_ref(), name, &Generics::new());
                    let members = problems
                        .append(
                            struc
                                .members
                                .iter()
                                .map(|member| self.struct_member(member, &generics))
                                .collect::<Result<_>>(),
                        )
                        .expect("ICE: empty result when getting struct members");

                    self.ir.realize_struct(idx, StructDefinition { members });
                }
            }
            inner::Definition::Function(decl, def) => {
                if let Some(Spanned(inner::FunctionDefinition::Expression(body), _)) = def {
                    let Some(ItemDef::Function(_, Parent::TopLevel(fun))) =
                        self.ir.get(decl.name.as_str())
                    else {
                        return problems;
                    };

                    self.ir.realize_function(
                        fun,
                        FunctionDefinition::Expression {
                            captures: 0,
                            body: (),
                        },
                    );
                }
            }
            inner::Definition::Effect(name, defs) => {
                if let Some(Spanned(inner::EffectDefinition::Body(body), _)) = defs {
                    let Some(ItemDef::Effect(_, eff)) = self.ir.get(name.as_str()) else {
                        return problems;
                    };

                    let members = body
                        .definitions
                        .iter()
                        .filter_map(|def| {
                            let name = def.name()?;
                            let ItemDef::Function(sig, _) = self.ir.get(name.as_str())? else {
                                return None;
                            };
                            Some(EffectMember {
                                name: name.as_str().to_compact_string(),
                                signature: sig,
                            })
                        })
                        .collect();

                    self.ir
                        .realize_effect(eff, EffectDefinition::Body { members });
                }
            }
        }

        problems
    }
    fn declaration(&mut self, def: &ast::Definition, parent: Option<&ast::Definition>) -> Problems {
        let mut problems = Problems::ok();

        match &def.0 {
            inner::Definition::Type(name, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind = problems.append(self.kind(name, SimpleKind::Type));

                match def {
                    Some(def) => match &def.0 {
                        inner::TypeDefinition::Type(spanned) => {
                            if let Some(kind) = kind {
                                let generics = self.generics(
                                    self.tt[kind].params.as_ref(),
                                    name,
                                    &Generics::new(),
                                );
                                let ty = problems.append(self.r#type(spanned, &generics));
                                if let Some(ty) = ty {
                                    self.ir.insert(
                                        name.as_str(),
                                        ItemDef::Alias(kind, Term::Type(ty)),
                                    );
                                }
                            }
                        }
                        inner::TypeDefinition::Struct(_) => {
                            if let Some(kind) = kind {
                                let struc = self.ir.push_struct();
                                self.ir.insert(name.as_str(), ItemDef::Struct(kind, struc));
                            }
                        }
                        inner::TypeDefinition::Intrinsic => {
                            let ty = problems.append(self.intrinsic_type(name));
                            if let (Some(kind), Some(ty)) = (kind, ty) {
                                self.ir
                                    .insert(name.as_str(), ItemDef::Alias(kind, Term::Type(ty)));
                            }
                        }
                    },
                    None => todo!("error"),
                }
            }
            inner::Definition::Function(decl, def) => match parent {
                Some(parent) => {
                    let Some(name) = parent.name() else {
                        return problems;
                    };
                    let Some(item) = self.ir.get(name.as_str()) else {
                        return problems;
                    };
                    let ItemDef::Effect(kind, effect) = item else {
                        todo!("error")
                    };

                    let generics =
                        self.generics(self.tt[kind].params.as_ref(), name, &Generics::new());
                    let sig = problems.append(self.function_signature(decl, &generics));
                    if let Some(sig) = sig {
                        self.ir.insert(
                            decl.name.as_str(),
                            ItemDef::Function(sig, Parent::Effect(effect)),
                        );
                    }
                }
                None => {
                    let sig = problems.append(self.function_signature(decl, &Generics::new()));
                    match def {
                        Some(def) => match &def.0 {
                            inner::FunctionDefinition::Expression(_) => {
                                if let Some(sig) = sig {
                                    let fun = self.ir.push_function();
                                    self.ir.insert(
                                        decl.name.as_str(),
                                        ItemDef::Function(sig, Parent::TopLevel(fun)),
                                    );
                                }
                            }
                            inner::FunctionDefinition::Intrinsic => {
                                let fun = problems.append(self.intrinsic_function(&decl.name));
                                if let (Some(sig), Some(fun)) = (sig, fun) {
                                    self.ir.insert(
                                        decl.name.as_str(),
                                        ItemDef::Function(sig, Parent::TopLevel(fun)),
                                    );
                                }
                            }
                        },
                        None => todo!("error"),
                    }
                }
            },
            inner::Definition::Effect(name, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind = problems.append(self.kind(name, SimpleKind::Effect));

                match def {
                    Some(def) => match &def.0 {
                        inner::EffectDefinition::Body(_) => {
                            if let Some(kind) = kind {
                                let effect = self.ir.push_effect();
                                self.ir.insert(name.as_str(), ItemDef::Effect(kind, effect));
                            }
                        }
                        inner::EffectDefinition::Alias(effects) => {
                            if let Some(kind) = kind {
                                let generics = self.generics(
                                    self.tt[kind].params.as_ref(),
                                    name,
                                    &Generics::new(),
                                );
                                let effects = problems.append(
                                    effects
                                        .iter()
                                        .map(|path| self.effect(path, &generics))
                                        .collect::<Result<Arc<_>>>(),
                                );
                                if let Some(effects) = effects {
                                    let row = effects
                                        .iter()
                                        .flat_map(|e| match self.tt[*e] {
                                            EffectEnum::Row(ref effects) => effects.iter().copied(),
                                            _ => slice::from_ref(e).iter().copied(),
                                        })
                                        .unique()
                                        .collect::<Arc<_>>();

                                    let effect = match *row {
                                        [single] => single,
                                        _ => self.tt.insert_effect(EffectEnum::Row(row)),
                                    };

                                    self.ir.insert(
                                        name.as_str(),
                                        ItemDef::Alias(kind, Term::Effect(effect)),
                                    );
                                }
                            }
                        }
                        inner::EffectDefinition::Intrinsic => {
                            let eff = problems.append(self.intrinsic_effect(name));
                            if let (Some(kind), Some(eff)) = (kind, eff) {
                                self.ir.insert(name.as_str(), ItemDef::Effect(kind, eff));
                            }
                        }
                    },
                    None => todo!("error"),
                }
            }
        }

        problems
    }
    fn struct_member(
        &mut self,
        member: &ast::StructMember,
        generics: &Generics,
    ) -> Result<StructMember> {
        match &member.0 {
            inner::StructMember::Data(name, ty) => {
                self.r#type(ty, generics).map(|ty| StructMember {
                    name: name.as_str().to_compact_string(),
                    ty,
                })
            }
        }
    }
    fn item(&mut self, path: &ast::Path) -> std::result::Result<(&Module, ItemDef), Problems> {
        let (module, preamble) = match &path.package {
            Some(pkg) => match self.imports.get(pkg.as_str()) {
                Some(module) => match self.query.untyped_ir(module, self.tt) {
                    Some(ir) => ((module, ir), None),
                    None => todo!("recover"),
                },
                None => todo!("error"),
            },
            None => (
                (self.module, &self.ir),
                self.imports.preamble().and_then(|module| {
                    self.query
                        .untyped_ir(module, self.tt)
                        .map(|ir| (module, ir))
                }),
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
        ast: Option<&[ast::GenericArgument]>,
        generics: &Generics,
    ) -> Result<(Kind, Term)> {
        match ast {
            Some(ast) => {
                let kind = self.tt[kind].clone();
                let Some(params) = kind.params else {
                    todo!("error");
                };
                if params.len() != ast.len() {
                    todo!("error");
                }

                let output = self.tt.insert_kind(KindEnum {
                    params: None,
                    output: kind.output,
                });
                Iterator::zip(params.iter().copied(), ast.iter())
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
                        SimpleKind::Effect => todo!(),
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
                    SimpleKind::Constant(_) => todo!(),
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

        self.apply(item_kind, term, path.generics.as_deref(), generics)
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
        match &arg.0 {
            inner::GenericArgument::Path(path) => self.term_path(param, path, &generics),
            inner::GenericArgument::Type(ty) => {
                if self.tt[param] == KindEnum::TYPE {
                    self.r#type(ty, &generics).map(Term::Type)
                } else {
                    todo!("error")
                }
            }
            inner::GenericArgument::Constant(constant) => todo!(),
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
        match &ty.0 {
            inner::Type::Path(path) => {
                let kind = self.tt.insert_kind(KindEnum::TYPE);
                self.term_path(kind, path, generics).map(|path| match path {
                    Term::Type(ty) => ty,
                    _ => panic!("ICE: generic argument of kind Type is not actually a Type"),
                })
            }
            inner::Type::Pointer(ty, region) => m! {
                ty <- self.r#type(ty, generics);
                region <- self.region(region.as_ref().expect("TODO: implied region"), generics);
                return self.tt.insert_type(TypeEnum::Pointer(ty, region));
            },
            inner::Type::PointerSlice(ty, region) => m! {
                ty <- self.r#type(ty, generics);
                region <- self.region(region.as_ref().expect("TODO: implied region"), generics);
                return self.tt.insert_type(TypeEnum::PointerSlice(ty, region));
            },
            inner::Type::PointerSliceNullTerminated(ty, region) => m! {
                ty <- self.r#type(ty, generics);
                region <- self.region(region.as_ref().expect("TODO: implied region"), generics);
                return self.tt.insert_type(TypeEnum::PointerSliceNullTerminated(ty, region));
            },
        }
    }
    fn simple_kind(&mut self, kind: &ast::Kind) -> Result<SimpleKind> {
        match &kind.0 {
            inner::Kind::Type => Result::new(SimpleKind::Type),
            inner::Kind::Effect => Result::new(SimpleKind::Effect),
            inner::Kind::Region => Result::new(SimpleKind::Region),
            // TODO: allow constant with generic type?
            inner::Kind::Constant(ty) => {
                self.r#type(ty, &Generics::new()).map(SimpleKind::Constant)
            }
        }
    }
    fn kind_params(&mut self, name: &ast::Name) -> Result<Option<Arc<[Kind]>>> {
        match &name.generics {
            Some(params) => params
                .iter()
                .map(|param| {
                    match &param.kind {
                        Some(kind) => self.simple_kind(kind),
                        None => Result::new(SimpleKind::Type),
                    }
                    .and_then(|output| self.kind(&param.name, output))
                })
                .collect::<Result<_>>()
                .map(Some),
            None => Result::new(None),
        }
    }
    fn kind(&mut self, name: &ast::Name, output: SimpleKind) -> Result<Kind> {
        self.kind_params(name)
            .map(|params| self.tt.insert_kind(KindEnum { params, output }))
    }

    fn intrinsic_type(&mut self, name: &ast::Name) -> Result<Type> {
        let module = self.module.to_compact_string();
        let ty = match (module.as_str(), name.as_str()) {
            ("builtin:preamble", "u8") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(8))),
            ("builtin:preamble", "u16") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(16))),
            ("builtin:preamble", "u32") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(32))),
            ("builtin:preamble", "u64") => TypeEnum::Integer(Integer::unsigned(IntSize::Exact(64))),
            ("builtin:preamble", "uint") => TypeEnum::Integer(Integer::unsigned(IntSize::Register)),
            ("builtin:preamble", "uptr") => TypeEnum::Integer(Integer::unsigned(IntSize::Address)),
            ("builtin:preamble", "usize") => TypeEnum::Integer(Integer::unsigned(IntSize::Index)),
            ("builtin:preamble", "i8") => TypeEnum::Integer(Integer::signed(IntSize::Exact(8))),
            ("builtin:preamble", "i16") => TypeEnum::Integer(Integer::signed(IntSize::Exact(16))),
            ("builtin:preamble", "i32") => TypeEnum::Integer(Integer::signed(IntSize::Exact(32))),
            ("builtin:preamble", "i64") => TypeEnum::Integer(Integer::signed(IntSize::Exact(64))),
            ("builtin:preamble", "int") => TypeEnum::Integer(Integer::signed(IntSize::Register)),
            ("builtin:preamble", "iptr") => TypeEnum::Integer(Integer::signed(IntSize::Address)),
            ("builtin:preamble", "isize") => TypeEnum::Integer(Integer::signed(IntSize::Index)),
            ("builtin:preamble", "bool") => TypeEnum::Boolean,
            ("builtin:preamble", "unit") => TypeEnum::Unit,
            _ => todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.as_str()
            ),
        };
        Result::new(self.tt.insert_type(ty))
    }
    fn intrinsic_function(&mut self, name: &ast::Name) -> Result<FunctionDef> {
        let module = self.module.to_compact_string();
        let value = match (module.as_str(), name.as_str()) {
            ("builtin:preamble", "len") => IntrinsicFunction::Len,
            ("builtin:preamble", "local") => IntrinsicFunction::Local,
            ("builtin:preamble", "alloca") => IntrinsicFunction::Alloca,
            ("builtin:preamble", "print_str") => IntrinsicFunction::PrintStr,
            ("builtin:preamble", "loop") => IntrinsicFunction::Loop,
            ("builtin:preamble", "unfounded") => IntrinsicFunction::Unfounded,
            _ => todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.as_str()
            ),
        };
        let fun = self.ir.push_function();
        self.ir
            .realize_function(fun, FunctionDefinition::Intrinsic(value));
        Result::new(fun)
    }
    fn intrinsic_effect(&mut self, name: &ast::Name) -> Result<EffectDef> {
        let module = self.module.to_compact_string();
        if !matches!(
            (module.as_str(), name.as_str()),
            ("builtin:preamble", "Div")
                | ("builtin:preamble", "Read")
                | ("builtin:preamble", "Write"),
        ) {
            todo!(
                "error: unknown intrinsic {}.{}",
                module.as_str(),
                name.as_str()
            )
        }
        let eff = self.ir.push_effect();
        self.ir.realize_effect(eff, EffectDefinition::Intrinsic);
        Result::new(eff)
    }
    fn function_signature<'a>(
        &mut self,
        sig: &'a ast::FunctionDeclaration,
        generics: &Generics<'a>,
    ) -> Result<FunctionSignature> {
        m! {
            type_params <- self.kind_params(&sig.name);
            let generics = self.generics(type_params.as_ref(), &sig.name, generics);
            params <- match &sig.parameters {
                Some(params) => params
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
                .flatten()
                .map(|effect| self.effect(effect, &generics))
                .collect::<Result<_>>();
            return self.tt.insert_function_signature(FunctionSignatureValue {
                type_params,
                params,
                returns,
                effects,
            });
        }
    }
    fn returns(
        &mut self,
        returns: Option<&ast::Returns>,
        generics: &Generics,
    ) -> Result<FunctionReturns> {
        match returns {
            Some(returns) => match &returns.0 {
                inner::Returns::Never => Result::new(FunctionReturns::Never),
                inner::Returns::Data(ty) => self.r#type(ty, generics).map(FunctionReturns::Data),
            },
            None => {
                let unit = self.tt.insert_type(TypeEnum::Unit);
                Result::new(FunctionReturns::Data(unit))
            }
        }
    }
    fn function_param<'a>(
        &mut self,
        param: &'a ast::FunctionParameter,
        generics: &Generics<'a>,
    ) -> Result<FunctionParameter> {
        match &param.0 {
            inner::FunctionParameter::Data(_, ty) => {
                self.r#type(ty, generics).map(FunctionParameter::Data)
            }
            inner::FunctionParameter::Lambda(decl) => self
                .function_signature(decl, generics)
                .map(FunctionParameter::Lambda),
        }
    }
}
