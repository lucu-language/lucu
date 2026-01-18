use std::iter;
use std::sync::Arc;

use compact_str::ToCompactString;
use do_notation::m;

use crate::err::{Problems, Result};
use crate::ir::untyped::{
    GenericArgument, GenericParameter, IR, IntSize, Integer, Item, Kind, KindEnum, KindStruct, Region, RegionEnum, StructMember, Substitute, Term, Type, TypeEnum, Untyped
};
use crate::module::Module;
use crate::span::Spanned;
use crate::stage::ast::inner;
use crate::stage::defs::Definitions;
use crate::stage::imports::Imports;
use crate::stage::{ModuleGraph, ast};

struct Lower<'a> {
    ir: &'a mut IR,
    module: &'a Module,

    ast: &'a ast::Module,
    imports: &'a Imports,
    definitions: &'a Definitions,

    graph: &'a ModuleGraph,
    untyped: Untyped,
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

impl Untyped {
    pub fn from(graph: &ModuleGraph, module: &Module, ir: &mut IR) -> Option<Result<Self>> {
        let stages = graph.stages(module)?;

        let ast = stages.ast()?;
        let imports = stages.imports()?;
        let definitions = stages.definitions()?;

        let lower = Lower {
            ir,
            module,
            ast,
            imports,
            definitions,
            graph,
            untyped: Untyped::default(),
        };
        Some(lower.module())
    }
}

impl Lower<'_> {
    fn module(mut self) -> Result<Untyped> {
        let decl_problems = self
            .definitions
            .postorder(self.ast)
            .map(|def| self.declaration(def))
            .collect::<Problems>();
        let def_problems = self
            .definitions
            .postorder(self.ast)
            .map(|def| self.definition(def))
            .collect::<Problems>();
        (decl_problems + def_problems).with(self.untyped)
    }
    fn generics<'a>(&self, kind: Kind, name: &'a ast::Name, base: &Generics<'a>) -> Generics<'a> {
        match (&self.ir[kind].params, &name.generics) {
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
                    let Some(&Item::Struct(kind, _)) = self.untyped.items.get(name.as_str()) else {
                        unreachable!();
                    };
                    let generics = self.generics(kind, name, &Generics::new());
                    let members = problems.append(
                        struc
                            .members
                            .iter()
                            .map(|member| self.struct_member(member, &generics))
                            .collect::<Result<_>>(),
                    );
                    let Some(Item::Struct(_, ptr)) = self.untyped.items.get_mut(name.as_str())
                    else {
                        unreachable!();
                    };
                    *ptr = members;
                }
            }
            inner::Definition::Function(_, _) => {
                // TODO
            }
            inner::Definition::Effect(_, _) => {
                // TODO
            }
        }

        problems
    }
    fn declaration(&mut self, def: &ast::Definition) -> Problems {
        let mut problems = Problems::ok();

        match &def.0 {
            inner::Definition::Type(name, def) => {
                let kind = problems.append(self.item_kind(name, None));

                match def {
                    Some(def) => match &def.0 {
                        inner::TypeDefinition::Type(spanned) => {
                            if let Some(kind) = kind {
                                let generics = self.generics(kind, name, &Generics::new());
                                let ty = problems.append(self.r#type(spanned, &generics));
                                if let Some(ty) = ty {
                                    self.untyped.items.insert(
                                        name.as_str().to_compact_string(),
                                        Item::Alias(kind, Term::Type(ty)),
                                    );
                                }
                            }
                        }
                        inner::TypeDefinition::Struct(_) => {
                            if let Some(kind) = kind {
                                self.untyped.items.insert(
                                    name.as_str().to_compact_string(),
                                    Item::Struct(kind, None),
                                );
                            }
                        }
                        inner::TypeDefinition::Intrinsic => {
                            let ty = problems.append(self.intrinsic_type(name));
                            if let (Some(kind), Some(ty)) = (kind, ty) {
                                self.untyped.items.insert(
                                    name.as_str().to_compact_string(),
                                    Item::Alias(kind, Term::Type(ty)),
                                );
                            }
                        }
                    },
                    None => todo!("error"),
                }
            }
            inner::Definition::Function(decl, _) => {
                // TODO
                // FIXME: could also be an effect function
                self.untyped
                    .items
                    .insert(decl.name.as_str().to_compact_string(), Item::Function);
            }
            inner::Definition::Effect(name, _) => {
                // TODO
                self.untyped
                    .items
                    .insert(name.as_str().to_compact_string(), Item::Effect);
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
    fn item(&mut self, path: &ast::Path) -> std::result::Result<(&Module, &Item), Problems> {
        let (module, preamble) = match &path.package {
            Some(pkg) => match self.imports.get(pkg.as_str()) {
                Some(module) => match self
                    .graph
                    .stages(module)
                    .and_then(|stages| stages.untyped_ir(self.graph, self.ir))
                {
                    Some(untyped) => ((module, untyped), None),
                    None => todo!("recover"),
                },
                None => todo!("error"),
            },
            None => (
                (self.module, &self.untyped),
                self.imports.preamble().and_then(|module| {
                    self.graph.stages(module).and_then(|stages| {
                        stages
                            .untyped_ir(self.graph, self.ir)
                            .map(|untyped| (module, untyped))
                    })
                }),
            ),
        };

        for (module, untyped) in iter::once(module).chain(preamble) {
            if let Some(item) = untyped.items.get(path.name.as_str()) {
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
                let kind = self.ir[kind].clone();
                let Some(params) = kind.params else {
                    todo!("error");
                };
                if params.len() != ast.len() {
                    todo!("error");
                }

                let output = self.ir.insert_kind(KindStruct {
                    params: None,
                    output: kind.output,
                });
                Iterator::zip(params.iter().copied(), ast.iter())
                    .map(|(param, arg)| self.generic_argument(param, arg, generics))
                    .collect::<Result<Arc<_>>>()
                    .map(|args| (output, term.subst(self.ir, 0, &args)))
            }
            None => Result::new((kind, term)),
        }
    }
    fn dummy_args(&mut self, kind: Kind) -> Option<Arc<[GenericArgument]>> {
        self.ir[kind].params.clone().map(|params| {
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
                    let term = match self.ir[kind].output {
                        KindEnum::Type => Term::Type(self.ir.insert_type(TypeEnum::Generic(param))),
                        KindEnum::Effect => todo!(),
                        KindEnum::Region => {
                            Term::Region(self.ir.insert_region(RegionEnum::Generic(param)))
                        }
                        KindEnum::Constant(_) => todo!(),
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
                let term = match self.ir[kind].output {
                    KindEnum::Type => Term::Type(self.ir.insert_type(TypeEnum::Generic(param))),
                    KindEnum::Effect => todo!(),
                    KindEnum::Region => {
                        Term::Region(self.ir.insert_region(RegionEnum::Generic(param)))
                    }
                    KindEnum::Constant(_) => todo!(),
                };
                (kind, term)
            } else {
                // Module Item
                let (module, item) = match self.item(path) {
                    Ok((module, item)) => (module, item),
                    Err(problems) => return problems.with(todo!("recovery value")),
                };
                match *item {
                    Item::Alias(item_kind, term) => (item_kind, term),
                    Item::Struct(item_kind, _) => {
                        let module = module.clone();
                        let generics = self.dummy_args(item_kind);
                        let base = self.ir.insert_type(TypeEnum::Struct(
                            module,
                            path.name.as_str().to_compact_string(),
                            generics,
                        ));
                        (item_kind, Term::Type(base))
                    }
                    Item::Effect => todo!(),
                    Item::EffectFunction => todo!("error"),
                    Item::Function => todo!("error"),
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
        let arity = self.ir[param].params.as_ref().map(|params| params.len());
        let generics = generics.shifted(arity.unwrap_or(0));
        match &arg.0 {
            inner::GenericArgument::Path(path) => self.term_path(param, path, &generics),
            inner::GenericArgument::Type(ty) => {
                if self.ir[param] == KindStruct::TYPE {
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
        let kind = self.ir.insert_kind(KindStruct::REGION);
        self.term_path(kind, region, generics)
            .map(|path| match path {
                Term::Region(region) => region,
                _ => panic!("ICE: generic argument of kind Region is not actually a Region"),
            })
    }
    fn r#type(&mut self, ty: &ast::Type, generics: &Generics) -> Result<Type> {
        match &ty.0 {
            inner::Type::Path(path) => {
                let kind = self.ir.insert_kind(KindStruct::TYPE);
                self.term_path(kind, path, generics).map(|path| match path {
                    Term::Type(ty) => ty,
                    _ => panic!("ICE: generic argument of kind Type is not actually a Type"),
                })
            }
            inner::Type::Pointer(ty, region) => m! {
                ty <- self.r#type(ty, generics);
                region <- self.region(region.as_ref().expect("TODO: implied region"), generics);
                return self.ir.insert_type(TypeEnum::Pointer(ty, region));
            },
            inner::Type::Slice(ty, region) => m! {
                ty <- self.r#type(ty, generics);
                region <- self.region(region.as_ref().expect("TODO: implied region"), generics);
                return self.ir.insert_type(TypeEnum::Slice(ty, region));
            },
        }
    }
    fn kind(&mut self, kind: &ast::Kind) -> Result<KindEnum> {
        match &kind.0 {
            inner::Kind::Type => Result::new(KindEnum::Type),
            inner::Kind::Effect => Result::new(KindEnum::Effect),
            inner::Kind::Region => Result::new(KindEnum::Region),
            // TODO: allow constant with generic type?
            inner::Kind::Constant(ty) => self.r#type(ty, &Generics::new()).map(KindEnum::Constant),
        }
    }
    fn item_kind(&mut self, name: &ast::Name, output: Option<&ast::Kind>) -> Result<Kind> {
        match output {
            Some(kind) => self.kind(kind),
            None => Result::new(KindEnum::Type),
        }
        .and_then(|output| match &name.generics {
            Some(params) => params
                .iter()
                .map(|param| self.item_kind(&param.name, param.kind.as_ref()))
                .collect::<Result<_>>()
                .map(|params| {
                    self.ir.insert_kind(KindStruct {
                        params: Some(params),
                        output,
                    })
                }),
            None => Result::new(self.ir.insert_kind(KindStruct {
                params: None,
                output,
            })),
        })
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
            _ => todo!("error"),
        };
        Result::new(self.ir.insert_type(ty))
    }
}
