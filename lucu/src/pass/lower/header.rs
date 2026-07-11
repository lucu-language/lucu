use std::sync::{Arc, OnceLock};

use compact_str::{CompactString, ToCompactString};
use petgraph::graph::NodeIndex;

use crate::ast;
use crate::error::{Problems, Result};
use crate::header::{
    EffectDecl, EffectMember, HandlerDecl, Header, ItemDecl, StructDecl, StructMember,
};
use crate::module::Module;
use crate::pass::defs::Definitions;
use crate::pass::imports::Imports;
use crate::pass::lower::{HeaderQuery, Lower};
use crate::type_table::{
    Constant, ConstantEnum, Effect, EffectEnum, GenericParameter, IntSize, Integer, Item,
    RegionEnum, SimpleKind, Term, Type, TypeEnum, TypeTable,
};

struct HeaderWIP<'a> {
    query: &'a dyn HeaderQuery,
    module: &'a Module,
    header: &'a Header,
}

impl HeaderQuery for HeaderWIP<'_> {
    fn header(&self, module: &Module) -> Option<&Header> {
        if module == self.module {
            Some(self.header)
        } else {
            self.query.header(module)
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
        let mut used_underscore = false;
        let mut lower = Lower {
            tt,
            module,
            imports,
            query,

            generics: im::HashMap::new(),
            used_underscore: &mut used_underscore,
            next_implicit_region: None,
            implicit_region_offset: 0,
            implicit_effects: None,
        };
        Some(lower.header(ast, definitions))
    }
}

enum Decl {
    Item(CompactString, ItemDecl),
    Handler(HandlerDecl),
}

impl<'a, 'b> Lower<'a, 'b> {
    pub(super) fn header(
        &mut self,
        ast: &'a ast::Module,
        definitions: &Definitions,
    ) -> Result<Header> {
        let mut header = Header::default();

        let mut pass1_problems = Problems::ok();
        let defs = pass1_problems
            .append(
                definitions
                    .nodes_postorder()
                    .map(|node| {
                        let (def, parent) = definitions.item_with_parent(node, ast);
                        let mut l = self.reborrow();
                        let header_wip = HeaderWIP {
                            query: l.query,
                            module: l.module,
                            header: &header,
                        };
                        l.query = &header_wip;
                        l.item_pass1(node, def, parent, &header)
                            .map(|decl| match decl {
                                Some(Decl::Item(name, decl)) => {
                                    header.insert(name, decl.clone());
                                    Some(decl)
                                }
                                Some(Decl::Handler(decl)) => {
                                    header.insert_global_handler(decl);
                                    None
                                }
                                None => None,
                            })
                    })
                    .collect::<Result<Vec<_>>>(),
            )
            .expect("ICE: no definition list");
        assert_eq!(
            defs.len(),
            definitions.nodes().len(),
            "ICE: definition list has different size"
        );

        let pass2_problems = Iterator::zip(
            definitions
                .nodes_postorder()
                .map(|node| definitions.item(node, ast)),
            defs,
        )
        .map(|(def, lower)| {
            let mut l = self.reborrow();
            let header_wip = HeaderWIP {
                query: l.query,
                module: l.module,
                header: &header,
            };
            l.query = &header_wip;
            l.item_pass2(def, lower, &header)
        })
        .collect::<Problems>();

        (pass1_problems + pass2_problems).with(header)
    }
    fn item_pass1(
        &mut self,
        node: NodeIndex,
        item: &'a ast::Item,
        parent: Option<&'a ast::Item>,
        header: &Header,
    ) -> Result<Option<Decl>> {
        let mut problems = Problems::ok();

        match item {
            ast::Item::Type(_, name, def) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let kind = problems.append(self.kind(name.generics.as_ref(), SimpleKind::Type));

                match def {
                    Some((_, ast::TypeDefinition::Type(ast))) => {
                        if let Some(kind) = kind {
                            let decl = self.with_name(
                                0,
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                |l| {
                                    let ty = problems.append(l.r#type(ast));
                                    if let Some(ty) = ty {
                                        let item = ItemDecl::Alias(kind, Term::Type(ty));
                                        Some(Decl::Item(name.ident.as_str().into(), item))
                                    } else {
                                        None
                                    }
                                },
                            );
                            return problems.with(decl);
                        }
                    }
                    Some((_, ast::TypeDefinition::Struct(_))) => {
                        if let Some(kind) = kind {
                            let item = ItemDecl::Struct(kind, Arc::new(OnceLock::new()));
                            return problems
                                .with(Some(Decl::Item(name.ident.as_str().into(), item)));
                        }
                    }
                    Some((_, ast::TypeDefinition::Intrinsic(_))) => {
                        let ty = problems.append(self.intrinsic_type(name));
                        if let (Some(kind), Some(ty)) = (kind, ty) {
                            let item = ItemDecl::Alias(kind, Term::Type(ty));
                            return problems
                                .with(Some(Decl::Item(name.ident.as_str().into(), item)));
                        }
                    }
                    None => todo!("error"),
                }
            }
            ast::Item::Function(decl, def) => match parent {
                Some(parent) => {
                    // TODO: is there a way to get this without looking it up again?
                    let Some(name) = parent.name() else { todo!() };
                    let Some(item) = header.get(name.ident.as_str()) else {
                        todo!()
                    };
                    let &ItemDecl::Effect(kind, _) = item else {
                        todo!("error")
                    };

                    let decl = self.with_name(
                        0,
                        self.tt[kind].params.as_ref(),
                        name.generics.as_ref(),
                        |l| {
                            let sig = problems.append(l.function_signature(decl));
                            if let Some(sig) = sig {
                                let apply = l.dummy_args(kind);
                                let effect = l.tt.insert_effect(EffectEnum::Item(Item {
                                    module: l.module.clone(),
                                    name: name.ident.as_str().to_compact_string(),
                                    apply,
                                }));

                                let item = ItemDecl::Function(sig, Some(effect), node);
                                Some(Decl::Item(decl.name.ident.as_str().into(), item))
                            } else {
                                None
                            }
                        },
                    );
                    return problems.with(decl);
                }
                None => {
                    let sig = problems.append(self.function_signature(decl));
                    if let Some(sig) = sig {
                        let item = ItemDecl::Function(sig, None, node);
                        return problems
                            .with(Some(Decl::Item(decl.name.ident.as_str().into(), item)));
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
                            let item = ItemDecl::Effect(kind, Arc::new(OnceLock::new()));
                            return problems
                                .with(Some(Decl::Item(name.ident.as_str().into(), item)));
                        }
                    }
                    Some((_, ast::EffectDefinition::Alias(effects))) => {
                        if let Some(kind) = kind {
                            let decl = self.with_name(
                                0,
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                |l| {
                                    let effects = problems.append(
                                        effects
                                            .iter()
                                            .map(|path| l.effect(path))
                                            .collect::<Result<Arc<_>>>(),
                                    );
                                    if let Some(effects) = effects {
                                        let effect = Effect::row(effects.iter(), l.tt);
                                        let item = ItemDecl::Alias(kind, Term::Effect(effect));
                                        Some(Decl::Item(name.ident.as_str().into(), item))
                                    } else {
                                        None
                                    }
                                },
                            );
                            return problems.with(decl);
                        }
                    }
                    Some((_, ast::EffectDefinition::Intrinsic(_))) => {
                        let eff = problems.append(self.intrinsic_effect(name));
                        if let (Some(kind), Some(eff)) = (kind, eff) {
                            let item = ItemDecl::Alias(kind, Term::Effect(eff));
                            return problems
                                .with(Some(Decl::Item(name.ident.as_str().into(), item)));
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
                let ty = problems.append(self.r#type(ty));
                let kind = ty.and_then(|ty| {
                    problems.append(self.kind(name.generics.as_ref(), SimpleKind::Constant(ty)))
                });

                match def {
                    Some((_, ast::ConstantDefinition::Constant(constant))) => {
                        if let (Some(ty), Some(kind)) = (ty, kind) {
                            let decl = self.with_name(
                                0,
                                self.tt[kind].params.as_ref(),
                                name.generics.as_ref(),
                                |l| {
                                    let constant = problems.append(l.constant(constant, ty));
                                    if let Some(constant) = constant {
                                        let item = ItemDecl::Alias(kind, Term::Constant(constant));
                                        Some(Decl::Item(name.ident.as_str().into(), item))
                                    } else {
                                        None
                                    }
                                },
                            );
                            return problems.with(decl);
                        }
                    }
                    Some((_, ast::ConstantDefinition::Intrinsic(_))) => {
                        let constant = problems.append(self.intrinsic_constant(name));
                        if let (Some(kind), Some(constant)) = (kind, constant) {
                            let item = ItemDecl::Alias(kind, Term::Constant(constant));
                            return problems
                                .with(Some(Decl::Item(name.ident.as_str().into(), item)));
                        }
                    }
                    None => todo!("error"),
                }
            }
            ast::Item::Handle(_, params, handler) => {
                if let Some(parent) = parent {
                    todo!("error")
                }

                let mut l = self.reborrow();
                let mut implicit_effects = Vec::new();
                l.implicit_effects = Some(&mut implicit_effects);
                let type_params = problems.append(l.kind_params(params.as_ref()));
                let decl = type_params.and_then(|type_params| {
                    let implicit_regions = l.count_implicit_regions(&handler.effect)
                        + handler
                            .with_effects
                            .as_ref()
                            .map(|es| l.count_implicit_regions(es))
                            .unwrap_or(0);
                    l.next_implicit_region = Some(
                        implicit_regions
                            + type_params.as_ref().map(|params| params.len()).unwrap_or(0),
                    );
                    l.implicit_region_offset = 0;

                    l.with_name(
                        implicit_regions,
                        type_params.clone().as_ref(),
                        params.as_ref(),
                        |l| {
                            let effect = problems.append(l.effect(&handler.effect));
                            let with_effects = problems.append(
                                handler
                                    .with_effects
                                    .iter()
                                    .flat_map(|we| &we.effects)
                                    .map(|effect| l.effect(effect))
                                    .collect::<Result<Box<_>>>(),
                            );
                            if let (Some(effect), Some(with_effects)) = (effect, with_effects) {
                                let with_effect = Effect::row(
                                    with_effects.iter().chain(
                                        l.implicit_effects
                                            .as_ref()
                                            .map(|v| &***v)
                                            .unwrap_or_default(),
                                    ),
                                    l.tt,
                                );
                                let handler = HandlerDecl {
                                    type_params,
                                    implicit_regions,
                                    effect,
                                    with_effect,
                                };
                                Some(Decl::Handler(handler))
                            } else {
                                None
                            }
                        },
                    )
                });
                return problems.with(decl);
            }
        }

        problems.with(None)
    }
    fn item_pass2(
        &mut self,
        item: &'a ast::Item,
        partial: Option<ItemDecl>,
        header: &Header,
    ) -> Problems {
        let mut problems = Problems::ok();

        match item {
            ast::Item::Type(_, name, def) => {
                if let Some((_, ast::TypeDefinition::Struct(struc))) = def {
                    let Some(ItemDecl::Struct(kind, idx)) = partial else {
                        return problems;
                    };

                    self.with_name(
                        0,
                        self.tt[kind].params.as_ref(),
                        name.generics.as_ref(),
                        |l| {
                            let members = problems
                                .append(
                                    struc
                                        .members
                                        .inner
                                        .iter()
                                        .map(|member| l.struct_member(member))
                                        .collect::<Result<_>>(),
                                )
                                .expect("ICE: empty result when getting struct members");
                            idx.set(StructDecl { members })
                                .expect("ICE: struct already defined");
                        },
                    )
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
                            let &ItemDecl::Function(sig, _, _) = header.get(name.ident.as_str())?
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
    fn struct_member(&mut self, member: &'a ast::StructMember) -> Result<StructMember> {
        match member {
            ast::StructMember::Data(name, ty) => self.r#type(ty).map(|ty| StructMember {
                name: name.as_str().to_compact_string(),
                ty,
            }),
        }
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
            ("builtin:types", "nullptr") => TypeEnum::NullPointer,
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
}
