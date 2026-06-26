use std::sync::Arc;

use compact_str::ToCompactString;

use crate::ast;
use crate::error::Result;
use crate::header::ItemDecl;
use crate::ir::{Block, FunctionDefinition, IR, Instruction, Next};
use crate::module::Module;
use crate::pass::defs::Definitions;
use crate::pass::imports::Imports;
use crate::pass::lower::{HeaderQuery, Lower};
use crate::type_table::{
    FunctionSignature, GenericArgument, GenericParameter, Region, RegionEnum, Term, TypeEnum,
    TypeTable,
};

impl<'a, 'scope> Lower<'a, 'scope> {
    fn ir(&mut self, ir: &IR, ast: &'a ast::Module, defs: &Definitions) -> Result<()> {
        let current = self
            .query
            .header(self.module)
            .expect("ICE: could not query header");
        current
            .items()
            .filter_map(|(name, decl)| {
                // TODO: effect functions
                let &ItemDecl::Function(sig, None, node) = decl else {
                    return None;
                };
                let ast::Item::Function(_, Some((_, def))) = defs.item(node, ast) else {
                    return None;
                };
                Some(self.function(name, sig, def).map(|ir_fun| {
                    let f = ir.push_function(ir_fun);
                    ir.function_map
                        .write()
                        .unwrap()
                        .insert((self.module.clone(), name.into()), f);
                }))
            })
            .collect::<Result<()>>()
    }
    fn function(
        &mut self,
        name: &'scope str,
        sig: FunctionSignature,
        def: &'a ast::FunctionDefinition,
    ) -> Result<FunctionDefinition> {
        println!("hi");
        println!("{}", sig.display(self.tt));
        match def {
            ast::FunctionDefinition::Expression(expression) => todo!(),
            ast::FunctionDefinition::Intrinsic(_) => {
                self.intrinsic_function(name).map(|blocks| todo!())
            }
        }
    }
    fn intrinsic_function(&mut self, name: &'scope str) -> Result<Box<[Block]>> {
        let module = self.module.to_compact_string();
        let fun = match (module.as_str(), name) {
            ("builtin:regions", "ref") => {
                let type_t = self.tt.insert_type(TypeEnum::Generic(GenericParameter {
                    index: 1,
                    apply: None,
                }));
                let type_u = self.tt.insert_type(TypeEnum::Generic(GenericParameter {
                    index: 0,
                    apply: None,
                }));
                let region_static = self.tt.insert_region(RegionEnum::Static);
                let type_ptr_t = self
                    .tt
                    .insert_type(TypeEnum::Pointer(type_t, region_static));
                let type_unit = self.tt.insert_type(TypeEnum::Unit);

                vec![Block {
                    instructions: vec![
                        (type_ptr_t, Instruction::Alloca),
                        (type_t, Instruction::Parameter(0)),
                        (
                            type_unit,
                            Instruction::Store {
                                address: 0,
                                value: 1,
                            },
                        ),
                        (type_unit, Instruction::Parameter(1)),
                        (
                            type_u,
                            Instruction::Call {
                                function: 3,
                                type_args: Arc::new([GenericArgument {
                                    term: Term::Region(region_static),
                                    arity: None,
                                }]),
                                args: Box::new([0]),
                                // TODO: provide effect handler for <read 0 | write 0> ??
                                effects: Box::new([]),
                            },
                        ),
                    ]
                    .into_boxed_slice(),
                    next: Next::Return(4),
                }]
                .into_boxed_slice()
            }
            ("builtin:regions", "alloca") => todo!(),
            _ => todo!("error: unknown intrinsic {}.{}", module.as_str(), name,),
        };
        Result::new(fun)
    }
}

impl IR {
    pub fn lower(
        &self,
        query: &impl HeaderQuery,
        module: &Module,
        ast: &ast::Module,
        imports: &Imports,
        definitions: &Definitions,
        tt: &TypeTable,
    ) -> Result<()> {
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
        lower.ir(self, ast, definitions)
    }
}
