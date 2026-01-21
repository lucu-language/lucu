use std::collections::HashMap;
use std::fmt::Display;

use compact_str::CompactString;
use petgraph::acyclic::Acyclic;
use petgraph::algo::kosaraju_scc;
use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{Data, GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable};

use crate::err::{ProblemKind, Problems, Result};
use crate::module::Module;
use crate::span::HasSpan;
use crate::stage::ast::visit::{Ast, Combine, Visitor};
use crate::stage::ast::{self, visit};
use crate::stage::defs::err::MultipleDefinitions;

pub mod err;

#[derive(Debug, Clone, Copy)]
pub struct Edge;

impl Display for Edge {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct DefinitionPaths;
impl Visitor for DefinitionPaths {
    type Output<'a> = im::HashSet<&'a str>;
    fn visit_path(self, path: &ast::Path) -> Self::Output<'_> {
        Self::Output::combine([
            if path.package.is_none() {
                im::HashSet::unit(path.name.as_str())
            } else {
                im::HashSet::new()
            },
            visit::visit_option_vec(&path.generics, self),
        ])
    }
    fn visit_struct(self, _struc: &ast::Struct) -> Self::Output<'_> {
        im::HashSet::new()
    }
    fn visit_effect_body(self, _body: &ast::EffectBody) -> Self::Output<'_> {
        im::HashSet::new()
    }
    fn visit_function_definition(self, _function: &ast::FunctionDefinition) -> Self::Output<'_> {
        im::HashSet::new()
    }
}

#[derive(Debug, Default)]
pub struct Definitions {
    defs: Vec<Definition>,
    graph: Acyclic<DiGraph<CompactString, Edge>>,
}

#[derive(Debug, Clone, Copy)]
pub struct Definition {
    parent: Option<NodeIndex>,
    index: usize,
}

impl Definition {
    pub fn top(definition: usize) -> Self {
        Self {
            index: definition,
            parent: None,
        }
    }
    pub fn child(parent: NodeIndex, child: usize) -> Self {
        Self {
            index: child,
            parent: Some(parent),
        }
    }
}

impl ast::Module {
    fn definition(&self, node: NodeIndex, defs: &[Definition]) -> &ast::Definition {
        self.definition_with_parent(node, defs).0
    }
    fn definition_with_parent(
        &self,
        node: NodeIndex,
        defs: &[Definition],
    ) -> (&ast::Definition, Option<&ast::Definition>) {
        let module_definition = defs[node.index()];
        match module_definition.parent {
            Some(parent_node) => {
                let parent = self.definition(parent_node, defs);
                (&parent.children()[module_definition.index], Some(parent))
            }
            None => (&self.definitions[module_definition.index], None),
        }
    }
    fn remove_generics(
        &self,
        node: NodeIndex,
        defs: &[Definition],
        gens: &mut im::HashSet<&str>,
    ) -> &ast::Definition {
        let module_definition = defs[node.index()];
        let ast = match module_definition.parent {
            Some(parent_node) => {
                let parent = self.remove_generics(parent_node, defs, gens);
                &parent.children()[module_definition.index]
            }
            None => &self.definitions[module_definition.index],
        };
        gens.retain(|&i| !ast.generics().iter().any(|g| g.name.as_str() == i));
        ast
    }
}

impl Definitions {
    pub fn postorder<'a>(&self, ast: &'a ast::Module) -> impl Iterator<Item = &'a ast::Definition> {
        self.graph
            .nodes_iter()
            .rev()
            .map(|idx| ast.definition(idx, &self.defs))
    }
    pub fn postorder_with_parent<'a>(
        &self,
        ast: &'a ast::Module,
    ) -> impl Iterator<Item = (&'a ast::Definition, Option<&'a ast::Definition>)> {
        self.graph
            .nodes_iter()
            .rev()
            .map(|idx| ast.definition_with_parent(idx, &self.defs))
    }
    pub fn indices(&self) -> impl Iterator<Item = NodeIndex> {
        self.graph.node_indices()
    }
    #[expect(clippy::implied_bounds_in_impls)]
    pub fn dot(
        &self,
    ) -> Dot<
        '_,
        impl IntoEdgeReferences
        + IntoNodeReferences
        + GraphProp
        + NodeIndexable
        + Data<NodeWeight = impl Display, EdgeWeight = impl Display>,
    > {
        Dot::new(&self.graph)
    }
    pub fn from(module: &Module, ast: &ast::Module) -> Result<Self> {
        let mut problems = Problems::ok();

        let mut graph = DiGraph::new();
        let mut scope = HashMap::new();
        let mut defs = Vec::new();

        for (idx, def) in ast.definitions.iter().enumerate() {
            Self::add_definition(&mut graph, &mut scope, &mut defs, def, Definition::top(idx));
        }

        // gaze upon this majestic code
        let scope = problems
            .append(
                scope
                    .into_iter()
                    .map(
                        |(k, v)| match v.split_first().expect("ICE: empty def vec") {
                            (&v, []) => Result::new((k, v)),
                            (&first, rest) => Result::error(
                                ProblemKind::MultipleDefinitions(MultipleDefinitions {
                                    name: k,
                                    redefined: rest
                                        .iter()
                                        .map(|&node| {
                                            ast.definition(node, &defs)
                                                .name()
                                                .expect("ICE: named definition has no name")
                                                .ident
                                                .span()
                                        })
                                        .collect(),
                                })
                                .at(
                                    module,
                                    &ast.definition(first, &defs)
                                        .name()
                                        .expect("ICE: named definition has no name")
                                        .ident,
                                ),
                            ),
                        },
                    )
                    .collect::<Result<HashMap<_, _>>>(),
            )
            .unwrap_or_default();

        for parent in (0..graph.node_count()).map(NodeIndex::new) {
            let def = ast.definition(parent, &defs);
            let mut names = def.visit(DefinitionPaths);
            ast.remove_generics(parent, &defs, &mut names);

            for name in names {
                if let Some(&child) = scope.get(name) {
                    graph.update_edge(parent, child, Edge);
                }
            }
        }

        for compound in kosaraju_scc(&graph) {
            match compound.as_slice() {
                &[v] if graph.contains_edge(v, v) => {
                    todo!("Cyclic graph: self-referential!")
                }
                [_] => {}
                _ => todo!("Cyclic graph!"),
            }
        }

        if problems.has_error() {
            problems.error()
        } else {
            let graph = Acyclic::try_from_graph(graph).expect("ICE: cyclic graph passed ssc test");
            problems.with(Self { defs, graph })
        }
    }
    fn add_definition(
        graph: &mut DiGraph<CompactString, Edge>,
        scope: &mut HashMap<CompactString, Vec<NodeIndex>>,
        defs: &mut Vec<Definition>,
        ast: &ast::Definition,
        def: Definition,
    ) {
        let name = ast.name().map(|name| name.as_str()).map(CompactString::new);
        let node = graph.add_node(name.clone().unwrap_or_default());
        defs.push(def);

        if let Some(name) = name {
            scope.entry(name).or_default().push(node);
        }
        if let Some(parent) = def.parent {
            graph.update_edge(node, parent, Edge);
        }
        for (idx, child) in ast.children().iter().enumerate() {
            Self::add_definition(graph, scope, defs, child, Definition::child(node, idx));
        }
    }
}
