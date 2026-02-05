use std::collections::HashMap;
use std::fmt::Display;

use compact_str::CompactString;
use petgraph::acyclic::Acyclic;
use petgraph::algo::kosaraju_scc;
use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{Data, GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable};

use crate::ast;
use crate::ast::visit::{Ast, Combine, Visitor, visit_option};
use crate::error::{ProblemKind, Problems, Result};
use crate::module::Module;
use crate::pass::defs::err::MultipleDefinitions;
use crate::span::HasSpan;

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
            visit_option(&path.generics, self, Visitor::visit),
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
    defs: Vec<Item>,
    graph: DiGraph<CompactString, Edge>,
    postorder: Box<[NodeIndex]>,
}

#[derive(Debug, Clone, Copy)]
pub struct Item {
    parent: Option<NodeIndex>,
    index: usize,
}

impl Item {
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
    fn item(&self, node: NodeIndex, defs: &[Item]) -> &ast::Item {
        self.item_with_parent(node, defs).0
    }
    fn item_with_parent(&self, node: NodeIndex, defs: &[Item]) -> (&ast::Item, Option<&ast::Item>) {
        let module_definition = defs[node.index()];
        match module_definition.parent {
            Some(parent_node) => {
                let parent = self.item(parent_node, defs);
                (
                    &parent.children().elements[module_definition.index].0,
                    Some(parent),
                )
            }
            None => (&self.items.elements[module_definition.index].0, None),
        }
    }
    fn remove_generics(
        &self,
        node: NodeIndex,
        defs: &[Item],
        gens: &mut im::HashSet<&str>,
    ) -> &ast::Item {
        let module_definition = defs[node.index()];
        let ast = match module_definition.parent {
            Some(parent_node) => {
                let parent = self.remove_generics(parent_node, defs, gens);
                &parent.children().elements[module_definition.index].0
            }
            None => &self.items.elements[module_definition.index].0,
        };
        gens.retain(|&i| !ast.generics().iter().any(|g| g.ident().as_str() == i));
        ast
    }
}

impl Definitions {
    pub fn postorder<'a>(&self, ast: &'a ast::Module) -> impl Iterator<Item = &'a ast::Item> {
        self.postorder
            .iter()
            .copied()
            .map(|idx| ast.item(idx, &self.defs))
    }
    pub fn postorder_with_parent<'a>(
        &self,
        ast: &'a ast::Module,
    ) -> impl Iterator<Item = (&'a ast::Item, Option<&'a ast::Item>)> {
        self.postorder
            .iter()
            .copied()
            .map(|idx| ast.item_with_parent(idx, &self.defs))
    }
    pub fn indices(&self) -> impl ExactSizeIterator<Item = NodeIndex> {
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

        for (idx, def) in ast.items.iter().enumerate() {
            Self::add_item(&mut graph, &mut scope, &mut defs, def, Item::top(idx));
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
                                            ast.item(node, &defs)
                                                .name()
                                                .expect("ICE: named definition has no name")
                                                .ident
                                                .span()
                                        })
                                        .collect(),
                                })
                                .at(
                                    module,
                                    &ast.item(first, &defs)
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
            let def = ast.item(parent, &defs);
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
            problems.with(Self {
                defs,
                postorder: graph.nodes_iter().rev().collect(),
                graph: graph.into_inner(),
            })
        }
    }
    fn add_item(
        graph: &mut DiGraph<CompactString, Edge>,
        scope: &mut HashMap<CompactString, Vec<NodeIndex>>,
        defs: &mut Vec<Item>,
        ast: &ast::Item,
        def: Item,
    ) {
        let name = ast.name().map(|name| name.ident.value.clone());
        let node = graph.add_node(name.clone().unwrap_or_default());
        defs.push(def);

        if let Some(name) = name {
            scope.entry(name).or_default().push(node);
        }
        if let Some(parent) = def.parent {
            graph.update_edge(node, parent, Edge);
        }
        for (idx, child) in ast.children().iter().enumerate() {
            Self::add_item(graph, scope, defs, child, Item::child(node, idx));
        }
    }
}
