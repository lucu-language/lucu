use std::collections::HashMap;
use std::fmt::Display;

use compact_str::CompactString;
use petgraph::acyclic::Acyclic;
use petgraph::algo::kosaraju_scc;
use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{Data, GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable};

use crate::err::{Problems, Result};
use crate::stage::ast::visit::{Ast, Combine, Visitor};
use crate::stage::ast::{self, visit};

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
    scope: HashMap<CompactString, NodeIndex>,
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
        let module_definition = defs[node.index()];
        match module_definition.parent {
            Some(parent_node) => {
                let parent = self.definition(parent_node, defs);
                &parent.children()[module_definition.index]
            }
            None => &self.definitions[module_definition.index],
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
    pub fn indices(&self) -> impl Iterator<Item = NodeIndex> {
        self.graph.node_indices()
    }
    pub fn get(&self, name: &str) -> Option<NodeIndex> {
        self.scope.get(name).copied()
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
    pub fn from(ast: &ast::Module) -> Result<Self> {
        let mut problems = Problems::ok();

        let mut graph = DiGraph::new();
        let mut scope = HashMap::new();
        let mut defs = Vec::new();

        for (idx, def) in ast.definitions.iter().enumerate() {
            Self::add_definition(&mut graph, &mut scope, &mut defs, def, Definition::top(idx));
        }

        for parent in (0..graph.node_count()).map(NodeIndex::new) {
            let def = ast.definition(parent, &defs);
            let mut names = def.visit(DefinitionPaths);
            ast.remove_generics(parent, &defs, &mut names);

            for name in names {
                if let Some(&[child]) = scope.get(name).map(Vec::as_slice) {
                    graph.update_edge(parent, child, Edge);
                }
            }
        }

        let scope = scope
            .into_iter()
            .map(|(k, v)| match v.as_slice() {
                [v] => (k, *v),
                _ => todo!("multiple definitions"),
            })
            .collect();

        for compound in kosaraju_scc(&graph) {
            match compound.as_slice() {
                &[v] if graph.contains_edge(v, v) => {
                    todo!("Cyclic graph: self-referential!")
                }
                [_] => {}
                _ => todo!("Cyclic graph!"),
            }
        }

        match Acyclic::try_from_graph(graph) {
            Ok(graph) => problems.with(Self { defs, scope, graph }),
            Err(_) => problems.error(),
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
            graph.update_edge(parent, node, Edge);
        }
        for (idx, child) in ast.children().iter().enumerate() {
            Self::add_definition(graph, scope, defs, child, Definition::child(node, idx));
        }
    }
}
