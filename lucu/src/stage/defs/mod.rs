use std::collections::{HashMap, HashSet};
use std::fmt::Display;

use compact_str::CompactString;
use petgraph::acyclic::Acyclic;
use petgraph::algo::kosaraju_scc;
use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{Data, GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable};

use crate::err::{Problems, Result};
use crate::stage::ast;
use crate::stage::ast::visit::{Ast, Visitor};

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
    type Output<'a> = im::Vector<&'a ast::Ident>;
    fn visit_path(self, path: &ast::Path) -> Self::Output<'_> {
        if path.package.is_none() {
            im::Vector::unit(&path.name)
        } else {
            im::Vector::new()
        }
    }
    fn visit_function(self, function: &ast::Function) -> Self::Output<'_> {
        // function definitions may have their own scopes,
        // so checking those is out of scope (pun intended) for this visitor
        function.declaration.visit(self)
    }
    fn visit_struct(self, _struc: &ast::Struct) -> Self::Output<'_> {
        // everything inside a struct definition is an *indirect* reference,
        // as these references are allowed to be mutually recursive
        im::Vector::new()
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
}

impl Definitions {
    pub fn spans<'a>(&self, ast: &'a ast::Module) -> impl Iterator<Item = &'a ast::Definition> {
        self.postorder().map(|idx| ast.definition(idx, &self.defs))
    }
    pub fn postorder(&self) -> impl Iterator<Item = NodeIndex> {
        self.graph.nodes_iter().rev()
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
            let generics: HashSet<&str> = def
                .generics()
                .iter()
                .map(|g| g.name.ident.as_str())
                .collect();

            for name in def
                .visit(DefinitionPaths)
                .into_iter()
                .filter(|ident| !generics.contains(ident.as_str()))
            {
                match scope.get(name.as_str()).map(Vec::as_slice) {
                    Some(&[child]) => {
                        graph.update_edge(parent, child, Edge);
                    }
                    Some(_) => {}
                    None => todo!("unknown definition"),
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
        let name = ast.name().map(ast::Name::as_str).map(CompactString::new);
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
