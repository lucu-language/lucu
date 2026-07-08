pub mod defs;
pub mod imports;
pub mod lexer;
pub mod lower;
pub mod parser;

use std::collections::HashMap;
use std::fmt::Display;
use std::ops::Deref;
use std::sync::OnceLock;

use petgraph::algo::{DfsSpace, has_path_connecting, kosaraju_scc};
use petgraph::dot::Dot;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{
    Data, EdgeRef, GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable,
};

use crate::error::{HasProblems, Problem, Result};
use crate::header::Header;
use crate::module::{Module, Modules};
use crate::pass::defs::Definitions;
use crate::pass::imports::{Import, Imports};
use crate::pass::lexer::Lexer;
use crate::pass::lower::HeaderQuery;
use crate::pass::parser::Parser;
use crate::tokens::Token;
use crate::type_table::TypeTable;

#[derive(Debug, Default)]
pub struct Stages {
    module: Module,
    source: Option<String>,

    tokens: Lazy<Box<[Token]>>,
    ast: Lazy<crate::ast::Module>,
    imports: Lazy<Imports>,
    definitions: Lazy<Definitions>,

    header: Lazy<Header>,
}

impl HasProblems for Stages {
    fn problems(&self) -> impl Iterator<Item = &Problem> {
        self.tokens
            .problems()
            .chain(self.ast.problems())
            .chain(self.imports.problems())
            .chain(self.definitions.problems())
    }
}

impl HasProblems for ModuleGraph {
    fn problems(&self) -> impl Iterator<Item = &Problem> {
        self.cache.0.values().flat_map(HasProblems::problems)
    }
}

#[derive(Debug)]
struct Lazy<T>(OnceLock<Result<T>>);

impl<T> Default for Lazy<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> HasProblems for Lazy<T> {
    fn problems(&self) -> impl Iterator<Item = &Problem> {
        self.0.get().into_iter().flat_map(Result::problems)
    }
}

impl<T> Lazy<T> {
    const fn new() -> Self {
        Self(OnceLock::new())
    }
    fn get_or_init(&self, f: impl FnOnce() -> Option<Result<T>>) -> Option<&T> {
        match self.0.get() {
            Some(t) => t.value(),
            None => {
                let t = f()?;
                self.0.get_or_init(|| t).value()
            }
        }
    }
    fn get(&self) -> Option<&T> {
        self.0.get().and_then(Result::value)
    }
}

impl Stages {
    pub fn new(module: Module, resolver: &impl Modules) -> Self {
        Self {
            source: resolver.contents(&module),
            module,
            ..Self::default()
        }
    }
    fn reset(&mut self, resolver: &impl Modules) {
        // reset everything
        *self = Self::new(std::mem::take(&mut self.module), resolver);
    }
    fn reset_imports(&mut self) {
        // reset imports and everything that depends on imports
        self.imports = Lazy::new();
        self.header = Lazy::new();
    }
    fn resolve_imports(&self, resolver: &impl Modules) -> Option<&Imports> {
        self.imports.get_or_init(|| {
            let ast = self.ast()?;
            Some(Imports::from(resolver, &self.module, ast))
        })
    }

    pub fn source(&self) -> Option<&str> {
        self.source.as_deref()
    }
    pub fn tokens(&self) -> Option<&[Token]> {
        self.tokens
            .get_or_init(|| {
                let source = self.source()?;
                Some(Result::new(Lexer::new(source).collect()))
            })
            .map(Deref::deref)
    }
    pub fn ast(&self) -> Option<&crate::ast::Module> {
        self.ast.get_or_init(|| {
            let source = self.source()?;
            let tokens = self.tokens()?;
            Some(Parser::new(&self.module, source, tokens).module())
        })
    }
    pub fn imports(&self) -> Option<&Imports> {
        self.imports.get()
    }
    pub fn definitions(&self) -> Option<&Definitions> {
        self.definitions.get_or_init(|| {
            let ast = self.ast()?;
            Some(Definitions::from(&self.module, ast))
        })
    }

    pub fn header(&self, graph: &ModuleGraph, tt: &TypeTable) -> Option<&Header> {
        let ast = self.ast()?;
        let imports = self.imports()?;
        let definitions = self.definitions()?;
        self.header
            .get_or_init(|| Header::from(graph, &self.module, ast, imports, definitions, tt))
    }
}

#[derive(Debug, Default)]
struct ModuleCache(HashMap<Module, Stages>);

impl ModuleCache {
    fn get_or_insert(&mut self, resolver: &impl Modules, module: &Module) -> &mut Stages {
        self.0
            .entry(module.clone())
            .or_insert_with(|| Stages::new(module.clone(), resolver))
    }
    fn get_mut(&mut self, module: &Module) -> Option<&mut Stages> {
        self.0.get_mut(module)
    }
    fn remove(&mut self, module: &Module) {
        self.0.remove(module);
    }
    fn exists(&self, module: &Module) -> bool {
        self.0
            .get(module)
            .is_some_and(|stages| stages.source.is_some())
    }
}

#[derive(Debug, Default)]
pub struct ModuleGraph {
    nodes: HashMap<Module, NodeIndex>,
    cache: ModuleCache,
    graph: DiGraph<Module, Import>,
}

impl HeaderQuery for ModuleGraph {
    fn header(&self, module: &Module) -> Option<&Header> {
        self.stages(module).and_then(|stages| stages.header.get())
    }
}

impl ModuleGraph {
    pub fn postorder(&self) -> Result<Vec<&Module>> {
        kosaraju_scc(&self.graph)
            .iter()
            .map(|v| match v.as_slice() {
                &[v] if self.graph.contains_edge(v, v) => {
                    todo!("Cyclic graph: self-referential!")
                }
                &[v] => Result::new(&self.graph[v]),
                _ => todo!("Cyclic graph!"),
            })
            .collect()
    }
    pub fn modules(&self) -> impl Iterator<Item = &Module> {
        self.graph.node_weights()
    }
    pub fn stages(&self, module: &Module) -> Option<&Stages> {
        self.cache.0.get(module)
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
    pub fn new() -> Self {
        Self::default()
    }
    pub fn contains(&self, module: &Module) -> bool {
        self.nodes.contains_key(module)
    }
    pub fn retain_connected(&mut self, main: &Module) {
        // FIXME: Node indices get changed when a node gets removed!

        let Some(&root) = self.nodes.get(main) else {
            // we don't even contain the main module
            // so we can reset all state
            *self = Self::new();
            return;
        };

        let mut space = DfsSpace::new(&self.graph);
        let unconnected = self
            .graph
            .node_indices()
            .filter(|&node| !has_path_connecting(&self.graph, root, node, Some(&mut space)))
            .collect::<Vec<_>>();
        for node in unconnected {
            let module = self
                .graph
                .remove_node(node)
                .expect("ICE: graph node index has no node");
            self.nodes.remove(&module);
            self.cache.0.remove(&module);
        }
    }
    pub fn insert_or_update(&mut self, resolver: &impl Modules, module: Module) {
        let mut reimport_nodes = Vec::new();

        let exists = resolver.exists(&module).is_ok();

        // reset our cache accordingly
        match self.nodes.get(&module).copied() {
            Some(node) => {
                if self.cache.exists(&module) != exists {
                    // reset the imports of modules importing this
                    let parent_nodes = self
                        .graph
                        .edges_directed(node, petgraph::Direction::Incoming)
                        .map(|edge| edge.source());
                    for parent_node in parent_nodes {
                        let parent = &self.graph[parent_node];
                        let stages = self
                            .cache
                            .get_mut(parent)
                            .expect("ICE: module is in node map but has no cache");
                        stages.reset_imports();
                        reimport_nodes.push(parent_node);
                    }
                }

                if exists {
                    // check if the import list changed
                    let stages = self
                        .cache
                        .get_mut(&module)
                        .expect("ICE: module is in node map but has no cache");

                    let old_imports = stages.resolve_imports(resolver).cloned();
                    stages.reset(resolver);
                    let new_imports = stages.resolve_imports(resolver);

                    if old_imports.as_ref() != new_imports {
                        reimport_nodes.push(node);
                    }
                } else {
                    // remove from graph
                    // if modules actually depend on this, it will be reimported again
                    self.nodes.remove(&module);
                    self.cache.remove(&module);
                    self.graph.remove_node(node);
                }
            }
            None if exists => {
                let node = self.graph.add_node(module.clone());
                self.nodes.insert(module, node);
                reimport_nodes.push(node)
            }
            None => {}
        }

        // (re)import changed nodes
        while let Some(parent_node) = reimport_nodes.pop() {
            self.clear_edges(parent_node);

            let parent = self.graph.node_weight(parent_node).unwrap().clone();
            let stages = self.cache.get_or_insert(resolver, &parent);
            let imports = stages.resolve_imports(resolver);

            for (import, child) in imports.into_iter().flatten() {
                let child_node = *self.nodes.entry(child.clone()).or_insert_with(|| {
                    let child_node = self.graph.add_node(child.clone());
                    reimport_nodes.push(child_node);
                    child_node
                });
                self.graph.add_edge(parent_node, child_node, import.clone());
            }
        }
    }
    fn clear_edges(&mut self, node: NodeIndex) {
        while let Some(edge) = self.graph.edges(node).next() {
            self.graph.remove_edge(edge.id());
        }
    }
}
