use std::{
    cell::OnceCell,
    collections::HashMap,
    fmt::Display,
    hash::{DefaultHasher, Hash, Hasher},
};

use definitions::Definitions;
use importer::{Import, Imports};
use lexer::{Lexer, token::Token};
use parser::{
    Parser,
    ast::{self},
};
use petgraph::{
    algo::{DfsSpace, has_path_connecting, kosaraju_scc},
    dot::Dot,
    graph::{DiGraph, NodeIndex},
    visit::{Data, EdgeRef, GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable},
};

use crate::{
    err::{HasDiagnostics, LucuDiagnostic, Result},
    module::{Module, ModuleResolver},
};

// stage 1
pub mod lexer;
// stage 2
pub mod parser;
// stage 3
pub mod importer;
// stage 4
pub mod definitions;

#[derive(Debug, Default)]
pub struct Stages {
    module: Module,
    source: Option<String>,

    tokens: OnceCell<Result<Box<[Token]>>>,
    ast: OnceCell<Result<ast::Module>>,
    imports: OnceCell<Result<Imports>>,
    definitions: OnceCell<Result<Definitions>>,
}

impl HasDiagnostics for Stages {
    fn diagnostics(&self) -> impl Iterator<Item = &LucuDiagnostic> {
        self.tokens
            .diagnostics()
            .chain(self.ast.diagnostics())
            .chain(self.imports.diagnostics())
            .chain(self.definitions.diagnostics())
    }
}

impl Stages {
    pub fn new(module: Module, resolver: &impl ModuleResolver) -> Self {
        Self {
            source: resolver.contents(&module),
            module,
            ..Self::default()
        }
    }
    fn reset(&mut self, resolver: &impl ModuleResolver) {
        // reset everything
        *self = Self::new(std::mem::take(&mut self.module), resolver);
    }
    fn reset_imports(&mut self) {
        // reset imports and everything that depends on imports
        self.imports = OnceCell::new();
    }

    pub fn source(&self) -> &str {
        self.source.as_deref().unwrap_or_default()
    }
    pub fn tokens(&self) -> Option<&[Token]> {
        self.tokens
            .get_or_init(|| Result::new(Lexer::new(self.source()).collect()))
            .value()
            .map(|v| &**v)
    }
    pub fn ast(&self) -> Option<&ast::Module> {
        self.ast
            .get_or_init(|| {
                self.tokens()
                    .map(|tokens| Parser::new(&self.module, self.source(), tokens).module())
                    .unwrap_or_default()
            })
            .value()
    }
    pub fn imports(&self, resolver: &impl ModuleResolver) -> Option<&Imports> {
        self.imports
            .get_or_init(|| {
                self.ast()
                    .map(|ast| Imports::from(resolver, &self.module, ast))
                    .unwrap_or_default()
            })
            .value()
    }
    pub fn definitions(&self) -> Option<&Definitions> {
        self.definitions
            .get_or_init(|| {
                self.ast()
                    .map(|ast| Definitions::from(ast))
                    .unwrap_or_default()
            })
            .value()
    }
}

#[derive(Debug, Default)]
struct ModuleCache(HashMap<Module, Stages>);

impl ModuleCache {
    fn get_or_insert(&mut self, resolver: &impl ModuleResolver, module: &Module) -> &mut Stages {
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
    pub fn stages(&self, module: &Module) -> Option<&Stages> {
        self.cache.0.get(module)
    }
    pub fn dot(
        &self,
    ) -> Dot<
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
            self.graph.remove_node(node);
        }
    }
    pub fn insert_or_update(&mut self, resolver: &impl ModuleResolver, module: Module) {
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
                    fn hash<T>(obj: T) -> u64
                    where
                        T: Hash,
                    {
                        let mut hasher = DefaultHasher::new();
                        obj.hash(&mut hasher);
                        hasher.finish()
                    }
                    let stages = self
                        .cache
                        .get_mut(&module)
                        .expect("ICE: module is in node map but has no cache");

                    let old_hash = hash(stages.imports(resolver));
                    stages.reset(resolver);
                    let new_hash = hash(stages.imports(resolver));

                    // in theory this could lead to a hash collision, but we assume these are rare enough
                    if old_hash != new_hash {
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
            let imports = stages.imports(resolver);

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
