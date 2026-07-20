pub mod defs;
pub mod imports;
pub mod lexer;
pub mod lower;
pub mod parser;

use std::collections::HashMap;
use std::fmt::Display;
use std::ops::Deref;
use std::path::PathBuf;
use std::sync::OnceLock;

use petgraph::algo::{DfsSpace, has_path_connecting, kosaraju_scc};
use petgraph::dot::Dot;
use petgraph::graphmap::DiGraphMap;
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
use crate::{ast, mu};

#[derive(Debug, Default)]
pub struct Stages {
    module: Module,
    path: Option<PathBuf>,
    source: Option<String>,

    tokens: Lazy<Box<[Token]>>,
    ast: Lazy<ast::Module>,
    imports: Lazy<Imports>,
    definitions: Lazy<Definitions>,

    header: Lazy<Header>,
    mu: Lazy<mu::Module>,
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

impl<'a> HasProblems for ModuleGraph<'a> {
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
            path: resolver.relative_path(&module),
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
    pub fn ast(&self) -> Option<&ast::Module> {
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
        self.header.get_or_init(|| {
            // TODO: evaluate headers of parent modules first
            // currently, we could go arbitrarily deep into the stack while resolving headers

            let ast = self.ast()?;
            let imports = self.imports()?;
            let definitions = self.definitions()?;
            Some(Header::from(
                graph,
                &self.module,
                ast,
                imports,
                definitions,
                tt,
            ))
        })
    }
    pub fn mu(
        &self,
        graph: &ModuleGraph,
        tt: &TypeTable,
        mu_tt: &mu::table::TypeTable,
        mu_et: &mu::table::ExpressionTable,
    ) -> Option<&mu::Module> {
        self.mu.get_or_init(|| {
            // TODO: evaluate headers of parent modules first
            // currently, we could go arbitrarily deep into the stack while resolving headers

            let source = self.source()?;
            let ast = self.ast()?;
            let imports = self.imports()?;
            let definitions = self.definitions()?;
            Some(mu::Module::from(
                graph,
                &self.module,
                self.path.as_deref(),
                source,
                ast,
                imports,
                definitions,
                tt,
                mu_tt,
                mu_et,
            ))
        })
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
pub struct ModuleGraph<'a> {
    cache: ModuleCache,
    graph: DiGraphMap<&'a Module, Import>,
}

impl<'a> HeaderQuery for ModuleGraph<'a> {
    fn header(&self, module: &Module, tt: &TypeTable) -> Option<&Header> {
        self.stages(module)
            .and_then(|stages| stages.header(self, tt))
    }
}

impl<'a> ModuleGraph<'a> {
    pub fn postorder(&self) -> Result<Vec<&'a Module>> {
        kosaraju_scc(&self.graph)
            .iter()
            .map(|v| match v.as_slice() {
                &[v] if self.graph.contains_edge(v, v) => {
                    todo!("error: cyclic graph: self-referential")
                }
                &[v] => Result::new(v),
                _vs => todo!("error: cyclic graph"),
            })
            .collect()
    }
    pub fn modules(&self) -> impl Iterator<Item = &'a Module> {
        self.graph.nodes()
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
        self.graph.contains_node(module)
    }
    pub fn retain_connected(&mut self, main: &Module) {
        // FIXME: Node indices get changed when a node gets removed!

        if !self.contains(main) {
            // we don't even contain the main module
            // so we can reset all state
            *self = Self::new();
            return;
        }

        let mut space = DfsSpace::new(&self.graph);
        let unconnected = self
            .graph
            .nodes()
            .filter(|&node| !has_path_connecting(&self.graph, main, node, Some(&mut space)))
            .collect::<Vec<_>>();
        for node in unconnected {
            self.graph.remove_node(node);
            self.cache.0.remove(node);
        }
    }
    pub fn insert_or_update(
        &mut self,
        resolver: &impl Modules,
        module: &'a Module,
        interner: impl Fn(&Module) -> &'a Module,
    ) {
        let mut reimport_nodes = Vec::new();

        let exists = resolver.exists(module).is_ok();

        // reset our cache accordingly
        if self.contains(module) {
            if self.cache.exists(module) != exists {
                // reset the imports of modules importing this
                let parent_nodes = self
                    .graph
                    .edges_directed(module, petgraph::Direction::Incoming)
                    .map(|edge| edge.source());
                for parent in parent_nodes {
                    let stages = self
                        .cache
                        .get_mut(parent)
                        .expect("ICE: module is in node map but has no cache");
                    stages.reset_imports();
                    reimport_nodes.push(parent);
                }
            }

            if exists {
                // check if the import list changed
                let stages = self
                    .cache
                    .get_mut(module)
                    .expect("ICE: module is in node map but has no cache");

                let old_imports = stages.resolve_imports(resolver).cloned();
                stages.reset(resolver);
                let new_imports = stages.resolve_imports(resolver);

                if old_imports.as_ref() != new_imports {
                    reimport_nodes.push(module);
                }
            } else {
                // remove from graph
                // if modules actually depend on this, it will be reimported again
                self.cache.remove(module);
                self.graph.remove_node(module);
            }
        } else if exists {
            let node = self.graph.add_node(module);
            reimport_nodes.push(node)
        }

        // (re)import changed nodes
        while let Some(parent) = reimport_nodes.pop() {
            self.clear_edges(parent);

            let stages = self.cache.get_or_insert(resolver, parent);
            let imports = stages.resolve_imports(resolver);

            for (import, child) in imports.into_iter().flatten() {
                let child = interner(child);
                if !self.graph.contains_node(child) {
                    reimport_nodes.push(child);
                }
                if let Some(edge) = self.graph.edge_weight_mut(parent, child) {
                    match (&edge, import.clone()) {
                        (
                            Import::Implicit,
                            Import::Named(compact_string) | Import::Both(compact_string),
                        ) => *edge = Import::Both(compact_string),
                        (
                            Import::Named(compact_string) | Import::Both(compact_string),
                            Import::Implicit,
                        ) => {
                            // TODO: can this be done without cloning?
                            *edge = Import::Both(compact_string.clone())
                        }
                        (Import::Implicit, Import::Implicit) => {
                            todo!("ICE: imported same module implicitly twice")
                        }
                        (
                            Import::Named(_) | Import::Both(_),
                            Import::Named(_) | Import::Both(_),
                        ) => todo!("ICE: imported same module twice"),
                    }
                } else {
                    self.graph.add_edge(parent, child, import.clone());
                }
            }
        }
    }
    fn clear_edges(&mut self, node: &'a Module) {
        while let Some((a, b, _)) = self.graph.edges(node).next() {
            self.graph.remove_edge(a, b);
        }
    }
}
