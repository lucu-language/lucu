use std::{
    collections::{HashMap, VecDeque},
    fmt::Display,
};

use compact_str::{CompactString, format_compact};
use im::HashSet;
use petgraph::{
    algo::kosaraju_scc,
    dot::Dot,
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};

use crate::{
    err::{LucuDiagnostic, Problems, Result, SimpleDiagnostic},
    module::{Module, ModuleResolver, UnknownModule},
    stage::{
        lexer::token::{Span, TokenKind},
        parser::{
            Parser,
            ast::{self, Name, Spanned},
            visitor::{Ast, PathKind},
        },
    },
};

#[derive(Debug)]
pub enum Import {
    Implicit,
    Named(CompactString),
}

impl Display for Import {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Import::Implicit => Ok(()),
            Import::Named(compact_string) => compact_string.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct ModuleGraph {
    asts: Vec<ast::Module>,
    graph: DiGraph<Module, Import>,
}

#[derive(Debug, Default)]
pub struct ModuleScope<'a> {
    defs: Vec<ModuleDefinition<'a>>,
    scope: HashMap<CompactString, NodeIndex>,
    graph: DiGraph<CompactString, PathKind>,
}

#[derive(Debug, Clone, Copy)]
pub struct ModuleDefinition<'a> {
    parent: Option<NodeIndex>,
    ast: &'a ast::Definition,
}

impl<'a> ModuleDefinition<'a> {
    pub fn top(definition: &'a ast::Definition) -> Self {
        Self {
            ast: definition,
            parent: None,
        }
    }
    pub fn child(parent: NodeIndex, child: &'a ast::Definition) -> Self {
        Self {
            ast: child,
            parent: Some(parent),
        }
    }
}

impl<'a> ModuleScope<'a> {
    pub fn postorder(&self) -> Result<Vec<NodeIndex>> {
        kosaraju_scc(&self.graph.filter_map(
            |_, _| Some(()),
            |_, &p| (p == PathKind::Direct).then_some(()),
        ))
        .iter()
        .map(|v| match v.as_slice() {
            [v] if self.graph.contains_edge(*v, *v) => todo!("Cyclic graph: self-referential!"),
            [v] => Result::new(*v),
            _ => todo!("Cyclic graph!"),
        })
        .collect()
    }
    pub fn dot(&self) -> Dot<&DiGraph<CompactString, PathKind>> {
        Dot::new(&self.graph)
    }
    pub fn from(ast: &'a ast::Module) -> Result<Self> {
        let mut problems = Problems::ok();

        let mut graph = DiGraph::new();
        let mut scope = HashMap::new();
        let mut defs = Vec::new();

        for def in &ast.definitions {
            Self::add_definition(
                &mut graph,
                &mut scope,
                &mut defs,
                ModuleDefinition::top(def),
            );
        }

        for (idx, def) in defs.iter().enumerate() {
            let generics: HashSet<&str> = def
                .ast
                .generics()
                .iter()
                .map(|g| g.name.ident.as_str())
                .collect();

            let parent = NodeIndex::new(idx);
            for (name, kind) in def
                .ast
                .module_paths()
                .into_iter()
                .filter(|(k, _)| !generics.contains(k.as_str()))
            {
                match scope.get(name.as_str()).map(Vec::as_slice) {
                    Some(&[child]) => {
                        if let Some(edge) = graph.find_edge(parent, child) {
                            graph[edge] = graph[edge].min(kind);
                        } else {
                            graph.add_edge(parent, child, kind);
                        }
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

        problems.with(Self { scope, graph, defs })
    }
    fn add_definition(
        graph: &mut DiGraph<CompactString, PathKind>,
        scope: &mut HashMap<CompactString, Vec<NodeIndex>>,
        defs: &mut Vec<ModuleDefinition<'a>>,
        def: ModuleDefinition<'a>,
    ) {
        let name = def.ast.name().map(Name::as_str).map(CompactString::new);
        let node = graph.add_node(name.clone().unwrap_or_default());
        defs.push(def);

        if let Some(name) = name {
            scope.entry(name).or_default().push(node);
        }
        if let Some(parent) = def.parent {
            graph.add_edge(node, parent, PathKind::Direct);
        }
        for child in def.ast.children() {
            Self::add_definition(graph, scope, defs, ModuleDefinition::child(node, child));
        }
    }
}

impl ModuleGraph {
    pub fn postorder(&self) -> Result<Vec<NodeIndex>> {
        kosaraju_scc(&self.graph)
            .iter()
            .map(|v| match v.as_slice() {
                [v] if self.graph.contains_edge(*v, *v) => todo!("Cyclic graph: self-referential!"),
                [v] => Result::new(*v),
                _ => todo!("Cyclic graph!"),
            })
            .collect()
    }
    pub fn imports(&self, idx: NodeIndex) -> impl Iterator<Item = (&Import, NodeIndex)> {
        self.graph
            .edges(idx)
            .map(|edge| (edge.weight(), edge.target()))
    }
    pub fn ast(&self, idx: NodeIndex) -> &ast::Module {
        &self.asts[idx.index()]
    }
    pub fn module(&self, idx: NodeIndex) -> &Module {
        &self.graph[idx]
    }
    pub fn dot(&self) -> Dot<&DiGraph<Module, Import>> {
        Dot::new(&self.graph)
    }
    pub fn from(resolver: &impl ModuleResolver) -> Result<Self> {
        let mut problems = Problems::ok();

        let mut asts = Vec::new();
        let mut graph = DiGraph::new();
        let mut nodes = HashMap::new();

        let mut queue = VecDeque::new();

        {
            let main = resolver.main();
            let source = resolver
                .contents(&main)
                .expect("ICE: could not find main file");

            let ast = problems
                .append(Parser::parse(&main, &source))
                .unwrap_or_default();
            let node = graph.add_node(main.clone());
            nodes.insert(main, node);
            queue.push_back((node, ast));
        }

        while let Some((parent_node, ast)) = queue.pop_front() {
            let parent = graph.node_weight(parent_node).unwrap().clone();

            if let Some(module) = resolver.preamble(&parent) {
                let source = resolver
                    .contents(&module)
                    .expect("ICE: could not find preamble");

                let node = *nodes.entry(module.clone()).or_insert_with(|| {
                    let ast = problems
                        .append(Parser::parse(&module, &source))
                        .unwrap_or_default();
                    let node = graph.add_node(module.clone());
                    queue.push_back((node, ast));
                    node
                });

                graph.add_edge(node, parent_node, Import::Implicit);
            }

            for import in &ast.imports {
                let module = Module::from_import(&parent, import.path.as_str());

                // get identifier and check if valid
                let ident = match &import.ident {
                    Some(ident) => ident.as_str().into(),
                    None => {
                        let ident = Self::import_name(&import.path);
                        problems.append(Problems::require(
                            TokenKind::is_valid_identifier(ident.as_str()),
                            || {
                                LucuDiagnostic::InvalidIdentifier(SimpleDiagnostic::new(
                                    parent.clone(),
                                    ident.span(),
                                ))
                            },
                        ));
                        ident.0.0
                    }
                };

                // adjust graph
                let source = problems
                    .append(Self::resolve_import(resolver, import, &module, &parent))
                    .unwrap_or_default();

                let node = *nodes.entry(module.clone()).or_insert_with(|| {
                    let ast = problems
                        .append(Parser::parse(&module, &source))
                        .unwrap_or_default();
                    let node = graph.add_node(module.clone());
                    queue.push_back((node, ast));
                    node
                });

                graph.add_edge(node, parent_node, Import::Named(ident));
            }

            asts.push(ast);
        }

        problems.with(Self { asts, graph })
    }
    fn resolve_import(
        resolver: &impl ModuleResolver,
        import: &ast::Import,
        module: &Module,
        parent: &Module,
    ) -> Result<String> {
        match resolver.contents(module) {
            Ok(source) => Result::new(source),
            Err(UnknownModule::UnknownLibrary(_)) => Result::error(LucuDiagnostic::UnknownLibrary(
                SimpleDiagnostic::new(parent.clone(), import.path.span()),
            )),
            Err(UnknownModule::UnknownFile(file)) => Result::error(LucuDiagnostic::UnknownFile(
                SimpleDiagnostic::new(parent.clone(), import.path.span())
                    .label(format_compact!("Path resolved to {}", file.display())),
            )),
        }
    }
    fn import_name(path: &ast::String) -> ast::Ident {
        let without_extension = path
            .as_str()
            .rsplit_once('.')
            .map(|t| t.0)
            .unwrap_or(&path.as_str());
        let end = path.span().end - 1 - (path.as_str().len() - without_extension.len()) as u32;

        let ident = without_extension
            .rsplit_once(['/', '\\', ':'])
            .map(|t| t.1)
            .unwrap_or(without_extension);
        let start = path.span().start + 1 + (without_extension.len() - ident.len()) as u32;

        ast::Ident(Spanned(ident.into(), Span::new(start, end)))
    }
}
