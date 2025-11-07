use std::{
    collections::{HashMap, VecDeque},
    fmt::Display,
};

use compact_str::{CompactString, format_compact};
use do_notation::m;
use petgraph::{
    algo::kosaraju_scc,
    dot::Dot,
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};

use crate::{
    err::{LucuDiagnostic, Result, SimpleDiagnostic},
    module::{Module, ModuleResolver, UnknownModule},
    stage::{
        lexer::token::{Span, TokenKind},
        parser::{
            Parser,
            ast::{self, Spanned},
            visitor::{Ast, PathKind},
        },
    },
};

fn import_name(path: &ast::String) -> ast::Ident {
    let without_extension = path.0.0.rsplit_once('.').map(|t| t.0).unwrap_or(&path.0.0);
    let end = path.0.1.end - 1 - (path.0.0.len() - without_extension.len()) as u32;

    let ident = without_extension
        .rsplit_once(['/', '\\', ':'])
        .map(|t| t.1)
        .unwrap_or(without_extension);
    let start = path.0.1.start + 1 + (without_extension.len() - ident.len()) as u32;

    ast::Ident(Spanned(ident.into(), Span::new(start, end)))
}

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
    asts: HashMap<NodeIndex, ast::Module>,
    graph: DiGraph<Module, Import>,
}

#[derive(Debug, Default)]
pub struct ModuleScope {
    scope: HashMap<CompactString, NodeIndex>,
    graph: DiGraph<CompactString, PathKind>,
}

impl ModuleScope {
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
    pub fn dot<'a>(&self) -> Dot<'a, &DiGraph<CompactString, PathKind>> {
        Dot::new(&self.graph)
    }
    pub fn from(ast: &ast::Module) -> Result<Self> {
        let mut result = Result::ok();

        let mut graph = DiGraph::new();
        let mut scope = HashMap::new();

        for def in &ast.definitions {
            let name = def.name().map(|name| name.ident.0.0.clone());
            let node = graph.add_node(name.clone().unwrap_or_default());
            if let Some(name) = name {
                scope.entry(name).or_insert(Vec::new()).push(node);
            }
        }

        for (idx, def) in ast.definitions.iter().enumerate() {
            let parent = NodeIndex::new(idx);
            for (name, kind) in def.module_paths() {
                match scope.get(name).map(Vec::as_slice) {
                    Some([child]) => {
                        graph.add_edge(parent, *child, kind);
                    }
                    Some(_) => {}
                    None => todo!("unknown definition"),
                }
            }
        }

        m! {
            _ <- result;
            scope <- scope
                .into_iter()
                .map(|(k, v)| match v.as_slice() {
                    [v] => Result::new((k, *v)),
                    _ => todo!("multiple definitions"),
                })
                .collect::<Result<_>>()
                .or_default();
            return Self { scope, graph };
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
    pub fn ast(&self, idx: NodeIndex) -> Option<&ast::Module> {
        self.asts.get(&idx)
    }
    pub fn module(&self, idx: NodeIndex) -> &Module {
        &self.graph[idx]
    }
    pub fn dot(&self) -> Dot<&DiGraph<Module, Import>> {
        Dot::new(&self.graph)
    }
    pub fn from(resolver: &impl ModuleResolver) -> Result<Self> {
        let mut result = Result::ok();

        let mut asts = HashMap::new();
        let mut graph = DiGraph::new();
        let mut nodes = HashMap::new();

        let mut queue = VecDeque::new();

        {
            let main = resolver.main();
            let contents = resolver
                .contents(&main)
                .expect("ICE: could not find main file");
            let ast = Parser::parse(&main, &contents);
            let node = graph.add_node(main.clone());
            nodes.insert(main, node);

            result += ast.take_value(|ast| queue.push_back((node, ast)));
        }

        while let Some((parent_node, ast)) = queue.pop_front() {
            let parent = graph.node_weight(parent_node).unwrap().clone();

            if let Some(module) = resolver.preamble(&parent) {
                let seen = nodes.contains_key(&module);

                // get graph node, add the edge to it
                let node = *nodes
                    .entry(module.clone())
                    .or_insert_with(|| graph.add_node(module.clone()));
                graph.add_edge(parent_node, node, Import::Implicit);

                // if this is a new node, queue its ast
                if !seen {
                    let source = resolver
                        .contents(&module)
                        .expect("ICE: could not find preamble");
                    result += Parser::parse(&module, &source)
                        .take_value(|ast| queue.push_back((node, ast)))
                }
            }

            for import in &ast.imports {
                let module = Module::from_import(&parent, &import.path.0.0);
                let seen = nodes.contains_key(&module);

                // get identifier and check if valid
                let ident = match &import.ident {
                    Some(ident) => ident.0.0.clone(),
                    None => {
                        let ident = import_name(&import.path);
                        result +=
                            Result::require(TokenKind::is_valid_identifier(&ident.0.0), || {
                                LucuDiagnostic::InvalidIdentifier(SimpleDiagnostic::new(
                                    parent.clone(),
                                    ident.0.1,
                                ))
                            });
                        ident.0.0
                    }
                };

                // get graph node, add the edge to it
                let node = *nodes
                    .entry(module.clone())
                    .or_insert_with(|| graph.add_node(module.clone()));
                graph.add_edge(parent_node, node, Import::Named(ident));

                // if this is a new node, queue its ast
                let resolved = resolve_import(resolver, import, &module, &parent);
                if seen {
                    result += resolved.take_value(|_| ());
                } else {
                    result += resolved
                        .and_then(|source| Parser::parse(&module, &source))
                        .take_value(|ast| queue.push_back((node, ast)))
                }
            }

            asts.insert(parent_node, ast);
        }

        result.map(|_| Self { asts, graph })
    }
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
            SimpleDiagnostic::new(parent.clone(), import.path.0.1),
        )),
        Err(UnknownModule::UnknownFile(file)) => Result::error(LucuDiagnostic::UnknownFile(
            SimpleDiagnostic::new(parent.clone(), import.path.0.1)
                .label(format_compact!("Path resolved to {}", file.display())),
        )),
    }
}
