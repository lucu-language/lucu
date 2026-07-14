use std::collections::HashMap;
use std::fmt::Display;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::OnceLock;

use lucu::error::{Diagnostic as _, HasProblems, ProblemLevel, Problems};
use lucu::module::{Libraries, Library, LibraryDir, Module, Modules, UnknownModule, import_name};
use lucu::pass::ModuleGraph;
use lucu::span::HasSpan;
use lucu::tokens::is_valid_identifier;
use lucu::type_table::TypeTable;
use tokio::sync::RwLock;
use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::ls_types::{
    Diagnostic, DiagnosticOptions, DiagnosticRelatedInformation, DiagnosticServerCapabilities,
    DiagnosticSeverity, DidChangeTextDocumentParams, DidChangeWorkspaceFoldersParams,
    DidCloseTextDocumentParams, DidOpenTextDocumentParams, DocumentDiagnosticParams,
    DocumentDiagnosticReport, DocumentDiagnosticReportResult, FullDocumentDiagnosticReport,
    InitializeParams, InitializeResult, InitializedParams, InlayHint, InlayHintLabel,
    InlayHintParams, Location, MessageType, NumberOrString, OneOf, Position, PositionEncodingKind,
    Range, RelatedFullDocumentDiagnosticReport, ServerCapabilities, TextDocumentSyncCapability,
    TextDocumentSyncKind, Uri, WorkDoneProgressOptions,
};
use tower_lsp_server::{Client, LanguageServer, LspService, Server};

struct Backend {
    workspaces: RwLock<HashMap<Uri, Workspace>>,
    type_table: TypeTable,
    client: Client,
}

#[derive(Debug)]
struct WorkspaceFiles {
    root: PathBuf,
    libraries: HashMap<Library, LibraryDir>,
    open: HashMap<Module, String>,
}

impl Libraries for WorkspaceFiles {
    fn path(&self, library: &Library) -> std::result::Result<PathBuf, UnknownModule> {
        Libraries::path(&self.libraries, library)
    }
    fn relative_path(&self, library: &Library) -> Option<PathBuf> {
        let library_dir = Libraries::path(self, library).ok();
        library_dir.and_then(|lib| lib.strip_prefix(&self.root).ok().map(Path::to_path_buf))
    }
    fn preamble(&self, library: &Library) -> Option<Module> {
        Libraries::preamble(&self.libraries, library)
    }
}

impl Modules for WorkspaceFiles {
    fn libraries(&self) -> &impl Libraries {
        self
    }
    fn exists(&self, module: &Module) -> std::result::Result<(), UnknownModule> {
        match self.open.get(module) {
            Some(_) => Ok(()),
            None => self.libraries.exists(module),
        }
    }
    fn contents(&self, module: &Module) -> Option<String> {
        match self.open.get(module) {
            Some(contents) => Some(contents.clone()),
            None => self.libraries.contents(module),
        }
    }
}

#[derive(Debug)]
struct Workspace {
    files: WorkspaceFiles,
    graph: ModuleGraph,
    order: OnceLock<std::result::Result<Vec<Module>, Problems>>,
}

impl Workspace {
    fn new(root: impl Into<PathBuf>) -> Self {
        let root = root.into();
        let stdlib_path = "../modules";

        let mut libraries = LibraryDir::stdlib(stdlib_path);
        libraries.insert(
            Library::MAIN,
            LibraryDir::new(root.clone()).with_preamble(Module::BUILTIN),
        );

        Self {
            files: WorkspaceFiles {
                libraries,
                open: HashMap::new(),
                root,
            },
            graph: ModuleGraph::new(),
            order: OnceLock::new(),
        }
    }
    async fn update(&self, tt: &TypeTable) {
        if let Ok(order) = self.order().await {
            for o in order {
                if let Some(stages) = self.graph.stages(o) {
                    let _ = stages.header(&self.graph, tt);
                }
            }
        }
    }
    async fn order(&self) -> std::result::Result<&[Module], &Problems> {
        self.order
            .get_or_init(|| {
                let mut problems = Problems::ok();
                let order = problems.append(
                    self.graph
                        .postorder()
                        .map(|v| v.into_iter().cloned().collect()),
                );
                order.ok_or(problems)
            })
            .as_deref()
    }
    fn problems(&self, module: &Module) -> Problems {
        match self.order.get() {
            Some(Ok(_)) => self
                .graph
                .stages(module)
                .into_iter()
                .flat_map(HasProblems::problems)
                .cloned()
                .collect(),
            Some(Err(problems)) => problems.for_module(module),
            None => Problems::ok(),
        }
    }
}

impl Backend {
    fn new(client: Client) -> Self {
        Self {
            workspaces: RwLock::new(HashMap::new()),
            type_table: TypeTable::new(),
            client,
        }
    }
    async fn log(&self, msg: &(impl Display + ?Sized)) {
        eprintln!("{msg}");
        self.client.log_message(MessageType::INFO, msg).await;
    }
    async fn workspace<'a>(&self, uri: &'a Uri) -> Option<(Uri, &'a str)> {
        self.workspaces.read().await.keys().find_map(|root| {
            uri.as_str().starts_with(root.as_str()).then_some((
                root.clone(),
                &uri.path().as_str()[root.path().as_str().len() + 1..],
            ))
        })
    }
    async fn update(&self, uri: &Uri) {
        self.workspaces.read().await[uri]
            .update(&self.type_table)
            .await;
        self.publish(uri).await;
    }
    async fn publish(&self, uri: &Uri) {
        let workspace = &self.workspaces.read().await[uri];
        for (module, src) in workspace.files.open.iter() {
            let problems = workspace.problems(module);
            let module_uri = Uri::from_str(&format!(
                "{}/{}",
                uri.as_str(),
                module.path_with_extension()
            ))
            .unwrap();
            let diagnostics = diagnostics(&module_uri, src, problems);

            self.log(&format!(
                "publishing diagnostics for {}",
                module_uri.as_str()
            ))
            .await;
            self.client
                .publish_diagnostics(module_uri, diagnostics, None)
                .await;
        }
    }
}

fn byte(s: &str, pos: Position) -> usize {
    line_column::index(s, pos.line + 1, pos.character + 1)
}

fn position(s: &str, byte: u32) -> Position {
    let (line, column) = line_column::line_column(s, byte as usize);
    Position {
        line: line - 1,
        character: column - 1,
    }
}

impl LanguageServer for Backend {
    async fn initialize(&self, init: InitializeParams) -> Result<InitializeResult> {
        let mut workspaces = self.workspaces.write().await;

        if let Some(folders) = init.workspace_folders {
            *workspaces = folders
                .into_iter()
                .map(|f| {
                    let workspace = Workspace::new(f.uri.to_file_path().unwrap());
                    (f.uri, workspace)
                })
                .collect();
        } else {
            #[expect(deprecated)]
            if let Some(root) = init.root_uri {
                let workspace = Workspace::new(root.to_file_path().unwrap());
                workspaces.insert(root, workspace);
            } else if let Some(path) = init.root_path {
                workspaces.insert(Uri::from_file_path(&path).unwrap(), Workspace::new(path));
            }
        }

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                position_encoding: Some(PositionEncodingKind::UTF8),
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::INCREMENTAL,
                )),
                diagnostic_provider: Some(DiagnosticServerCapabilities::Options(
                    DiagnosticOptions {
                        identifier: None,
                        inter_file_dependencies: true,
                        workspace_diagnostics: false,
                        work_done_progress_options: WorkDoneProgressOptions {
                            work_done_progress: None,
                        },
                    },
                )),
                inlay_hint_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            server_info: None,
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.log(&format!(
            "server initialized with workspaces {:?}",
            self.workspaces
                .read()
                .await
                .keys()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ))
        .await;
    }

    async fn did_change_workspace_folders(&self, params: DidChangeWorkspaceFoldersParams) {
        let mut workspaces = self.workspaces.write().await;

        for removed in params.event.removed {
            workspaces.remove(&removed.uri);
        }

        workspaces.extend(params.event.added.into_iter().map(|f| {
            let workspace = Workspace::new(f.uri.to_file_path().unwrap());
            (f.uri, workspace)
        }));

        self.log(&format!("added workspaces {:#?}", workspaces))
            .await;

        self.client.workspace_diagnostic_refresh().await.unwrap();
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        if let Some((workspace_uri, relative)) = self.workspace(&params.text_document.uri).await {
            let module = Module::new(Library::MAIN, relative);

            let mut write = self.workspaces.write().await;
            let workspace = write.get_mut(&workspace_uri).unwrap();
            workspace
                .files
                .open
                .insert(module.clone(), params.text_document.text);

            self.log(&format!("opened {}", module)).await;

            // update module
            workspace.graph.insert_or_update(&workspace.files, module);
            workspace.order = OnceLock::new();
            drop(write);

            self.update(&workspace_uri).await;
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some((workspace_uri, relative)) = self.workspace(&params.text_document.uri).await {
            let module = Module::new(Library::MAIN, relative);

            let mut write = self.workspaces.write().await;
            let workspace = write.get_mut(&workspace_uri).unwrap();

            // adjust string
            let s = workspace.files.open.get_mut(&module).unwrap();
            for change in params.content_changes {
                match change.range {
                    Some(range) => {
                        let start = byte(s, range.start);
                        let end = byte(s, range.end);
                        s.replace_range(start..end, &change.text);
                    }
                    None => *s = change.text,
                }
            }

            self.log(&format!("edited {}", module)).await;

            // update module
            workspace.graph.insert_or_update(&workspace.files, module);
            workspace.order = OnceLock::new();
            drop(write);

            self.update(&workspace_uri).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        if let Some((workspace_uri, relative)) = self.workspace(&params.text_document.uri).await {
            let module = Module::new(Library::MAIN, relative);

            let mut write = self.workspaces.write().await;
            let workspace = write.get_mut(&workspace_uri).unwrap();
            workspace.files.open.remove(&module);

            self.log(&format!("closed {}", module)).await;

            // update module
            workspace.graph.insert_or_update(&workspace.files, module);
            workspace.order = OnceLock::new();
            drop(write);

            self.update(&workspace_uri).await;
        }
    }

    async fn diagnostic(
        &self,
        params: DocumentDiagnosticParams,
    ) -> Result<DocumentDiagnosticReportResult> {
        if let Some((workspace_uri, relative)) = self.workspace(&params.text_document.uri).await {
            let module = Module::new(Library::MAIN, relative);
            let workspace = &self.workspaces.read().await[&workspace_uri];
            let source = workspace
                .files
                .contents(&module)
                .expect("ERROR: unknown source");
            let problems = workspace.problems(&module);

            self.log(&format!("asked diagnostics for {}", module)).await;

            Ok(DocumentDiagnosticReportResult::Report(
                DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                    related_documents: None,
                    full_document_diagnostic_report: FullDocumentDiagnosticReport {
                        result_id: None,
                        items: diagnostics(&params.text_document.uri, &source, problems),
                    },
                }),
            ))
        } else {
            Ok(DocumentDiagnosticReportResult::Report(
                DocumentDiagnosticReport::Full(Default::default()),
            ))
        }
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        self.log("got inlay hint request!").await;
        if let Some((workspace_uri, relative)) = self.workspace(&params.text_document.uri).await {
            let module = Module::new(Library::MAIN, relative);
            let workspace = &self.workspaces.read().await[&workspace_uri];
            let stages = workspace.graph.stages(&module);

            if let Some((Some(source), Some(ast))) = stages.map(|s| (s.source(), s.ast())) {
                Ok(Some(
                    ast.imports
                        .elements
                        .iter()
                        .filter_map(|(import, _)| {
                            if import.ident.is_some() {
                                return None;
                            }

                            let name = import_name(import.path.as_str());
                            eprintln!("{name}");
                            if !is_valid_identifier(name) {
                                return None;
                            }

                            Some(InlayHint {
                                position: position(source, import.path.span().end),
                                label: InlayHintLabel::String(name.to_owned()),
                                kind: None,
                                text_edits: None,
                                tooltip: None,
                                padding_left: Some(true),
                                padding_right: None,
                                data: None,
                            })
                        })
                        .collect(),
                ))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}

fn diagnostics(uri: &Uri, source: &str, problems: Problems) -> Vec<Diagnostic> {
    problems
        .into_iter()
        .map(|p| {
            let header = p.header();
            let label = p.label();
            Diagnostic {
                range: Range {
                    start: position(source, p.span.start),
                    end: position(source, p.span.end),
                },
                severity: Some(match header.level {
                    ProblemLevel::Error => DiagnosticSeverity::ERROR,
                    ProblemLevel::Warning => DiagnosticSeverity::WARNING,
                }),
                code: Some(NumberOrString::Number(header.id as i32)),
                // TODO
                code_description: None,
                source: Some("lucu".to_owned()),
                message: match label {
                    Some(label) => format!("{}\n{}", header.title, label),
                    None => header.title.to_owned(),
                },
                related_information: Some(
                    p.kind
                        .context()
                        .flat_map(|c| {
                            c.module.is_none().then_some(())?;
                            Some(DiagnosticRelatedInformation {
                                location: Location {
                                    uri: uri.clone(),
                                    range: Range {
                                        start: position(source, c.span.start),
                                        end: position(source, c.span.end),
                                    },
                                },
                                message: c.label?.into_owned(),
                            })
                        })
                        .collect(),
                ),
                tags: match p.kind {
                    // TODO: unnecessary
                    // TODO: deprecated
                    _ => None,
                },
                data: None,
            }
        })
        .collect()
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}
