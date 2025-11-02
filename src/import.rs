use compact_str::format_compact;
use do_notation::m;
use im::HashSet;

use crate::{
    err::{LucuDiagnostic, Result, SimpleDiagnostic},
    module::{Module, ModuleResolver, UnknownModule},
    stage::{
        lexer::{Lexer, Span},
        parser::{
            Parser,
            ast::{self, Ident, Spanned},
        },
    },
};

fn import_name(path: &ast::String) -> ast::Ident {
    let without_extension = path.0.rsplit_once('.').map(|t| t.0).unwrap_or(&path.0);
    let end = path.1.end - 1 - (path.0.len() - without_extension.len()) as u32;

    let ident = without_extension
        .rsplit_once(['/', '\\', ':'])
        .map(|t| t.1)
        .unwrap_or(without_extension);
    let start = path.1.start + 1 + (without_extension.len() - ident.len()) as u32;

    Spanned(ident.into(), Span::new(start, end))
}

fn reborrow<'short>(
    vec: &'short im::Vector<(&Module, &ModuleImports, usize)>,
) -> &'short im::Vector<(&'short Module, &'short ModuleImports, usize)> {
    // SAFETY: this is effectively like reborrowing a `&'short &'a Module` to `&'short Module`
    unsafe { std::mem::transmute(vec) }
}

fn module_imports_recursive<T: ModuleResolver>(
    resolver: &T,
    module: &Module,
    source: &str,
    done: &mut HashSet<Module>,
    stack: im::Vector<(&Module, &ModuleImports, usize)>,
) -> Result<Vec<(Module, ast::Module, ModuleImports)>> {
    if stack.iter().any(|(m, _, _)| *m == module) {
        todo!("Cycle");
    }
    if done.contains(module) {
        return Result::new(Vec::new());
    }

    done.insert(module.clone());
    m! {
        let tokens = Lexer::new(source).collect::<Box<_>>();
        ast <- Parser::new(module, source, &tokens).module();

        let imports = ModuleImports::from(resolver, module, &ast);
        children <- imports.iter().enumerate().map(|(i, (path, id, m))| {
            let child = match resolver.contents(m) {
                Ok(source) => module_imports_recursive(
                    resolver,
                    m,
                    &source,
                    done,
                    reborrow(&stack).clone() + im::Vector::unit((module, &imports, i)),
                ),
                Err(UnknownModule::UnknownLibrary(_)) => Result::default().with(LucuDiagnostic::UnknownLibrary(
                    SimpleDiagnostic::new(module.clone(), path.expect("ICE: could not find preamble").1),
                )),
                Err(UnknownModule::UnknownFile(file)) => Result::default().with(LucuDiagnostic::UnknownFile(
                    SimpleDiagnostic::new(module.clone(), path.expect("ICE: could not find preamble").1)
                        .label(format_compact!("Path resolved to {}", file.display())),
                )),
            };
            child.checked(|_| id.filter(|id| !id.valid()).map(|id| LucuDiagnostic::InvalidIdentifier(
                SimpleDiagnostic::new(module.clone(), id.1),
            )))
        }).collect::<Result<Vec<_>>>();

        return Iterator::chain(
            children.into_iter().flatten(),
            std::iter::once((module.clone(), ast, imports))
        ).collect();
    }
}

#[derive(Debug)]
pub struct ModuleImports {
    preamble: Option<Module>,
    imports: Vec<(ast::String, ast::Ident, Module)>,
}

impl ModuleImports {
    fn from(resolver: &impl ModuleResolver, module: &Module, ast: &ast::Module) -> Self {
        let preamble = resolver.preamble(module);
        let imports = ast
            .imports
            .iter()
            .map(|import| {
                (
                    import.path.clone(),
                    import_name(&import.path),
                    Module::from_import(module, &import.path.0),
                )
            })
            .collect();
        Self { preamble, imports }
    }
    pub fn all(
        resolver: &impl ModuleResolver,
    ) -> Result<Vec<(Module, ast::Module, ModuleImports)>> {
        let main = resolver.main();
        let source = resolver
            .contents(&main)
            .expect("ICE: could not find main file");
        module_imports_recursive(
            resolver,
            &main,
            &source,
            &mut HashSet::new(),
            im::Vector::new(),
        )
    }
    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (Option<&ast::String>, Option<&ast::Ident>, &Module)> {
        Iterator::chain(
            self.preamble.iter().map(|m| (None, None, m)),
            self.imports.iter().map(|(s, i, m)| (Some(s), Some(i), m)),
        )
    }
}
