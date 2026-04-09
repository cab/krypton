use std::collections::HashSet;

use krypton_parser::ast::{CompileTarget, Decl, Module, Span};
use krypton_parser::diagnostics::ParseError;
use krypton_parser::platform::filter_by_platform;

use crate::module_resolver::ModuleResolver;
use crate::stdlib_loader::StdlibLoader;

/// A parsed module with its resolved path.
#[derive(Debug)]
pub struct ResolvedModule {
    pub path: String,
    pub module: Module,
}

/// Imported modules in topological order (dependencies first).
/// Does NOT include the root module.
#[derive(Debug)]
pub struct ModuleGraph {
    pub modules: Vec<ResolvedModule>,
    pub prelude_tree_paths: HashSet<String>,
}

/// Errors that can occur during module graph resolution.
#[derive(Debug)]
pub enum ModuleGraphError {
    CircularImport {
        cycle: Vec<String>,
        span: Span,
    },
    UnknownModule {
        path: String,
        span: Span,
    },
    BareImport {
        path: String,
        span: Span,
    },
    ParseError {
        path: String,
        source: String,
        errors: Vec<ParseError>,
    },
}

/// Build a topologically-sorted module graph from a root module.
///
/// Resolves all `import` declarations (including transitive imports)
/// and returns them in dependency order (dependencies before dependents).
/// The root module itself is NOT included in the graph.
///
/// Automatically includes the prelude and its transitive core/* dependencies.
pub fn build_module_graph(
    root: &Module,
    resolver: &dyn ModuleResolver,
    target: CompileTarget,
) -> Result<ModuleGraph, ModuleGraphError> {
    let mut builder = ModuleGraphBuilder {
        resolver,
        target,
        visited: HashSet::new(),
        stack: Vec::new(),
        stack_set: HashSet::new(),
        result: Vec::new(),
    };

    // Auto-add prelude and its transitive deps (uses stdlib resolver internally)
    builder.visit_prelude_tree("prelude")?;

    let prelude_tree_paths: HashSet<String> =
        builder.result.iter().map(|m| m.path.clone()).collect();

    // Walk root imports with proper span tracking for error messages
    for decl in &root.decls {
        if let Decl::Import { path, span, .. } = decl {
            builder.visit_user_module(path, *span)?;
        }
    }

    Ok(ModuleGraph {
        modules: builder.result,
        prelude_tree_paths,
    })
}

/// Mutable accumulators used during module graph traversal.
struct ModuleGraphBuilder<'a> {
    resolver: &'a dyn ModuleResolver,
    target: CompileTarget,
    visited: HashSet<String>,
    stack: Vec<String>,
    stack_set: HashSet<String>,
    result: Vec<ResolvedModule>,
}

impl<'a> ModuleGraphBuilder<'a> {
    /// DFS visit a prelude-tree module (stdlib fallback, zero spans for errors).
    fn visit_prelude_tree(&mut self, path: &str) -> Result<(), ModuleGraphError> {
        if self.visited.contains(path) {
            return Ok(());
        }

        if self.stack_set.contains(path) {
            let mut cycle = self.stack.clone();
            cycle.push(path.to_string());
            return Err(ModuleGraphError::CircularImport {
                cycle,
                span: (0, 0),
            });
        }

        // For prelude tree, try stdlib first, then user resolver
        let source = StdlibLoader::get_source(path)
            .map(|s| s.to_string())
            .or_else(|| self.resolver.resolve(path));

        let source = match source {
            Some(s) => s,
            None => {
                return Err(ModuleGraphError::UnknownModule {
                    path: path.to_string(),
                    span: (0, 0),
                });
            }
        };

        let (mut module, parse_errors) = krypton_parser::parser::parse(&source);
        if !parse_errors.is_empty() {
            return Err(ModuleGraphError::ParseError {
                path: path.to_string(),
                source,
                errors: parse_errors,
            });
        }

        filter_by_platform(&mut module, self.target);

        self.stack.push(path.to_string());
        self.stack_set.insert(path.to_string());

        for decl in &module.decls {
            if let Decl::Import { path: dep_path, .. } = decl {
                self.visit_prelude_tree(dep_path)?;
            }
        }

        self.stack.pop();
        self.stack_set.remove(path);
        self.visited.insert(path.to_string());

        self.result.push(ResolvedModule {
            path: path.to_string(),
            module,
        });

        Ok(())
    }

    /// DFS visit a user-imported module with proper span tracking.
    fn visit_user_module(&mut self, path: &str, import_span: Span) -> Result<(), ModuleGraphError> {
        if self.visited.contains(path) {
            return Ok(());
        }

        if self.stack_set.contains(path) {
            let mut cycle = self.stack.clone();
            cycle.push(path.to_string());
            return Err(ModuleGraphError::CircularImport {
                cycle,
                span: import_span,
            });
        }

        let source =
            self.resolver
                .resolve(path)
                .ok_or_else(|| ModuleGraphError::UnknownModule {
                    path: path.to_string(),
                    span: import_span,
                })?;

        let (mut module, parse_errors) = krypton_parser::parser::parse(&source);
        if !parse_errors.is_empty() {
            return Err(ModuleGraphError::ParseError {
                path: path.to_string(),
                source,
                errors: parse_errors,
            });
        }

        filter_by_platform(&mut module, self.target);

        self.stack.push(path.to_string());
        self.stack_set.insert(path.to_string());

        for decl in &module.decls {
            if let Decl::Import {
                path: dep_path,
                span,
                ..
            } = decl
            {
                self.visit_user_module(dep_path, *span)?;
            }
        }

        self.stack.pop();
        self.stack_set.remove(path);
        self.visited.insert(path.to_string());

        self.result.push(ResolvedModule {
            path: path.to_string(),
            module,
        });

        Ok(())
    }
}
