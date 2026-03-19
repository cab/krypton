use std::collections::HashSet;

use krypton_parser::ast::{Decl, Module, Span};
use krypton_parser::diagnostics::ParseError;

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
    CircularImport { cycle: Vec<String>, span: Span },
    UnknownModule { path: String, span: Span },
    BareImport { path: String, span: Span },
    ParseError { path: String, source: String, errors: Vec<ParseError> },
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
) -> Result<ModuleGraph, ModuleGraphError> {
    let mut visited: HashSet<String> = HashSet::new();
    let mut stack: Vec<String> = Vec::new();
    let mut stack_set: HashSet<String> = HashSet::new();
    let mut result: Vec<ResolvedModule> = Vec::new();

    // Auto-add prelude and its transitive deps (uses stdlib resolver internally)
    visit_prelude_tree("prelude", resolver, &mut visited, &mut stack, &mut stack_set, &mut result)?;

    let prelude_tree_paths: HashSet<String> = result.iter().map(|m| m.path.clone()).collect();

    // Walk root imports with proper span tracking for error messages
    for decl in &root.decls {
        if let Decl::Import { path, span, .. } = decl {
            visit_user_module(path, *span, resolver, &mut visited, &mut stack, &mut stack_set, &mut result)?;
        }
    }

    Ok(ModuleGraph { modules: result, prelude_tree_paths })
}

/// DFS visit a prelude-tree module (stdlib fallback, zero spans for errors).
fn visit_prelude_tree(
    path: &str,
    resolver: &dyn ModuleResolver,
    visited: &mut HashSet<String>,
    stack: &mut Vec<String>,
    stack_set: &mut HashSet<String>,
    result: &mut Vec<ResolvedModule>,
) -> Result<(), ModuleGraphError> {
    if visited.contains(path) {
        return Ok(());
    }

    if stack_set.contains(path) {
        let mut cycle = stack.clone();
        cycle.push(path.to_string());
        return Err(ModuleGraphError::CircularImport {
            cycle,
            span: (0, 0),
        });
    }

    // For prelude tree, try stdlib first, then user resolver
    let source = StdlibLoader::get_source(path)
        .map(|s| s.to_string())
        .or_else(|| resolver.resolve(path));

    let source = match source {
        Some(s) => s,
        None => {
            return Err(ModuleGraphError::UnknownModule {
                path: path.to_string(),
                span: (0, 0),
            });
        }
    };

    let (module, parse_errors) = krypton_parser::parser::parse(&source);
    if !parse_errors.is_empty() {
        return Err(ModuleGraphError::ParseError {
            path: path.to_string(),
            source,
            errors: parse_errors,
        });
    }

    stack.push(path.to_string());
    stack_set.insert(path.to_string());

    for decl in &module.decls {
        if let Decl::Import { path: dep_path, .. } = decl {
            visit_prelude_tree(dep_path, resolver, visited, stack, stack_set, result)?;
        }
    }

    stack.pop();
    stack_set.remove(path);
    visited.insert(path.to_string());

    result.push(ResolvedModule {
        path: path.to_string(),
        module,
    });

    Ok(())
}

/// DFS visit a user-imported module with proper span tracking.
fn visit_user_module(
    path: &str,
    import_span: Span,
    resolver: &dyn ModuleResolver,
    visited: &mut HashSet<String>,
    stack: &mut Vec<String>,
    stack_set: &mut HashSet<String>,
    result: &mut Vec<ResolvedModule>,
) -> Result<(), ModuleGraphError> {
    if visited.contains(path) {
        return Ok(());
    }

    if stack_set.contains(path) {
        let mut cycle = stack.clone();
        cycle.push(path.to_string());
        return Err(ModuleGraphError::CircularImport {
            cycle,
            span: import_span,
        });
    }

    let source = resolver.resolve(path).ok_or_else(|| ModuleGraphError::UnknownModule {
        path: path.to_string(),
        span: import_span,
    })?;

    let (module, parse_errors) = krypton_parser::parser::parse(&source);
    if !parse_errors.is_empty() {
        return Err(ModuleGraphError::ParseError {
            path: path.to_string(),
            source,
            errors: parse_errors,
        });
    }

    stack.push(path.to_string());
    stack_set.insert(path.to_string());

    for decl in &module.decls {
        if let Decl::Import { path: dep_path, span, .. } = decl {
            visit_user_module(dep_path, *span, resolver, visited, stack, stack_set, result)?;
        }
    }

    stack.pop();
    stack_set.remove(path);
    visited.insert(path.to_string());

    result.push(ResolvedModule {
        path: path.to_string(),
        module,
    });

    Ok(())
}
