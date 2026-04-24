use rustc_hash::{FxHashMap, FxHashSet};

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
    pub prelude_tree_paths: FxHashSet<String>,
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
    /// The import's head segment matches a known transitive dep — the user
    /// has imported from a package that is reachable through the graph but
    /// isn't listed in their own `[dependencies]`. The resolver couldn't
    /// produce a source, but we can surface a more targeted error than
    /// [`ModuleGraphError::UnknownModule`].
    TransitiveDependencyImport {
        path: String,
        canonical: String,
        span: Span,
    },
    /// The import names a path whose final segment ends with `_test`. These
    /// modules are reserved for files discovered by the test runner and
    /// cannot be imported from ordinary source modules. Surfaced instead
    /// of [`ModuleGraphError::UnknownModule`] so the diagnostic can name
    /// the rule.
    TestModuleImport {
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
    build_module_graph_with_hints(root, resolver, target, &[])
}

/// Like [`build_module_graph`], but enriched with `transitive_hints` so that
/// when an import can't be resolved we can distinguish "truly unknown" from
/// "known transitive dependency not declared in `[dependencies]`". Each hint
/// is `(local_root_name, canonical)` — matching the shape produced by
/// `ResolvedGraph::transitive_hints`.
pub fn build_module_graph_with_hints(
    root: &Module,
    resolver: &dyn ModuleResolver,
    target: CompileTarget,
    transitive_hints: &[(String, String)],
) -> Result<ModuleGraph, ModuleGraphError> {
    build_module_graph_inner(
        root,
        resolver,
        target,
        transitive_hints,
        &FxHashSet::default(),
    )
}

/// Like [`build_module_graph_with_hints`], but with a `skip_set` of module
/// paths the DFS should treat as already-resolved. Paths in `skip_set` are
/// not resolved, parsed, or recursed into, and do not appear in the returned
/// `modules` list. Callers are responsible for arranging that skipped
/// modules are already present in any downstream `interface_cache` they
/// intend to use. Used by the `krypton test` two-phase compile pipeline to
/// avoid re-walking the source unit once per test module.
pub fn build_module_graph_with_skip(
    root: &Module,
    resolver: &dyn ModuleResolver,
    target: CompileTarget,
    transitive_hints: &[(String, String)],
    skip_set: &FxHashSet<String>,
) -> Result<ModuleGraph, ModuleGraphError> {
    build_module_graph_inner(root, resolver, target, transitive_hints, skip_set)
}

fn build_module_graph_inner(
    root: &Module,
    resolver: &dyn ModuleResolver,
    target: CompileTarget,
    transitive_hints: &[(String, String)],
    skip_set: &FxHashSet<String>,
) -> Result<ModuleGraph, ModuleGraphError> {
    let mut builder = ModuleGraphBuilder {
        resolver,
        target,
        transitive_hints,
        skip_set,
        pre_loaded: FxHashMap::default(),
        visited: FxHashSet::default(),
        stack: Vec::new(),
        stack_set: FxHashSet::default(),
        result: Vec::new(),
    };

    // Auto-add prelude and its transitive deps (uses stdlib resolver internally)
    builder.visit_prelude_tree("prelude")?;

    let prelude_tree_paths: FxHashSet<String> =
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

/// Build a module graph from **multiple** pre-parsed root modules, each
/// identified by its module path. Every root is included in the returned
/// `modules` list (toposorted with transitive imports), unlike the
/// single-root variant which excludes the root.
///
/// The `skip_set` behaves identically to [`build_module_graph_with_skip`] —
/// DFS visits to any path in the set are short-circuited and the skipped
/// module does not appear in `modules`.
pub fn build_module_graph_multi_root(
    roots: &[(String, Module)],
    resolver: &dyn ModuleResolver,
    target: CompileTarget,
    transitive_hints: &[(String, String)],
    skip_set: &FxHashSet<String>,
) -> Result<ModuleGraph, ModuleGraphError> {
    let mut pre_loaded: FxHashMap<String, Module> = FxHashMap::default();
    for (path, module) in roots {
        let mut module = module.clone();
        filter_by_platform(&mut module, target);
        pre_loaded.insert(path.clone(), module);
    }

    let mut builder = ModuleGraphBuilder {
        resolver,
        target,
        transitive_hints,
        skip_set,
        pre_loaded,
        visited: FxHashSet::default(),
        stack: Vec::new(),
        stack_set: FxHashSet::default(),
        result: Vec::new(),
    };

    builder.visit_prelude_tree("prelude")?;
    let prelude_tree_paths: FxHashSet<String> =
        builder.result.iter().map(|m| m.path.clone()).collect();

    for (path, _) in roots {
        builder.visit_user_module(path, (0, 0))?;
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
    transitive_hints: &'a [(String, String)],
    /// Paths the DFS must not resolve, parse, recurse into, or emit.
    /// The caller guarantees these are already type-checked and present in
    /// any downstream interface cache.
    skip_set: &'a FxHashSet<String>,
    /// Pre-parsed modules supplied by the caller (multi-root mode). When a
    /// visit encounters a path here, the stored `Module` is used directly
    /// and the resolver is never asked for this path.
    pre_loaded: FxHashMap<String, Module>,
    visited: FxHashSet<String>,
    stack: Vec<String>,
    stack_set: FxHashSet<String>,
    result: Vec<ResolvedModule>,
}

impl<'a> ModuleGraphBuilder<'a> {
    /// DFS visit a prelude-tree module (stdlib fallback, zero spans for errors).
    fn visit_prelude_tree(&mut self, path: &str) -> Result<(), ModuleGraphError> {
        if self.visited.contains(path) || self.skip_set.contains(path) {
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
        if self.visited.contains(path) || self.skip_set.contains(path) {
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

        // Roots supplied by `build_module_graph_multi_root` are pre-parsed and
        // platform-filtered; use them directly instead of asking the resolver.
        let module = if let Some(m) = self.pre_loaded.remove(path) {
            m
        } else {
            let source = match self.resolver.resolve(path) {
                Some(s) => s,
                None => return Err(self.unresolved_error(path, import_span)),
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
            module
        };

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

    /// Classify an unresolved import. A leaf segment ending in `_test` is
    /// always a [`ModuleGraphError::TestModuleImport`] — test modules are
    /// invisible to the `FileSystemResolver` by design. Otherwise, if the
    /// head segment matches a known transitive-dep hint, emit the more
    /// specific error; failing both, fall back to `UnknownModule`.
    fn unresolved_error(&self, path: &str, span: Span) -> ModuleGraphError {
        use crate::module_resolver::is_test_module_path;
        if is_test_module_path(path) {
            return ModuleGraphError::TestModuleImport {
                path: path.to_string(),
                span,
            };
        }
        let head = match path.split_once('/') {
            Some((h, _)) => h,
            None => path,
        };
        for (local, canonical) in self.transitive_hints {
            if local == head {
                return ModuleGraphError::TransitiveDependencyImport {
                    path: path.to_string(),
                    canonical: canonical.clone(),
                    span,
                };
            }
        }
        ModuleGraphError::UnknownModule {
            path: path.to_string(),
            span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module_resolver::{is_test_module_path, ModuleResolver};

    /// A resolver that mirrors `FileSystemResolver`'s test-module exclusion
    /// without touching the filesystem: names in `known` resolve, test-module
    /// paths always refuse, everything else is `None`.
    struct StubResolver {
        known: Vec<(String, String)>,
    }

    impl ModuleResolver for StubResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if is_test_module_path(module_path) {
                return None;
            }
            for (path, source) in &self.known {
                if path == module_path {
                    return Some(source.clone());
                }
            }
            None
        }
    }

    fn parse_root(source: &str) -> Module {
        let (module, errors) = krypton_parser::parser::parse(source);
        assert!(errors.is_empty(), "parse errors: {:?}", errors);
        module
    }

    #[test]
    fn graph_builder_emits_test_module_import() {
        let root = parse_root("import foo_test.{x}\n");
        let resolver = StubResolver { known: Vec::new() };
        let err =
            build_module_graph(&root, &resolver, CompileTarget::Jvm).expect_err("expected error");
        match err {
            ModuleGraphError::TestModuleImport { path, .. } => {
                assert_eq!(path, "foo_test");
            }
            other => panic!("expected TestModuleImport, got {other:?}"),
        }
    }

    #[test]
    fn graph_builder_emits_test_module_import_for_nested() {
        let root = parse_root("import parser/lexer_test.{x}\n");
        let resolver = StubResolver { known: Vec::new() };
        let err =
            build_module_graph(&root, &resolver, CompileTarget::Jvm).expect_err("expected error");
        match err {
            ModuleGraphError::TestModuleImport { path, .. } => {
                assert_eq!(path, "parser/lexer_test");
            }
            other => panic!("expected TestModuleImport, got {other:?}"),
        }
    }

    #[test]
    fn graph_builder_unknown_path_without_test_suffix() {
        let root = parse_root("import nonexistent.{x}\n");
        let resolver = StubResolver { known: Vec::new() };
        let err =
            build_module_graph(&root, &resolver, CompileTarget::Jvm).expect_err("expected error");
        match err {
            ModuleGraphError::UnknownModule { path, .. } => {
                assert_eq!(path, "nonexistent");
            }
            other => panic!("expected UnknownModule, got {other:?}"),
        }
    }
}
