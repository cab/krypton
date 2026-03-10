use std::collections::HashMap;

use krypton_parser::ast::{Decl, Visibility};

use crate::infer::infer_module_inner;
use crate::module_resolver::{ModuleResolver, StdlibResolver};
use crate::stdlib_loader::StdlibLoader;
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{ExternFnInfo, TypedModule};
use crate::types::{TypeEnv, TypeVarGen};
use crate::unify::SpannedTypeError;

/// Resolver wrapper that falls back to stdlib for prelude transitive deps.
struct PreludeResolver<'a> {
    inner: &'a dyn ModuleResolver,
    stdlib: StdlibResolver,
}

impl<'a> ModuleResolver for PreludeResolver<'a> {
    fn resolve(&self, module_path: &str) -> Option<String> {
        // Try stdlib first (prelude imports core/* modules)
        if let Some(source) = self.stdlib.resolve(module_path) {
            return Some(source);
        }
        self.inner.resolve(module_path)
    }
}

/// Auto-import prelude types and functions into a module's environment.
/// Resolves `prelude.kr` from stdlib, typechecks it (caching the result),
/// and binds all re-exported names into the given environment.
///
/// Skipped when `import_stack` contains "prelude" (prevents circular deps
/// when typechecking prelude itself and its transitive deps).
pub fn auto_import_prelude(
    env: &mut TypeEnv,
    registry: &mut TypeRegistry,
    gen: &mut TypeVarGen,
    resolver: &dyn ModuleResolver,
    cache: &mut HashMap<String, TypedModule>,
    import_stack: &mut Vec<String>,
    fn_provenance_map: &mut HashMap<String, (String, String)>,
    type_provenance: &mut HashMap<String, String>,
    imported_extern_fns: &mut Vec<ExternFnInfo>,
) -> Result<(), SpannedTypeError> {
    // Skip auto-import when we're typechecking the prelude or its transitive deps
    if import_stack.iter().any(|s| s == "prelude") {
        // Still register Vec as known type name
        registry.register_name("Vec");
        return Ok(());
    }

    // Resolve and typecheck prelude.kr if not already cached
    if !cache.contains_key("prelude") {
        let source = StdlibLoader::get_source("prelude")
            .expect("missing stdlib source for prelude");
        let (prelude_module, parse_errors) = krypton_parser::parser::parse(source);
        assert!(parse_errors.is_empty(), "parse errors in stdlib prelude");

        // Use a resolver that falls back to stdlib for prelude's transitive deps
        let prelude_resolver = PreludeResolver {
            inner: resolver,
            stdlib: StdlibResolver,
        };

        import_stack.push("prelude".to_string());
        let prelude_typed = infer_module_inner(
            &prelude_module, &prelude_resolver, cache, import_stack, Some("prelude".to_string()),
        )?;
        import_stack.pop();
        cache.insert("prelude".to_string(), prelude_typed);
    }

    let cached = cache.get("prelude").unwrap();

    // Bind re-exported functions (constructors) into env with provenance
    for (name, scheme) in &cached.reexported_fn_types {
        let original_prov = cached.fn_provenance.get(name)
            .cloned()
            .unwrap_or_else(|| ("prelude".to_string(), name.clone()));
        env.bind_with_provenance(name.clone(), scheme.clone(), original_prov.0.clone());
        fn_provenance_map.insert(name.clone(), original_prov);
    }

    // Bind re-exported types into registry
    let stdlib = StdlibResolver;
    for reex_type_name in &cached.reexported_type_names {
        let original_vis = cached.reexported_type_visibility.get(reex_type_name)
            .cloned()
            .unwrap_or(Visibility::Pub);

        if registry.lookup_type(reex_type_name).is_none() {
            let original_path = cached.type_provenance.get(reex_type_name);
            if let Some(orig_path) = original_path {
                if let Some(orig_source) = stdlib.resolve(orig_path) {
                    let (orig_module, _) = krypton_parser::parser::parse(&orig_source);
                    for odecl in &orig_module.decls {
                        if let Decl::DefType(td) = odecl {
                            if td.name == *reex_type_name {
                                registry.register_name(&td.name);
                                let constructors = type_registry::process_type_decl(td, registry, gen)
                                    .unwrap_or_else(|e| panic!("error registering prelude type {}: {e:?}", td.name));

                                // Mark as prelude so user types can shadow
                                registry.set_prelude(&td.name);

                                if matches!(original_vis, Visibility::PubOpen) {
                                    for (cname, scheme) in &constructors {
                                        env.bind(cname.clone(), scheme.clone());
                                        fn_provenance_map.insert(cname.clone(), (orig_path.clone(), cname.clone()));
                                    }
                                }

                                type_provenance.insert(td.name.clone(), orig_path.clone());
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    // Copy extern fns from prelude's transitive imports
    let cached = cache.get("prelude").unwrap();
    for ext in &cached.imported_extern_fns {
        imported_extern_fns.push(ext.clone());
    }

    // Register Vec as a known type name (no constructors — backed by KryptonArray)
    registry.register_name("Vec");

    Ok(())
}
