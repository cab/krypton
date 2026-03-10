use std::collections::HashMap;

use krypton_parser::ast::{Decl, Module, Visibility};
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{ExternFnInfo, TypedModule};
use crate::types::{TypeEnv, TypeVarGen};
use crate::unify::SpannedTypeError;

/// Auto-import prelude types and functions into a module's environment.
/// The prelude and its transitive dependencies are already type-checked
/// and present in `cache` (the module graph builder ensures this).
///
/// Skipped when `is_prelude_tree` is true (when type-checking the prelude
/// itself or its transitive core/* deps).
pub fn auto_import_prelude(
    env: &mut TypeEnv,
    registry: &mut TypeRegistry,
    gen: &mut TypeVarGen,
    parsed_modules: &HashMap<String, &Module>,
    cache: &mut HashMap<String, TypedModule>,
    is_prelude_tree: bool,
    fn_provenance_map: &mut HashMap<String, (String, String)>,
    type_provenance: &mut HashMap<String, String>,
    imported_extern_fns: &mut Vec<ExternFnInfo>,
) -> Result<(), SpannedTypeError> {
    // Skip auto-import when we're typechecking the prelude or its transitive deps
    if is_prelude_tree {
        // Still register Vec as known type name
        registry.register_name("Vec");
        return Ok(());
    }

    // Prelude should already be in cache from the module graph
    let cached = match cache.get("prelude") {
        Some(c) => c,
        None => {
            panic!("prelude not found in cache — module graph should have resolved it");
        }
    };

    // Bind re-exported functions (constructors) into env with provenance
    for (name, scheme) in &cached.reexported_fn_types {
        let original_prov = cached.fn_provenance.get(name)
            .cloned()
            .unwrap_or_else(|| ("prelude".to_string(), name.clone()));
        env.bind_with_provenance(name.clone(), scheme.clone(), original_prov.0.clone());
        fn_provenance_map.insert(name.clone(), original_prov);
    }

    // Bind re-exported types into registry
    for reex_type_name in &cached.reexported_type_names {
        let original_vis = cached.reexported_type_visibility.get(reex_type_name)
            .cloned()
            .unwrap_or(Visibility::Pub);

        if registry.lookup_type(reex_type_name).is_none() {
            let original_path = cached.type_provenance.get(reex_type_name);
            if let Some(orig_path) = original_path {
                if let Some(orig_module) = parsed_modules.get(orig_path.as_str()) {
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
