use crate::stdlib_loader::StdlibLoader;
use crate::type_registry::{self, TypeRegistry};
use crate::types::{TypeEnv, TypeVarGen};

/// Register prelude types (Option, Result, List, Ordering) from stdlib .kr sources.
/// These are available in every module without explicit import.
pub fn register_prelude_types(
    env: &mut TypeEnv,
    registry: &mut TypeRegistry,
    gen: &mut TypeVarGen,
) {
    for &module_path in StdlibLoader::PRELUDE_MODULES {
        let source = StdlibLoader::get_source(module_path)
            .unwrap_or_else(|| panic!("missing stdlib source for {module_path}"));

        let (module, errors) = krypton_parser::parser::parse(source);
        assert!(
            errors.is_empty(),
            "parse errors in stdlib {module_path}: {errors:?}"
        );

        for decl in &module.decls {
            if let krypton_parser::ast::Decl::DefType(type_decl) = decl {
                let constructors =
                    type_registry::process_type_decl(type_decl, registry, gen)
                        .unwrap_or_else(|e| panic!("error registering prelude type {}: {e:?}", type_decl.name));

                // Mark as prelude so user types can shadow
                registry.set_prelude(&type_decl.name);

                for (name, scheme) in constructors {
                    env.bind(name, scheme);
                }
            }
        }
    }
}
