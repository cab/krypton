use krypton_parser::ast::Visibility;

use crate::module_interface::{
    ExportedFnSummary, ExternTypeSummary, ModuleInterface, ReexportedFnEntry, ReexportedTypeEntry,
    TraitMethodSummary, TraitSummary, TypeSummary,
};

/// Outcome of resolving a single bare name against a module's interface.
///
/// Returned by `ImportResolver::resolve` for each requested import name; the
/// caller dispatches on the variant to either bind the named symbol or
/// surface a visibility diagnostic. The kind-specific payloads are reserved
/// for future name-keyed dispatch — today's caller only uses
/// `Unknown` / `Private` to drive Pass-A diagnostics, so the other arms are
/// `#[allow(dead_code)]`.
#[allow(dead_code)]
pub(super) enum ResolveResult<'a> {
    Fn(&'a ExportedFnSummary),
    ReexportedFn(&'a ReexportedFnEntry),
    Type(&'a TypeSummary),
    ReexportedType(&'a ReexportedTypeEntry),
    ExternType(&'a ExternTypeSummary),
    Trait(&'a TraitSummary),
    TraitMethod {
        trait_def: &'a TraitSummary,
        method: &'a TraitMethodSummary,
    },
    Private,
    Unknown,
}

/// Resolves a bare import name against a module interface, in the same
/// priority order that `process_single_import` uses for visibility checks
/// and explicit-name binding. Linear scan over the iface vectors — they are
/// small (a few dozen entries per module in practice).
pub(super) struct ImportResolver<'a> {
    iface: &'a ModuleInterface,
}

impl<'a> ImportResolver<'a> {
    pub(super) fn new(iface: &'a ModuleInterface) -> Self {
        Self { iface }
    }

    pub(super) fn resolve(&self, name: &str) -> ResolveResult<'a> {
        if let Some(ef) = self.iface.exported_fns.iter().find(|ef| ef.name == name) {
            return ResolveResult::Fn(ef);
        }
        if let Some(rf) = self
            .iface
            .reexported_fns
            .iter()
            .find(|rf| rf.local_name == name)
        {
            return ResolveResult::ReexportedFn(rf);
        }
        if let Some(ts) = self.iface.exported_types.iter().find(|ts| ts.name == name) {
            // Defensive: type collection already excludes Private, but the
            // explicit guard preserves the union-check semantics that lived
            // at imports.rs:200–203 prior to this refactor.
            if !matches!(ts.visibility, Visibility::Private) {
                return ResolveResult::Type(ts);
            }
        }
        if let Some(rt) = self
            .iface
            .reexported_types
            .iter()
            .find(|rt| rt.local_name == name)
        {
            return ResolveResult::ReexportedType(rt);
        }
        if let Some(et) = self
            .iface
            .extern_types
            .iter()
            .find(|et| et.krypton_name == name)
        {
            return ResolveResult::ExternType(et);
        }
        for trait_def in &self.iface.exported_traits {
            if trait_def.name == name {
                return ResolveResult::Trait(trait_def);
            }
        }
        for trait_def in &self.iface.exported_traits {
            if let Some(method) = trait_def.methods.iter().find(|m| m.name == name) {
                return ResolveResult::TraitMethod { trait_def, method };
            }
        }
        if self.iface.private_names.contains(name) {
            return ResolveResult::Private;
        }
        ResolveResult::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module_interface::{LocalSymbolKey, ModulePath, TypeSummaryKind};
    use crate::types::{Type, TypeScheme};
    use krypton_parser::ast::ExternTarget;
    use rustc_hash::{FxHashMap, FxHashSet};

    fn empty_iface() -> ModuleInterface {
        ModuleInterface {
            module_path: ModulePath::new("test"),
            direct_deps: Vec::new(),
            exported_fns: Vec::new(),
            reexported_fns: Vec::new(),
            exported_types: Vec::new(),
            reexported_types: Vec::new(),
            exported_traits: Vec::new(),
            exported_instances: Vec::new(),
            extern_types: Vec::new(),
            exported_fn_qualifiers: FxHashMap::default(),
            type_visibility: FxHashMap::default(),
            private_names: FxHashSet::default(),
        }
    }

    fn unit_scheme() -> TypeScheme {
        TypeScheme {
            vars: Vec::new(),
            constraints: Vec::new(),
            ty: Type::Unit,
            var_names: FxHashMap::default(),
        }
    }

    fn make_fn_summary(name: &str) -> ExportedFnSummary {
        ExportedFnSummary {
            key: LocalSymbolKey::Function(name.to_string()),
            name: name.to_string(),
            exported_symbol: name.to_string(),
            scheme: unit_scheme(),
            origin: None,
            def_span: None,
        }
    }

    fn make_type_summary(name: &str, visibility: Visibility) -> TypeSummary {
        TypeSummary {
            key: LocalSymbolKey::Type(name.to_string()),
            name: name.to_string(),
            type_params: Vec::new(),
            type_param_vars: Vec::new(),
            kind: TypeSummaryKind::Opaque,
            lifts: None,
            visibility,
        }
    }

    #[test]
    fn resolves_exported_fn() {
        let mut iface = empty_iface();
        iface.exported_fns.push(make_fn_summary("foo"));
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("foo"), ResolveResult::Fn(_)));
    }

    #[test]
    fn resolves_reexported_fn() {
        let mut iface = empty_iface();
        iface.reexported_fns.push(ReexportedFnEntry {
            local_name: "bar".to_string(),
            canonical_ref: crate::module_interface::CanonicalRef {
                module: ModulePath::new("origin"),
                symbol: LocalSymbolKey::Function("bar".to_string()),
            },
            scheme: unit_scheme(),
            origin: None,
            def_span: None,
        });
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("bar"), ResolveResult::ReexportedFn(_)));
    }

    #[test]
    fn resolves_exported_type_pub() {
        let mut iface = empty_iface();
        iface
            .exported_types
            .push(make_type_summary("T", Visibility::Pub));
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("T"), ResolveResult::Type(_)));
    }

    #[test]
    fn private_exported_type_falls_through_to_private_names() {
        let mut iface = empty_iface();
        // Defensive case: TypeSummary with Private visibility and the name
        // also recorded in private_names. The defensive guard in resolve()
        // skips the Type arm and falls through to the Private arm.
        iface
            .exported_types
            .push(make_type_summary("Hidden", Visibility::Private));
        iface.private_names.insert("Hidden".to_string());
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("Hidden"), ResolveResult::Private));
    }

    #[test]
    fn resolves_reexported_type() {
        let mut iface = empty_iface();
        iface.reexported_types.push(ReexportedTypeEntry {
            local_name: "Opt".to_string(),
            canonical_ref: crate::module_interface::CanonicalRef {
                module: ModulePath::new("origin"),
                symbol: LocalSymbolKey::Type("Opt".to_string()),
            },
            visibility: Visibility::Pub,
        });
        let r = ImportResolver::new(&iface);
        assert!(matches!(
            r.resolve("Opt"),
            ResolveResult::ReexportedType(_)
        ));
    }

    #[test]
    fn resolves_extern_type() {
        let mut iface = empty_iface();
        iface.extern_types.push(ExternTypeSummary {
            krypton_name: "Ref".to_string(),
            host_module: "host".to_string(),
            target: ExternTarget::Java,
            lifts: None,
        });
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("Ref"), ResolveResult::ExternType(_)));
    }

    fn make_trait_summary(name: &str, methods: Vec<&str>) -> TraitSummary {
        TraitSummary {
            key: LocalSymbolKey::Trait(name.to_string()),
            visibility: Visibility::Pub,
            name: name.to_string(),
            module_path: ModulePath::new("origin"),
            type_var: "a".to_string(),
            type_var_id: crate::types::TypeVarId(0),
            type_var_ids: Vec::new(),
            type_var_names: Vec::new(),
            type_var_arity: 1,
            superclasses: Vec::new(),
            methods: methods
                .into_iter()
                .map(|m| TraitMethodSummary {
                    name: m.to_string(),
                    param_types: Vec::new(),
                    return_type: Type::Unit,
                    constraints: Vec::new(),
                })
                .collect(),
        }
    }

    #[test]
    fn resolves_trait_by_name() {
        let mut iface = empty_iface();
        iface
            .exported_traits
            .push(make_trait_summary("Eq", vec!["eq"]));
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("Eq"), ResolveResult::Trait(_)));
    }

    #[test]
    fn resolves_trait_method_by_name() {
        let mut iface = empty_iface();
        iface
            .exported_traits
            .push(make_trait_summary("Functor", vec!["map", "lift"]));
        let r = ImportResolver::new(&iface);
        match r.resolve("map") {
            ResolveResult::TraitMethod { trait_def, method } => {
                assert_eq!(trait_def.name, "Functor");
                assert_eq!(method.name, "map");
            }
            _ => panic!("expected TraitMethod"),
        }
    }

    #[test]
    fn resolves_private_name() {
        let mut iface = empty_iface();
        iface.private_names.insert("hidden".to_string());
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("hidden"), ResolveResult::Private));
    }

    #[test]
    fn unknown_name() {
        let iface = empty_iface();
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("missing"), ResolveResult::Unknown));
    }

    #[test]
    fn fn_priority_over_type() {
        // Synthetic — should not happen in practice (fns and types share no
        // namespace in Krypton), but the priority must be deterministic.
        let mut iface = empty_iface();
        iface.exported_fns.push(make_fn_summary("Both"));
        iface
            .exported_types
            .push(make_type_summary("Both", Visibility::Pub));
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("Both"), ResolveResult::Fn(_)));
    }
}
