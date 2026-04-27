use krypton_parser::ast::Visibility;

use crate::module_interface::{
    ExportedFnSummary, ExternTypeSummary, LocalSymbolKey, ModuleInterface, ReexportedFnEntry,
    ReexportedTypeEntry, TraitMethodSummary, TraitSummary, TypeSummary,
};

/// Outcome of resolving a single bare name against a module's interface.
///
/// Returned by `ImportResolver::resolve` for each requested import name. The
/// dispatcher in `process_single_import` matches on the variant to call the
/// right per-arm helper (`bind_explicit_exported_fn`,
/// `bind_explicit_reexported_type`, `bind_explicit_trait`, …) or — for
/// `Unknown` / `Private` — to surface a visibility diagnostic.
///
/// `Type` / `ReexportedType` / `Trait` / `TraitMethod` payloads are consumed
/// directly by their helpers. `Fn` / `ReexportedFn` / `ExternType` payloads
/// identify the variant kind for visibility but are otherwise unused: the
/// dispatcher re-scans the iface fn collections to bind every same-named
/// candidate (overloads from `pub import a.{f}; pub import b.{f}` or from a
/// local + re-export stack). `ExternType` is bound by
/// `bind_extern_type_visibility`, not the per-arm dispatcher.
pub(super) enum ResolveResult<'a> {
    Fn(#[allow(dead_code)] &'a ExportedFnSummary),
    ReexportedFn(#[allow(dead_code)] &'a ReexportedFnEntry),
    Type(&'a TypeSummary),
    ReexportedType(&'a ReexportedTypeEntry),
    ExternType(#[allow(dead_code)] &'a ExternTypeSummary),
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
    /// When true, suppress the standard private-visibility filter so the
    /// resolver returns `Fn`/`Type` variants for entries in
    /// `iface.private_fns` / `iface.private_types`. Set only when resolving
    /// a `_test.kr` companion's import of its source-unit twin; every other
    /// import path uses the standard filtered resolver.
    bypass_visibility: bool,
}

impl<'a> ImportResolver<'a> {
    pub(super) fn new(iface: &'a ModuleInterface) -> Self {
        Self {
            iface,
            bypass_visibility: false,
        }
    }

    /// Resolver variant for a `_test.kr` companion module reading its source
    /// unit twin. Returns `Fn`/`Type` for entries in `iface.private_fns` /
    /// `iface.private_types` and lets `Visibility::Private` `exported_types`
    /// flow through unfiltered.
    pub(super) fn for_companion(iface: &'a ModuleInterface) -> Self {
        Self {
            iface,
            bypass_visibility: true,
        }
    }

    pub(super) fn resolve(&self, name: &str) -> ResolveResult<'a> {
        let exported_fn = self.iface.exported_fns.iter().find(|ef| ef.name == name);
        let reexported_fn = self
            .iface
            .reexported_fns
            .iter()
            .find(|rf| rf.local_name == name);
        let exported_type = self.iface.exported_types.iter().find(|ts| ts.name == name);
        let exported_type = if self.bypass_visibility {
            exported_type
        } else {
            exported_type.filter(|ts| !matches!(ts.visibility, Visibility::Private))
        };
        let reexported_type = self
            .iface
            .reexported_types
            .iter()
            .find(|rt| rt.local_name == name);

        // Record types share their name with their default constructor; both
        // entries can land in the iface (Type registration + Constructor in
        // exported/reexported_fns). The Type-arm helpers register the type
        // *and* bind the constructor, while the Fn-arm helpers only bind the
        // constructor — so dispatching to Fn would leave the type
        // unregistered. Prefer the Type variant whenever a same-name
        // constructor is paired with a Type entry.
        let fn_is_self_named_constructor = |key: &LocalSymbolKey, lookup: &str| -> bool {
            matches!(
                key,
                LocalSymbolKey::Constructor { parent_type, name: ctor_name }
                if parent_type == lookup && ctor_name == lookup
            )
        };
        // For the test-companion bypass, the same dual-record rule must
        // see private_fns and private_types: a private record `T` lives in
        // both vectors (as a Constructor in private_fns and as a Type in
        // private_types). Prefer the Type arm so the helper registers the
        // type AND binds the constructor.
        let private_fn = if self.bypass_visibility {
            self.iface.private_fns.iter().find(|ef| ef.name == name)
        } else {
            None
        };
        let private_type = if self.bypass_visibility {
            self.iface.private_types.iter().find(|ts| ts.name == name)
        } else {
            None
        };
        let dual_record = exported_fn
            .map(|ef| fn_is_self_named_constructor(&ef.key, name))
            .unwrap_or(false)
            || reexported_fn
                .map(|rf| fn_is_self_named_constructor(&rf.canonical_ref.symbol, name))
                .unwrap_or(false)
            || private_fn
                .map(|pf| fn_is_self_named_constructor(&pf.key, name))
                .unwrap_or(false);
        if dual_record {
            if let Some(ts) = exported_type {
                return ResolveResult::Type(ts);
            }
            if let Some(rt) = reexported_type {
                return ResolveResult::ReexportedType(rt);
            }
            if let Some(pt) = private_type {
                return ResolveResult::Type(pt);
            }
        }

        if let Some(ef) = exported_fn {
            return ResolveResult::Fn(ef);
        }
        if let Some(rf) = reexported_fn {
            return ResolveResult::ReexportedFn(rf);
        }
        if let Some(ts) = exported_type {
            return ResolveResult::Type(ts);
        }
        if let Some(rt) = reexported_type {
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
        if let Some(pf) = private_fn {
            return ResolveResult::Fn(pf);
        }
        if let Some(pt) = private_type {
            return ResolveResult::Type(pt);
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
            private_fns: Vec::new(),
            private_types: Vec::new(),
            is_test_companion_of: None,
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
    fn companion_bypass_resolves_private_fn() {
        let mut iface = empty_iface();
        iface.private_fns.push(make_fn_summary("private_x"));
        iface.private_names.insert("private_x".to_string());
        let r = ImportResolver::for_companion(&iface);
        assert!(matches!(r.resolve("private_x"), ResolveResult::Fn(_)));
    }

    #[test]
    fn companion_bypass_resolves_private_type() {
        let mut iface = empty_iface();
        iface
            .private_types
            .push(make_type_summary("Inner", Visibility::Private));
        iface.private_names.insert("Inner".to_string());
        let r = ImportResolver::for_companion(&iface);
        assert!(matches!(r.resolve("Inner"), ResolveResult::Type(_)));
    }

    #[test]
    fn companion_bypass_returns_private_exported_type_directly() {
        let mut iface = empty_iface();
        iface
            .exported_types
            .push(make_type_summary("Inner", Visibility::Private));
        let r = ImportResolver::for_companion(&iface);
        assert!(matches!(r.resolve("Inner"), ResolveResult::Type(_)));
    }

    #[test]
    fn no_bypass_still_returns_private_for_known_private_fn() {
        let mut iface = empty_iface();
        iface.private_fns.push(make_fn_summary("private_x"));
        iface.private_names.insert("private_x".to_string());
        let r = ImportResolver::new(&iface);
        assert!(matches!(r.resolve("private_x"), ResolveResult::Private));
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
