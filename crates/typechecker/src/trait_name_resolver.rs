use rustc_hash::{FxHashMap, FxHashSet};

use crate::typed_ast::TraitName;
use crate::unify::TypeError;

/// Owns the bare-name → TraitName map for a single module's inference pass.
///
/// Separated from `TraitRegistry` (which stores full `TraitName → TraitInfo`)
/// so that "silent" trait registrations — trait defs pulled in transitively to
/// satisfy a re-exported method's origin but not named by the user — can
/// register into the registry without leaking a bare name that impls could
/// target. Without that split, `pub import core/functor.{map}` from prelude
/// would silently publish `Functor` as a user-visible bare name in every
/// consumer.
#[derive(Default)]
pub struct TraitNameResolver {
    /// Bare trait name → canonical `TraitName`. Populated for user-visible
    /// imports (`import core/functor.{Functor}`) and locally-defined traits.
    bare_names: FxHashMap<String, TraitName>,
    /// Bare names of traits declared in this module (orphan-check inputs).
    local_names: Vec<String>,
    /// Bare names for "internally imported" trait defs — registered into the
    /// trait registry (so dict resolution works) but intentionally hidden from
    /// `resolve` so user impls cannot bind to them without an explicit import.
    internal_imported: FxHashSet<String>,
    /// Alias map: user-chosen name → canonical `TraitName`. Queried as a
    /// fallback by `resolve` when the bare name isn't registered directly.
    aliases: FxHashMap<String, TraitName>,
}

impl TraitNameResolver {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a trait defined in the current module. Fails with
    /// `AmbiguousTraitName` if the same bare name is already bound to a trait
    /// in a different module.
    pub fn register_local(
        &mut self,
        name: String,
        trait_name: TraitName,
    ) -> Result<(), TypeError> {
        self.check_ambiguity(&name, &trait_name)?;
        self.bare_names.insert(name.clone(), trait_name);
        if !self.local_names.contains(&name) {
            self.local_names.push(name);
        }
        Ok(())
    }

    /// Register a trait imported by name (user-visible). Fails with
    /// `AmbiguousTraitName` if the same bare name is already bound to a trait
    /// in a different module.
    pub fn register_imported(
        &mut self,
        name: String,
        trait_name: TraitName,
    ) -> Result<(), TypeError> {
        self.check_ambiguity(&name, &trait_name)?;
        self.bare_names.insert(name, trait_name);
        Ok(())
    }

    /// Register a trait whose definition must live in the trait registry to
    /// satisfy a transitively-imported method's origin, but whose bare name
    /// MUST NOT become user-visible. Idempotent: repeated registration for
    /// the same `TraitName` is a no-op.
    pub fn register_internal(&mut self, trait_name: &TraitName) {
        self.internal_imported
            .insert(trait_name.local_name.clone());
    }

    /// Register a user-supplied alias for an existing trait. Aliases are
    /// consulted as a fallback in `resolve` when the primary bare-name lookup
    /// misses.
    pub fn register_alias(&mut self, alias: String, canonical: TraitName) {
        self.aliases.insert(alias, canonical);
    }

    /// Resolve a bare name the user can write in source (constraints, impl
    /// heads). Returns `None` for internally-imported traits — those are
    /// reachable only via the registry when a `TraitName` is already known.
    pub fn resolve(&self, name: &str) -> Option<&TraitName> {
        self.bare_names
            .get(name)
            .or_else(|| self.aliases.get(name))
    }

    /// True if any path — bare, alias, or internal — has registered this bare
    /// name. Used by re-export visibility checks so that an internally
    /// imported trait still satisfies a "name exists" query without leaking
    /// into user resolution.
    pub fn is_known(&self, name: &str) -> bool {
        self.bare_names.contains_key(name)
            || self.aliases.contains_key(name)
            || self.internal_imported.contains(name)
    }

    /// True if this bare trait name was either imported directly (user-visible
    /// or aliased) or registered internally. Consumed by downstream IR to
    /// distinguish "defined here" vs "imported from elsewhere".
    pub fn is_imported(&self, name: &str) -> bool {
        // A locally-declared trait is not imported, even if it shares a name
        // with an internal registration (e.g. prelude silent-import of a trait
        // whose bare name a fixture then redeclares locally).
        if self.local_names.iter().any(|n| n == name) {
            return false;
        }
        self.bare_names.contains_key(name)
            || self.aliases.contains_key(name)
            || self.internal_imported.contains(name)
    }

    /// Bare names of traits declared in the current module, in declaration
    /// order.
    pub fn local_names(&self) -> &[String] {
        &self.local_names
    }

    fn check_ambiguity(
        &self,
        name: &str,
        trait_name: &TraitName,
    ) -> Result<(), TypeError> {
        if let Some(existing) = self.bare_names.get(name) {
            if existing != trait_name {
                return Err(TypeError::AmbiguousTraitName {
                    name: name.to_string(),
                    existing_module: existing.module_path.clone(),
                    new_module: trait_name.module_path.clone(),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tn(module: &str, name: &str) -> TraitName {
        TraitName::new(module.to_string(), name.to_string())
    }

    #[test]
    fn resolve_returns_bare_registration() {
        let mut r = TraitNameResolver::new();
        let eq = tn("core/eq", "Eq");
        r.register_imported("Eq".into(), eq.clone()).unwrap();
        assert_eq!(r.resolve("Eq"), Some(&eq));
    }

    #[test]
    fn alias_resolved_as_fallback() {
        let mut r = TraitNameResolver::new();
        let eq = tn("core/eq", "Eq");
        r.register_alias("MyEq".into(), eq.clone());
        assert_eq!(r.resolve("MyEq"), Some(&eq));
        assert!(r.resolve("Eq").is_none());
    }

    #[test]
    fn register_internal_does_not_expose_bare_name() {
        let mut r = TraitNameResolver::new();
        let functor = tn("core/functor", "Functor");
        r.register_internal(&functor);
        assert!(r.resolve("Functor").is_none());
        assert!(r.is_known("Functor"));
        assert!(r.is_imported("Functor"));
    }

    #[test]
    fn ambiguity_detected_across_modules() {
        let mut r = TraitNameResolver::new();
        r.register_imported("Eq".into(), tn("module_a", "Eq"))
            .unwrap();
        let err = r
            .register_imported("Eq".into(), tn("module_b", "Eq"))
            .unwrap_err();
        match err {
            TypeError::AmbiguousTraitName {
                name,
                existing_module,
                new_module,
            } => {
                assert_eq!(name, "Eq");
                assert_eq!(existing_module, "module_a");
                assert_eq!(new_module, "module_b");
            }
            other => panic!("expected AmbiguousTraitName, got {other:?}"),
        }
    }

    #[test]
    fn same_trait_reregistration_is_idempotent() {
        let mut r = TraitNameResolver::new();
        let eq = tn("core/eq", "Eq");
        r.register_imported("Eq".into(), eq.clone()).unwrap();
        r.register_imported("Eq".into(), eq.clone()).unwrap();
        assert_eq!(r.resolve("Eq"), Some(&eq));
    }

    #[test]
    fn local_registration_records_name() {
        let mut r = TraitNameResolver::new();
        let foo = tn("test", "Foo");
        r.register_local("Foo".into(), foo.clone()).unwrap();
        assert_eq!(r.local_names(), &["Foo".to_string()]);
        assert_eq!(r.resolve("Foo"), Some(&foo));
    }

    #[test]
    fn local_shadows_internal_for_is_imported() {
        // A module that silently imports `Functor` via prelude and then
        // declares its own `trait Functor[f[_]]` must report "not imported"
        // so downstream IR treats it as a local trait.
        let mut r = TraitNameResolver::new();
        let prelude_functor = tn("core/functor", "Functor");
        r.register_internal(&prelude_functor);
        let local_functor = tn("test", "Functor");
        r.register_local("Functor".into(), local_functor.clone())
            .unwrap();
        assert!(!r.is_imported("Functor"));
        assert_eq!(r.resolve("Functor"), Some(&local_functor));
    }

    #[test]
    fn is_known_union_semantics() {
        let mut r = TraitNameResolver::new();
        r.register_imported("Eq".into(), tn("core/eq", "Eq"))
            .unwrap();
        r.register_alias("MyShow".into(), tn("core/show", "Show"));
        r.register_internal(&tn("core/functor", "Functor"));
        assert!(r.is_known("Eq"));
        assert!(r.is_known("MyShow"));
        assert!(r.is_known("Functor"));
        assert!(!r.is_known("Nothing"));
    }
}
