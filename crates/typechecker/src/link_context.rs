use std::collections::{HashMap, HashSet, VecDeque};

use crate::module_interface::{
    CanonicalRef, ExportedFnSummary, ExternFnSummary, ExternTypeSummary, InstanceSummary,
    ModuleInterface, ModulePath, TraitSummary, TypeSummary,
};
use crate::typed_ast::TraitName;
use krypton_parser::ast::Visibility;

// ---------------------------------------------------------------------------
// Dense module ID
// ---------------------------------------------------------------------------

/// Dense session-local module ID. Canonical identity remains `ModulePath`-based.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleId(u32);

struct ModuleIdInterner {
    forward: HashMap<ModulePath, ModuleId>,
    reverse: Vec<ModulePath>,
}

impl ModuleIdInterner {
    fn new() -> Self {
        Self {
            forward: HashMap::new(),
            reverse: Vec::new(),
        }
    }

    fn intern(&mut self, path: &ModulePath) -> ModuleId {
        if let Some(&id) = self.forward.get(path) {
            return id;
        }
        let id = ModuleId(self.reverse.len() as u32);
        self.forward.insert(path.clone(), id);
        self.reverse.push(path.clone());
        id
    }

    fn lookup(&self, path: &ModulePath) -> Option<ModuleId> {
        self.forward.get(path).copied()
    }

    fn resolve(&self, id: ModuleId) -> &ModulePath {
        &self.reverse[id.0 as usize]
    }
}

// ---------------------------------------------------------------------------
// Index entry types
// ---------------------------------------------------------------------------

enum FnEntry {
    Direct { index: usize },
    Reexport { canonical_module: ModuleId, canonical_name: String, index: usize },
}

enum TypeEntry {
    Direct { index: usize },
    Reexport { canonical_module: ModuleId, canonical_name: String },
}

// ---------------------------------------------------------------------------
// LinkContext
// ---------------------------------------------------------------------------

pub struct LinkContext {
    interner: ModuleIdInterner,
    interfaces: HashMap<ModuleId, ModuleInterface>,

    // Indexes
    fn_index: HashMap<(ModuleId, String), FnEntry>,
    type_index: HashMap<(ModuleId, String), TypeEntry>,
    trait_index: HashMap<(ModuleId, String), ModuleId>,
    instance_index: HashMap<TraitName, Vec<(ModuleId, usize)>>,
    extern_fn_index: HashMap<String, (ModuleId, usize)>,
    extern_type_index: HashMap<String, (ModuleId, usize)>,
    transitive_deps: HashMap<ModuleId, HashSet<ModuleId>>,
}

impl LinkContext {
    /// Build the link context from a set of module interfaces.
    pub fn build(interfaces: Vec<ModuleInterface>) -> Self {
        let mut interner = ModuleIdInterner::new();

        // Step 1: Intern all module paths (from interfaces + their direct_deps)
        for iface in &interfaces {
            interner.intern(&iface.module_path);
            for dep in &iface.direct_deps {
                interner.intern(dep);
            }
        }

        // Step 2: Store interfaces by ModuleId
        let mut iface_map = HashMap::new();
        for iface in interfaces {
            let id = interner.lookup(&iface.module_path).unwrap();
            iface_map.insert(id, iface);
        }

        // Step 3: Build fn_index
        let mut fn_index = HashMap::new();
        for (&mod_id, iface) in &iface_map {
            for (i, f) in iface.exported_fns.iter().enumerate() {
                fn_index.insert(
                    (mod_id, f.name.clone()),
                    FnEntry::Direct { index: i },
                );
            }
            for (i, f) in iface.reexported_fns.iter().enumerate() {
                let canonical_mod = interner.intern(&f.canonical_ref.module);
                fn_index.insert(
                    (mod_id, f.local_name.clone()),
                    FnEntry::Reexport {
                        canonical_module: canonical_mod,
                        canonical_name: f.canonical_ref.symbol.local_name(),
                        index: i,
                    },
                );
            }
        }

        // Step 4: Build type_index
        let mut type_index = HashMap::new();
        for (&mod_id, iface) in &iface_map {
            for (i, t) in iface.exported_types.iter().enumerate() {
                type_index.insert(
                    (mod_id, t.name.clone()),
                    TypeEntry::Direct { index: i },
                );
            }
            for t in &iface.reexported_types {
                let canonical_mod = interner.intern(&t.canonical_ref.module);
                type_index.insert(
                    (mod_id, t.local_name.clone()),
                    TypeEntry::Reexport {
                        canonical_module: canonical_mod,
                        canonical_name: t.canonical_ref.symbol.local_name(),
                    },
                );
            }
        }

        // Step 5: Build trait_index
        let mut trait_index = HashMap::new();
        for (&mod_id, iface) in &iface_map {
            for t in &iface.exported_traits {
                trait_index.insert((mod_id, t.name.clone()), mod_id);
            }
        }

        // Step 6: Build instance_index grouped by TraitName
        let mut instance_index: HashMap<TraitName, Vec<(ModuleId, usize)>> = HashMap::new();
        for (&mod_id, iface) in &iface_map {
            for (i, inst) in iface.exported_instances.iter().enumerate() {
                instance_index
                    .entry(inst.trait_name.clone())
                    .or_default()
                    .push((mod_id, i));
            }
        }

        // Step 7: Build extern_fn_index (first declaring module wins)
        let mut extern_fn_index = HashMap::new();
        for (&mod_id, iface) in &iface_map {
            for (i, ef) in iface.extern_fns.iter().enumerate() {
                let declaring_id = interner.intern(&ef.declaring_module);
                extern_fn_index.entry(ef.name.clone()).or_insert((declaring_id, i));
                // Also index by the module that has the extern in its interface
                // so lookup can find it. Use declaring module as the key.
                let _ = mod_id; // suppress unused warning
            }
        }

        // Step 8: Build extern_type_index
        let mut extern_type_index = HashMap::new();
        for (&mod_id, iface) in &iface_map {
            for (i, et) in iface.extern_types.iter().enumerate() {
                extern_type_index.entry(et.krypton_name.clone()).or_insert((mod_id, i));
            }
        }

        // Step 9: Compute transitive_deps via BFS
        let mut transitive_deps = HashMap::new();
        // Build direct_deps map (ModuleId -> Vec<ModuleId>)
        let mut direct_dep_map: HashMap<ModuleId, Vec<ModuleId>> = HashMap::new();
        for (&mod_id, iface) in &iface_map {
            let deps: Vec<ModuleId> = iface
                .direct_deps
                .iter()
                .filter_map(|d| interner.lookup(d))
                .collect();
            direct_dep_map.insert(mod_id, deps);
        }

        for &mod_id in iface_map.keys() {
            let mut reachable = HashSet::new();
            reachable.insert(mod_id);
            let mut queue = VecDeque::new();
            if let Some(deps) = direct_dep_map.get(&mod_id) {
                for &dep in deps {
                    if reachable.insert(dep) {
                        queue.push_back(dep);
                    }
                }
            }
            while let Some(current) = queue.pop_front() {
                if let Some(deps) = direct_dep_map.get(&current) {
                    for &dep in deps {
                        if reachable.insert(dep) {
                            queue.push_back(dep);
                        }
                    }
                }
            }
            transitive_deps.insert(mod_id, reachable);
        }

        LinkContext {
            interner,
            interfaces: iface_map,
            fn_index,
            type_index,
            trait_index,
            instance_index,
            extern_fn_index,
            extern_type_index,
            transitive_deps,
        }
    }

    // -----------------------------------------------------------------------
    // Query methods
    // -----------------------------------------------------------------------

    pub fn module_id(&self, path: &ModulePath) -> Option<ModuleId> {
        self.interner.lookup(path)
    }

    pub fn module_path(&self, id: ModuleId) -> &ModulePath {
        self.interner.resolve(id)
    }

    pub fn module_interface(&self, path: &ModulePath) -> Option<&ModuleInterface> {
        let id = self.interner.lookup(path)?;
        self.interfaces.get(&id)
    }

    pub fn lookup_fn_summary(&self, path: &ModulePath, name: &str) -> Option<&ExportedFnSummary> {
        let id = self.interner.lookup(path)?;
        match self.fn_index.get(&(id, name.to_string()))? {
            FnEntry::Direct { index } => {
                self.interfaces.get(&id)?.exported_fns.get(*index)
            }
            FnEntry::Reexport { canonical_module, canonical_name, .. } => {
                // Resolve to canonical module's direct entry
                match self.fn_index.get(&(*canonical_module, canonical_name.clone()))? {
                    FnEntry::Direct { index } => {
                        self.interfaces.get(canonical_module)?.exported_fns.get(*index)
                    }
                    _ => None,
                }
            }
        }
    }

    pub fn lookup_type_summary(&self, path: &ModulePath, name: &str) -> Option<&TypeSummary> {
        let id = self.interner.lookup(path)?;
        match self.type_index.get(&(id, name.to_string()))? {
            TypeEntry::Direct { index } => {
                self.interfaces.get(&id)?.exported_types.get(*index)
            }
            TypeEntry::Reexport { canonical_module, canonical_name } => {
                match self.type_index.get(&(*canonical_module, canonical_name.clone()))? {
                    TypeEntry::Direct { index } => {
                        self.interfaces.get(canonical_module)?.exported_types.get(*index)
                    }
                    _ => None,
                }
            }
        }
    }

    pub fn lookup_trait(&self, path: &ModulePath, name: &str) -> Option<&TraitSummary> {
        let id = self.interner.lookup(path)?;
        let &defining_mod = self.trait_index.get(&(id, name.to_string()))?;
        self.interfaces.get(&defining_mod)?
            .exported_traits
            .iter()
            .find(|t| t.name == name)
    }

    pub fn instances_for_trait(&self, trait_name: &TraitName) -> Vec<(&ModulePath, &InstanceSummary)> {
        let Some(entries) = self.instance_index.get(trait_name) else {
            return Vec::new();
        };
        entries
            .iter()
            .filter_map(|(mod_id, idx)| {
                let iface = self.interfaces.get(mod_id)?;
                let inst = iface.exported_instances.get(*idx)?;
                Some((self.interner.resolve(*mod_id), inst))
            })
            .collect()
    }

    pub fn all_instances(&self) -> impl Iterator<Item = (&ModulePath, &InstanceSummary)> {
        self.interfaces.iter().flat_map(move |(mod_id, iface)| {
            let path = self.interner.resolve(*mod_id);
            iface.exported_instances.iter().map(move |inst| (path, inst))
        })
    }

    pub fn lookup_extern_fn(&self, name: &str) -> Option<(&ModulePath, &ExternFnSummary)> {
        let &(mod_id, idx) = self.extern_fn_index.get(name)?;
        let iface = self.interfaces.get(&mod_id)?;
        let ef = iface.extern_fns.get(idx)?;
        Some((self.interner.resolve(mod_id), ef))
    }

    pub fn lookup_extern_type(&self, name: &str) -> Option<&ExternTypeSummary> {
        let &(mod_id, idx) = self.extern_type_index.get(name)?;
        self.interfaces.get(&mod_id)?.extern_types.get(idx)
    }

    pub fn resolve_fn_canonical(&self, path: &ModulePath, name: &str) -> Option<&CanonicalRef> {
        let id = self.interner.lookup(path)?;
        match self.fn_index.get(&(id, name.to_string()))? {
            FnEntry::Reexport { index, .. } => {
                let iface = self.interfaces.get(&id)?;
                Some(&iface.reexported_fns.get(*index)?.canonical_ref)
            }
            FnEntry::Direct { .. } => None, // Direct fns don't have a canonical ref indirection
        }
    }

    pub fn resolve_type_canonical(&self, path: &ModulePath, name: &str) -> Option<&CanonicalRef> {
        let id = self.interner.lookup(path)?;
        match self.type_index.get(&(id, name.to_string()))? {
            TypeEntry::Reexport { .. } => {
                let iface = self.interfaces.get(&id)?;
                iface
                    .reexported_types
                    .iter()
                    .find(|t| t.local_name == name)
                    .map(|t| &t.canonical_ref)
            }
            TypeEntry::Direct { .. } => None,
        }
    }

    pub fn view_for(&self, path: &ModulePath) -> Option<ModuleLinkView<'_>> {
        let id = self.interner.lookup(path)?;
        let reachable = self.transitive_deps.get(&id)?;
        Some(ModuleLinkView {
            ctx: self,
            module_id: id,
            reachable,
        })
    }
}

// ---------------------------------------------------------------------------
// ModuleLinkView — scoped, visibility-enforced access
// ---------------------------------------------------------------------------

pub struct ModuleLinkView<'a> {
    ctx: &'a LinkContext,
    module_id: ModuleId,
    reachable: &'a HashSet<ModuleId>,
}

impl<'a> ModuleLinkView<'a> {
    pub fn module_path(&self) -> &ModulePath {
        self.ctx.interner.resolve(self.module_id)
    }

    pub fn is_reachable(&self, path: &ModulePath) -> bool {
        self.ctx
            .interner
            .lookup(path)
            .is_some_and(|id| self.reachable.contains(&id))
    }

    pub fn lookup_fn_summary(
        &self,
        path: &ModulePath,
        name: &str,
    ) -> Option<&'a ExportedFnSummary> {
        let target_id = self.ctx.interner.lookup(path)?;
        if !self.reachable.contains(&target_id) {
            return None;
        }
        self.ctx.lookup_fn_summary(path, name)
    }

    pub fn lookup_type_summary(
        &self,
        path: &ModulePath,
        name: &str,
    ) -> Option<&'a TypeSummary> {
        let target_id = self.ctx.interner.lookup(path)?;
        if !self.reachable.contains(&target_id) {
            return None;
        }
        let summary = self.ctx.lookup_type_summary(path, name)?;
        // Visibility check: private types hidden unless own module
        if target_id != self.module_id && summary.visibility == Visibility::Private {
            return None;
        }
        Some(summary)
    }

    pub fn lookup_extern_fn(&self, name: &str) -> Option<(&'a ModulePath, &'a ExternFnSummary)> {
        let result = self.ctx.lookup_extern_fn(name)?;
        let mod_id = self.ctx.interner.lookup(result.0)?;
        if !self.reachable.contains(&mod_id) {
            return None;
        }
        Some(result)
    }

    pub fn instances_for_trait(
        &self,
        trait_name: &TraitName,
    ) -> Vec<(&'a ModulePath, &'a InstanceSummary)> {
        self.ctx
            .instances_for_trait(trait_name)
            .into_iter()
            .filter(|(path, _)| self.is_reachable(path))
            .collect()
    }

    pub fn all_instances(&self) -> Vec<(&'a ModulePath, &'a InstanceSummary)> {
        self.ctx
            .all_instances()
            .filter(|(path, _)| self.is_reachable(path))
            .collect()
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::module_interface::*;
    use crate::typed_ast::TraitName;
    use crate::types::{Type, TypeScheme};
    use krypton_parser::ast::{ExternTarget, Visibility};

    fn make_interface(path: &str) -> ModuleInterface {
        ModuleInterface {
            module_path: ModulePath::new(path),
            direct_deps: vec![],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_fns: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        }
    }

    fn make_fn_summary(name: &str) -> ExportedFnSummary {
        ExportedFnSummary {
            key: LocalSymbolKey::Function(name.to_string()),
            name: name.to_string(),
            scheme: TypeScheme {
                vars: vec![],
                var_names: HashMap::new(),
                constraints: vec![],
                ty: Type::Int,
            },
            origin: None,
            def_span: None,
        }
    }

    fn make_type_summary(name: &str, vis: Visibility) -> TypeSummary {
        TypeSummary {
            key: LocalSymbolKey::Type(name.to_string()),
            name: name.to_string(),
            type_params: vec![],
            type_param_vars: vec![],
            kind: TypeSummaryKind::Record {
                fields: vec![("x".to_string(), Type::Int)],
            },
            visibility: vis,
        }
    }

    fn make_trait_summary(name: &str, module_path: &str) -> TraitSummary {
        TraitSummary {
            key: LocalSymbolKey::Trait(name.to_string()),
            visibility: Visibility::Pub,
            name: name.to_string(),
            module_path: ModulePath::new(module_path),
            type_var: "a".to_string(),
            type_var_id: crate::types::TypeVarId(0),
            type_var_arity: 0,
            superclasses: vec![],
            methods: vec![],
        }
    }

    fn make_instance_summary(trait_module: &str, trait_name: &str, target: &str) -> InstanceSummary {
        InstanceSummary {
            key: LocalSymbolKey::Instance {
                trait_name: trait_name.to_string(),
                target_type: target.to_string(),
            },
            trait_name: TraitName::new(trait_module.to_string(), trait_name.to_string()),
            target_type_name: target.to_string(),
            target_type: Type::Named(target.to_string(), vec![]),
            type_var_ids: HashMap::new(),
            constraints: vec![],
            method_summaries: vec![],
            is_intrinsic: false,
        }
    }

    // 1. Module ID interning
    #[test]
    fn test_module_id_interning() {
        let a = make_interface("mod_a");
        let b = make_interface("mod_b");
        let c = make_interface("mod_c");
        let ctx = LinkContext::build(vec![a, b, c]);

        let id_a = ctx.module_id(&ModulePath::new("mod_a")).unwrap();
        let id_b = ctx.module_id(&ModulePath::new("mod_b")).unwrap();
        let id_c = ctx.module_id(&ModulePath::new("mod_c")).unwrap();

        assert_ne!(id_a, id_b);
        assert_ne!(id_b, id_c);
        assert_ne!(id_a, id_c);

        // Round-trip
        assert_eq!(ctx.module_path(id_a), &ModulePath::new("mod_a"));
        assert_eq!(ctx.module_path(id_b), &ModulePath::new("mod_b"));
        assert_eq!(ctx.module_path(id_c), &ModulePath::new("mod_c"));
    }

    // 2. Fn lookup direct
    #[test]
    fn test_fn_lookup_direct() {
        let mut iface = make_interface("mod_a");
        iface.exported_fns.push(make_fn_summary("my_fn"));
        let ctx = LinkContext::build(vec![iface]);

        let result = ctx.lookup_fn_summary(&ModulePath::new("mod_a"), "my_fn");
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, "my_fn");
    }

    // 3. Fn lookup missing
    #[test]
    fn test_fn_lookup_missing() {
        let iface = make_interface("mod_a");
        let ctx = LinkContext::build(vec![iface]);
        assert!(ctx.lookup_fn_summary(&ModulePath::new("mod_a"), "nonexistent").is_none());
    }

    // 4. Type lookup
    #[test]
    fn test_type_lookup() {
        let mut iface = make_interface("mod_a");
        iface.exported_types.push(make_type_summary("Point", Visibility::Pub));
        let ctx = LinkContext::build(vec![iface]);

        let result = ctx.lookup_type_summary(&ModulePath::new("mod_a"), "Point");
        assert!(result.is_some());
        let ts = result.unwrap();
        assert_eq!(ts.name, "Point");
        match &ts.kind {
            TypeSummaryKind::Record { fields } => {
                assert_eq!(fields[0].0, "x");
            }
            _ => panic!("expected Record"),
        }
    }

    // 5. Trait lookup
    #[test]
    fn test_trait_lookup() {
        let mut iface = make_interface("mod_a");
        iface.exported_traits.push(make_trait_summary("Eq", "mod_a"));
        let ctx = LinkContext::build(vec![iface]);

        let result = ctx.lookup_trait(&ModulePath::new("mod_a"), "Eq");
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, "Eq");
    }

    // 6. Instance index groups by trait
    #[test]
    fn test_instance_index_groups_by_trait() {
        let mut iface_a = make_interface("mod_a");
        iface_a.exported_instances.push(make_instance_summary("core/eq", "Eq", "Int"));

        let mut iface_b = make_interface("mod_b");
        iface_b.exported_instances.push(make_instance_summary("core/show", "Show", "Int"));
        iface_b.exported_instances.push(make_instance_summary("core/eq", "Eq", "String"));

        let ctx = LinkContext::build(vec![iface_a, iface_b]);

        let eq_trait = TraitName::new("core/eq".to_string(), "Eq".to_string());
        let eq_instances = ctx.instances_for_trait(&eq_trait);
        assert_eq!(eq_instances.len(), 2);

        let show_trait = TraitName::new("core/show".to_string(), "Show".to_string());
        let show_instances = ctx.instances_for_trait(&show_trait);
        assert_eq!(show_instances.len(), 1);
    }

    // 7. All instances
    #[test]
    fn test_all_instances() {
        let mut iface_a = make_interface("mod_a");
        iface_a.exported_instances.push(make_instance_summary("core/eq", "Eq", "Int"));

        let mut iface_b = make_interface("mod_b");
        iface_b.exported_instances.push(make_instance_summary("core/show", "Show", "Int"));
        iface_b.exported_instances.push(make_instance_summary("core/eq", "Eq", "String"));

        let ctx = LinkContext::build(vec![iface_a, iface_b]);
        let all: Vec<_> = ctx.all_instances().collect();
        assert_eq!(all.len(), 3);
    }

    // 8. Extern fn lookup
    #[test]
    fn test_extern_fn_lookup() {
        let mut iface = make_interface("mod_a");
        iface.extern_fns.push(ExternFnSummary {
            name: "abs".to_string(),
            declaring_module: ModulePath::new("mod_a"),
            host_module_path: "java.lang.Math".to_string(),
            target: ExternTarget::Java,
            nullable: false,
            param_types: vec![Type::Int],
            return_type: Type::Int,
        });
        let ctx = LinkContext::build(vec![iface]);

        let result = ctx.lookup_extern_fn("abs");
        assert!(result.is_some());
        let (path, ef) = result.unwrap();
        assert_eq!(path, &ModulePath::new("mod_a"));
        assert_eq!(ef.name, "abs");
    }

    // 9. Extern type lookup
    #[test]
    fn test_extern_type_lookup() {
        let mut iface = make_interface("mod_a");
        iface.extern_types.push(ExternTypeSummary {
            krypton_name: "Blob".to_string(),
            host_module: "ffi.mjs".to_string(),
            target: ExternTarget::Js,
        });
        let ctx = LinkContext::build(vec![iface]);

        let result = ctx.lookup_extern_type("Blob");
        assert!(result.is_some());
        assert_eq!(result.unwrap().krypton_name, "Blob");
    }

    // 10. Reexport fn resolution
    #[test]
    fn test_reexport_fn_resolution() {
        let mut iface_a = make_interface("mod_a");
        iface_a.exported_fns.push(make_fn_summary("helper"));

        let mut iface_b = make_interface("mod_b");
        iface_b.direct_deps.push(ModulePath::new("mod_a"));
        iface_b.reexported_fns.push(ReexportedFnEntry {
            local_name: "helper".to_string(),
            canonical_ref: CanonicalRef {
                module: ModulePath::new("mod_a"),
                symbol: LocalSymbolKey::Function("helper".to_string()),
            },
            scheme: TypeScheme {
                vars: vec![],
                var_names: HashMap::new(),
                constraints: vec![],
                ty: Type::Int,
            },
            origin: None,
            def_span: None,
        });

        let ctx = LinkContext::build(vec![iface_a, iface_b]);

        let canonical = ctx.resolve_fn_canonical(&ModulePath::new("mod_b"), "helper");
        assert!(canonical.is_some());
        assert_eq!(canonical.unwrap().module, ModulePath::new("mod_a"));

        // Also verify we can look up the fn summary through the reexport
        let summary = ctx.lookup_fn_summary(&ModulePath::new("mod_b"), "helper");
        assert!(summary.is_some());
        assert_eq!(summary.unwrap().name, "helper");
    }

    // 11. Reexport type resolution
    #[test]
    fn test_reexport_type_resolution() {
        let mut iface_a = make_interface("mod_a");
        iface_a.exported_types.push(make_type_summary("Point", Visibility::Pub));

        let mut iface_b = make_interface("mod_b");
        iface_b.direct_deps.push(ModulePath::new("mod_a"));
        iface_b.reexported_types.push(ReexportedTypeEntry {
            local_name: "Point".to_string(),
            canonical_ref: CanonicalRef {
                module: ModulePath::new("mod_a"),
                symbol: LocalSymbolKey::Type("Point".to_string()),
            },
            visibility: Visibility::Pub,
        });

        let ctx = LinkContext::build(vec![iface_a, iface_b]);

        let canonical = ctx.resolve_type_canonical(&ModulePath::new("mod_b"), "Point");
        assert!(canonical.is_some());
        assert_eq!(canonical.unwrap().module, ModulePath::new("mod_a"));

        // Lookup through reexport resolves to canonical
        let summary = ctx.lookup_type_summary(&ModulePath::new("mod_b"), "Point");
        assert!(summary.is_some());
        assert_eq!(summary.unwrap().name, "Point");
    }

    // 12. Transitive deps
    #[test]
    fn test_transitive_deps() {
        let mut iface_a = make_interface("mod_a");
        iface_a.direct_deps.push(ModulePath::new("mod_b"));

        let mut iface_b = make_interface("mod_b");
        iface_b.direct_deps.push(ModulePath::new("mod_c"));

        let iface_c = make_interface("mod_c");

        let ctx = LinkContext::build(vec![iface_a, iface_b, iface_c]);

        let view_a = ctx.view_for(&ModulePath::new("mod_a")).unwrap();
        assert!(view_a.is_reachable(&ModulePath::new("mod_a")));
        assert!(view_a.is_reachable(&ModulePath::new("mod_b")));
        assert!(view_a.is_reachable(&ModulePath::new("mod_c")));

        let view_b = ctx.view_for(&ModulePath::new("mod_b")).unwrap();
        assert!(view_b.is_reachable(&ModulePath::new("mod_b")));
        assert!(view_b.is_reachable(&ModulePath::new("mod_c")));
        assert!(!view_b.is_reachable(&ModulePath::new("mod_a")));
    }

    // 13. View reachable fn
    #[test]
    fn test_view_reachable_fn() {
        let mut iface_a = make_interface("mod_a");
        iface_a.direct_deps.push(ModulePath::new("mod_b"));

        let mut iface_b = make_interface("mod_b");
        iface_b.exported_fns.push(make_fn_summary("b_fn"));

        let ctx = LinkContext::build(vec![iface_a, iface_b]);
        let view = ctx.view_for(&ModulePath::new("mod_a")).unwrap();

        assert!(view.lookup_fn_summary(&ModulePath::new("mod_b"), "b_fn").is_some());
    }

    // 14. View unreachable fn
    #[test]
    fn test_view_unreachable_fn() {
        let iface_a = make_interface("mod_a");

        let mut iface_c = make_interface("mod_c");
        iface_c.exported_fns.push(make_fn_summary("c_fn"));

        let ctx = LinkContext::build(vec![iface_a, iface_c]);
        let view = ctx.view_for(&ModulePath::new("mod_a")).unwrap();

        assert!(view.lookup_fn_summary(&ModulePath::new("mod_c"), "c_fn").is_none());
    }

    // 15. View private type hidden
    #[test]
    fn test_view_private_type_hidden() {
        let mut iface_a = make_interface("mod_a");
        iface_a.direct_deps.push(ModulePath::new("mod_b"));

        let mut iface_b = make_interface("mod_b");
        iface_b.exported_types.push(make_type_summary("Secret", Visibility::Private));

        let ctx = LinkContext::build(vec![iface_a, iface_b]);
        let view = ctx.view_for(&ModulePath::new("mod_a")).unwrap();

        assert!(view.lookup_type_summary(&ModulePath::new("mod_b"), "Secret").is_none());
    }

    // 16. View own module sees all (including private)
    #[test]
    fn test_view_own_module_sees_all() {
        let mut iface_a = make_interface("mod_a");
        iface_a.exported_types.push(make_type_summary("Internal", Visibility::Private));
        iface_a.exported_fns.push(make_fn_summary("priv_fn"));

        let ctx = LinkContext::build(vec![iface_a]);
        let view = ctx.view_for(&ModulePath::new("mod_a")).unwrap();

        assert!(view.lookup_type_summary(&ModulePath::new("mod_a"), "Internal").is_some());
        assert!(view.lookup_fn_summary(&ModulePath::new("mod_a"), "priv_fn").is_some());
    }

    // 17. View instances filtered by reachability
    #[test]
    fn test_view_instances_filtered_by_reachability() {
        let mut iface_a = make_interface("mod_a");
        iface_a.direct_deps.push(ModulePath::new("mod_b"));
        iface_a.exported_instances.push(make_instance_summary("core/eq", "Eq", "A"));

        let mut iface_b = make_interface("mod_b");
        iface_b.exported_instances.push(make_instance_summary("core/eq", "Eq", "B"));

        let mut iface_c = make_interface("mod_c");
        iface_c.exported_instances.push(make_instance_summary("core/eq", "Eq", "C"));

        let ctx = LinkContext::build(vec![iface_a, iface_b, iface_c]);
        let view = ctx.view_for(&ModulePath::new("mod_a")).unwrap();

        let eq_trait = TraitName::new("core/eq".to_string(), "Eq".to_string());
        let instances = view.instances_for_trait(&eq_trait);
        // Should see mod_a and mod_b instances, not mod_c
        assert_eq!(instances.len(), 2);
        let target_types: Vec<&str> = instances.iter().map(|(_, i)| i.target_type_name.as_str()).collect();
        assert!(target_types.contains(&"A"));
        assert!(target_types.contains(&"B"));
        assert!(!target_types.contains(&"C"));

        // all_instances should also be filtered
        let all = view.all_instances();
        assert_eq!(all.len(), 2);
    }
}
