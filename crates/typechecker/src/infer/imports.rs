use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Decl, ImportName, Module, Span, Visibility};

use crate::type_registry;
use crate::typed_ast::{self as typed_ast, TraitName};
use crate::types::{Type, TypeScheme};
use crate::unify::{SpannedTypeError, TypeError};

use super::import_resolver::{ImportResolver, ResolveResult};
use super::{
    constructor_binding_ref, imported_binding_ref, spanned, ModuleInferenceState, QualifiedExport,
    QualifiedModuleBinding,
};

fn constructor_kind_from_summary(
    summary: &crate::module_interface::TypeSummary,
) -> crate::types::ConstructorBindingKind {
    match summary.kind {
        crate::module_interface::TypeSummaryKind::Opaque => {
            unreachable!("opaque exported types do not have constructors")
        }
        crate::module_interface::TypeSummaryKind::Record { .. } => {
            crate::types::ConstructorBindingKind::Record
        }
        crate::module_interface::TypeSummaryKind::Sum { .. } => {
            crate::types::ConstructorBindingKind::Variant
        }
    }
}

impl ModuleInferenceState {
    /// Bind an imported name's def span, or just update the span if the name
    /// already has overload candidates (to avoid overwriting the overload set).
    fn bind_or_update_def_span(
        &mut self,
        effective_name: String,
        scheme: crate::types::TypeScheme,
        binding_source: crate::types::BindingSource,
        def_span: Span,
        source_module: String,
    ) {
        let has_overloads = self
            .env
            .lookup_entry(&effective_name)
            .is_some_and(|e| e.overload_candidates.is_some());
        let ds = crate::types::DefSpan {
            span: def_span,
            source_module: Some(source_module),
        };
        if has_overloads {
            self.env.set_def_span(effective_name, ds);
        } else {
            self.env
                .bind_with_source_and_def_span(effective_name, scheme, binding_source, ds);
        }
    }

    /// Build a synthetic `Decl::Import` for the prelude, gathering all re-exported names
    /// from the cached prelude module. Returns `None` when we ARE the prelude or it
    /// isn't cached yet.
    pub(super) fn build_synthetic_prelude_import(
        &mut self,
        is_prelude_tree: bool,
        interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
    ) -> Option<Decl> {
        if is_prelude_tree {
            return None;
        }
        let iface = interface_cache.get("prelude")?;
        use crate::module_interface::LocalSymbolKey;

        let mut names: Vec<ImportName> = Vec::new();

        // Re-exported type names (e.g. Option, Result, List, Ordering)
        for reex in &iface.reexported_types {
            names.push(ImportName {
                name: reex.local_name.clone(),
                alias: None,
            });
        }

        // Build set of constructor names from pub (transparent) re-exported types,
        // so we can exclude them from the re-exported fn list (they come from type processing).
        let mut prelude_constructor_names: FxHashSet<String> = FxHashSet::default();
        for reex in &iface.reexported_types {
            if matches!(reex.visibility, Visibility::Pub) {
                let orig_path = &reex.canonical_ref.module.0;
                if let Some(orig_iface) = interface_cache.get(orig_path.as_str()) {
                    for ef in &orig_iface.exported_fns {
                        if matches!(ef.key, LocalSymbolKey::Constructor { .. }) {
                            prelude_constructor_names.insert(ef.name.clone());
                        }
                    }
                }
            }
        }

        // Re-exported trait names (e.g. Eq, Show, Semigroup, etc.)
        for trait_summary in &iface.exported_traits {
            names.push(ImportName {
                name: trait_summary.name.clone(),
                alias: None,
            });
        }

        // Re-exported functions (e.g. println), excluding constructors
        // that will be bound via type processing
        for ef in &iface.reexported_fns {
            if !prelude_constructor_names.contains(&ef.local_name) {
                names.push(ImportName {
                    name: ef.local_name.clone(),
                    alias: None,
                });
            }
        }

        // Track which names came from the prelude so we can remove shadowed
        // entries from the import context later.
        for n in &names {
            self.prelude_imported_names.insert(n.name.clone());
        }

        Some(Decl::Import {
            platform: None,
            is_pub: false,
            path: "prelude".to_string(),
            names,
            span: (0, 0),
        })
    }
    /// Process all import declarations (Phase 6): the import loop.
    pub(super) fn process_imports(
        &mut self,
        module: &Module,
        interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
        synthetic_prelude_import: Option<&Decl>,
    ) -> Result<(), SpannedTypeError> {
        // Build decl list: synthetic prelude import (if any) + module's own decls
        let all_decls: Vec<&Decl> = synthetic_prelude_import
            .into_iter()
            .chain(module.decls.iter())
            .collect();
        for decl in &all_decls {
            if let Decl::Import {
                is_pub,
                path,
                names,
                span,
                ..
            } = decl
            {
                self.process_single_import(*is_pub, path, names, *span, interface_cache)?;
            }
        }
        Ok(())
    }

    fn process_single_import(
        &mut self,
        is_pub: bool,
        path: &str,
        names: &[ImportName],
        span: Span,
        interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
    ) -> Result<(), SpannedTypeError> {
        // Module should already be type-checked (topological order guarantees this)
        let iface = interface_cache
            .get(path)
            .expect("module interface should be in cache (topological order)");

        let requested: FxHashSet<&str> = names.iter().map(|n| n.name.as_str()).collect();
        let import_all = names.is_empty();
        let is_synthetic_prelude_import = path == "prelude" && span == (0, 0);

        let qualifier_name = path.rsplit('/').next().unwrap_or(path).to_string();
        let mut qualified_exports: FxHashMap<String, QualifiedExport> = FxHashMap::default();

        let resolver = ImportResolver::new(iface);

        // Pass A — visibility
        for name in &requested {
            match resolver.resolve(name) {
                ResolveResult::Unknown => {
                    return Err(spanned(
                        TypeError::UnknownExport {
                            name: name.to_string(),
                            module_path: path.to_string(),
                        },
                        span,
                    ));
                }
                ResolveResult::Private => {
                    return Err(spanned(
                        TypeError::PrivateName {
                            name: name.to_string(),
                            module_path: path.to_string(),
                        },
                        span,
                    ));
                }
                _ => {}
            }
        }

        // Build alias map from ImportName so explicit-name passes can look
        // up an alias by canonical name without re-scanning `names`.
        let aliases: FxHashMap<&str, &str> = names
            .iter()
            .filter_map(|n| n.alias.as_deref().map(|a| (n.name.as_str(), a)))
            .collect();

        // Pass B — explicit name binding. Iterate the iface collections in
        // the same order the original per-collection loops used, so that
        // `fn_types` insertion order (load-bearing for env display
        // snapshots and overload tie-break) stays identical.
        for ef in &iface.exported_fns {
            if requested.contains(ef.name.as_str()) {
                let alias = aliases.get(ef.name.as_str()).copied();
                self.bind_explicit_exported_fn(
                    ef,
                    alias,
                    iface,
                    path,
                    span,
                    is_synthetic_prelude_import,
                )?;
            }
        }
        for rf in &iface.reexported_fns {
            if requested.contains(rf.local_name.as_str()) {
                let alias = aliases.get(rf.local_name.as_str()).copied();
                self.bind_explicit_reexported_fn(
                    rf,
                    alias,
                    iface,
                    interface_cache,
                    span,
                    is_synthetic_prelude_import,
                )?;
            }
        }
        for reex in &iface.reexported_types {
            if requested.contains(reex.local_name.as_str()) {
                let alias = aliases.get(reex.local_name.as_str()).copied();
                self.bind_explicit_reexported_type(
                    reex,
                    alias,
                    interface_cache,
                    path,
                    span,
                    is_synthetic_prelude_import,
                )?;
            }
        }
        for ts in &iface.exported_types {
            if requested.contains(ts.name.as_str()) {
                let alias = aliases.get(ts.name.as_str()).copied();
                self.bind_explicit_exported_type(
                    ts,
                    alias,
                    path,
                    span,
                    is_synthetic_prelude_import,
                )?;
            }
        }

        // import_all qualified-fn binding (exported_fns + reexported_fns).
        if import_all {
            self.bind_qualified_exports_for_import_all(
                iface,
                interface_cache,
                path,
                &qualifier_name,
                is_synthetic_prelude_import,
                &mut qualified_exports,
            );
        }

        // Type/constructor handling: import_all + silent registration of
        // non-requested types (constructor resolution still needs the type).
        self.bind_types_pass(
            iface,
            &requested,
            import_all,
            path,
            &qualifier_name,
            span,
            is_synthetic_prelude_import,
            &mut qualified_exports,
        )?;

        // Store qualified module binding *after* type processing so pub
        // (transparent) constructor entries added above are captured.
        if import_all {
            self.qualified_modules.insert(
                qualifier_name.clone(),
                QualifiedModuleBinding {
                    module_path: path.to_string(),
                    exports: qualified_exports.clone(),
                },
            );
        }

        // Extern types: post-pass populates `imported_type_info` regardless of
        // whether the name was explicitly requested.
        self.bind_extern_type_visibility(iface, &requested, import_all, path);

        // Trait pass: binds trait defs, registers bare names, and binds
        // visible methods. Single iteration handles both explicit-by-name
        // requests (trait or method) and `import_all`, matching the
        // pre-refactor behavior.
        self.bind_traits_pass(
            iface,
            &requested,
            import_all,
            &aliases,
            path,
            span,
            is_synthetic_prelude_import,
        )?;

        if is_pub {
            self.process_pub_reexports(names, span)?;
        }

        Ok(())
    }

    fn process_pub_reexports(
        &mut self,
        names: &[ImportName],
        span: Span,
    ) -> Result<(), SpannedTypeError> {
        for import_name in names {
            let effective_name = import_name
                .alias
                .as_ref()
                .unwrap_or(&import_name.name)
                .clone();
            let found_fn = self.imports.contains_name(&effective_name);
            let found_type = self
                .imports
                .imported_type_info
                .contains_key(&effective_name);
            let canonical_trait = self.trait_names.resolve(&effective_name).cloned();
            let found_trait = canonical_trait.is_some();

            if !found_fn && !found_type && !found_trait {
                return Err(spanned(
                    TypeError::PrivateReexport {
                        name: effective_name.clone(),
                    },
                    span,
                ));
            }
            if found_fn {
                let candidates: Vec<_> = self
                    .imports
                    .get_by_name(&effective_name)
                    .map(|f| (f.scheme.clone(), f.origin.clone(), f.qualified_name.clone()))
                    .collect();
                let reexport_def_span = self.env.get_def_span(&effective_name).map(|d| d.span);
                for (scheme, origin, qualified_name) in candidates {
                    // Dedup key is (qualified_name, normalized param types):
                    // the param types distinguish overloads that share a
                    // canonical qualified name, and the qualified name
                    // distinguishes cross-module entries. A pure-name key
                    // would collapse overloads; a pure-qualified-name key
                    // would double-count when a single overload is reached
                    // via multiple re-export statements in this module.
                    let new_params = crate::overload::fn_param_types(&scheme.ty);
                    let already_reexported = self.reexported_fn_types.iter().any(|ef| {
                        ef.name == effective_name
                            && ef.qualified_name.as_ref() == Some(&qualified_name)
                            && crate::overload::fn_param_types(&ef.scheme.ty) == new_params
                    });
                    if already_reexported {
                        continue;
                    }
                    self.reexported_fn_types.push(typed_ast::ExportedFn {
                        name: effective_name.clone(),
                        scheme,
                        origin,
                        def_span: reexport_def_span,
                        qualified_name: Some(qualified_name),
                    });
                }
            }
            if found_type {
                self.reexported_type_names.push(effective_name.clone());
                let original_vis = self
                    .imports
                    .imported_type_info
                    .get(&effective_name)
                    .map(|(_, vis)| *vis)
                    .unwrap_or(Visibility::Opaque);
                self.reexported_type_visibility
                    .insert(effective_name.clone(), original_vis);
            }
            if let Some(canonical) = canonical_trait {
                if let Some(td) = self.imported_trait_defs.iter().find(|td| {
                    td.name == canonical.local_name && td.module_path == canonical.module_path
                }) {
                    self.reexported_trait_defs.push(td.clone());
                }
            }
        }
        Ok(())
    }

    fn bind_explicit_exported_fn(
        &mut self,
        ef: &crate::module_interface::ExportedFnSummary,
        alias: Option<&str>,
        iface: &crate::module_interface::ModuleInterface,
        path: &str,
        span: Span,
        is_synthetic_prelude_import: bool,
    ) -> Result<(), SpannedTypeError> {
        let effective_name = alias
            .map(str::to_string)
            .unwrap_or_else(|| ef.name.clone());
        match &ef.key {
            crate::module_interface::LocalSymbolKey::Constructor { parent_type, .. } => {
                let kind = iface
                    .exported_types
                    .iter()
                    .find(|ts| ts.name == *parent_type)
                    .map(constructor_kind_from_summary)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: constructor parent type '{}' not in exported_types",
                            parent_type
                        )
                    });
                self.imports.bind_imported_constructor(
                    &mut self.env,
                    effective_name.clone(),
                    ef.scheme.clone(),
                    path.to_string(),
                    parent_type.clone(),
                    ef.name.clone(),
                    kind,
                    is_synthetic_prelude_import,
                );
            }
            _ => {
                let binding_source = self.imports.bind_import(
                    &mut self.env,
                    crate::infer::ImportBinding {
                        name: effective_name.clone(),
                        scheme: ef.scheme.clone(),
                        origin: ef.origin.clone(),
                        source_module: path.to_string(),
                        original_name: ef.name.clone(),
                        is_prelude: is_synthetic_prelude_import,
                        span,
                    },
                )?;
                if let Some(ds) = ef.def_span {
                    self.bind_or_update_def_span(
                        effective_name.clone(),
                        ef.scheme.clone(),
                        binding_source,
                        ds,
                        path.to_string(),
                    );
                }
            }
        }
        if let Some(quals) = iface.exported_fn_qualifiers.get(&ef.name) {
            self.imports
                .imported_fn_qualifiers
                .insert(effective_name, quals.clone());
        }
        Ok(())
    }

    fn bind_explicit_reexported_fn(
        &mut self,
        ef: &crate::module_interface::ReexportedFnEntry,
        alias: Option<&str>,
        iface: &crate::module_interface::ModuleInterface,
        interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
        span: Span,
        is_synthetic_prelude_import: bool,
    ) -> Result<(), SpannedTypeError> {
        use crate::module_interface;

        let effective_name = alias
            .map(str::to_string)
            .unwrap_or_else(|| ef.local_name.clone());
        let canonical_name = ef.canonical_ref.symbol.local_name();
        let original_prov = (ef.canonical_ref.module.0.clone(), canonical_name);
        match &ef.canonical_ref.symbol {
            crate::module_interface::LocalSymbolKey::Constructor { parent_type, .. } => {
                let kind = interface_cache
                    .get(original_prov.0.as_str())
                    .and_then(|orig_iface| {
                        orig_iface
                            .exported_types
                            .iter()
                            .find(|ts| ts.name == *parent_type)
                    })
                    .map(constructor_kind_from_summary)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: constructor parent type '{}' not in exported_types for module {}",
                            parent_type, original_prov.0
                        )
                    });
                self.imports.bind_imported_constructor(
                    &mut self.env,
                    effective_name.clone(),
                    ef.scheme.clone(),
                    original_prov.0.clone(),
                    parent_type.clone(),
                    original_prov.1.clone(),
                    kind,
                    is_synthetic_prelude_import,
                );
            }
            _ => {
                let binding_source = self.imports.bind_import(
                    &mut self.env,
                    crate::infer::ImportBinding {
                        name: effective_name.clone(),
                        scheme: ef.scheme.clone(),
                        origin: ef.origin.clone(),
                        source_module: original_prov.0.clone(),
                        original_name: original_prov.1.clone(),
                        is_prelude: is_synthetic_prelude_import,
                        span,
                    },
                )?;
                if let Some(ds) = ef.def_span {
                    self.bind_or_update_def_span(
                        effective_name.clone(),
                        ef.scheme.clone(),
                        binding_source,
                        ds,
                        original_prov.0.clone(),
                    );
                }
            }
        }
        if let Some(quals) = iface.exported_fn_qualifiers.get(&ef.local_name) {
            self.imports
                .imported_fn_qualifiers
                .insert(effective_name, quals.clone());
        }
        // Silent trait-def import: when the re-exported fn is a trait
        // method (`ef.origin: Some(TraitName)`), pull the origin trait's
        // full def into `imported_trait_defs` so the consumer's trait
        // registry can resolve dicts at call sites, but mark the name as
        // internal so `impl Functor[X]` without an explicit import still
        // errors with `UnknownTrait`.
        if let Some(origin) = &ef.origin {
            if let Some(origin_iface) = interface_cache.get(origin.module_path.as_str()) {
                if let Some(trait_summary) = origin_iface
                    .exported_traits
                    .iter()
                    .find(|t| t.name == origin.local_name)
                {
                    let td = module_interface::trait_summary_to_exported_def(trait_summary);
                    let already = self
                        .imported_trait_defs
                        .iter()
                        .any(|x| x.name == td.name && x.module_path == td.module_path);
                    if !already {
                        self.imported_trait_defs.push(td);
                    }
                    self.trait_names.register_internal(origin);
                }
            }
        }
        Ok(())
    }

    fn bind_explicit_exported_type(
        &mut self,
        ts: &crate::module_interface::TypeSummary,
        alias: Option<&str>,
        path: &str,
        span: Span,
        is_synthetic_prelude_import: bool,
    ) -> Result<(), SpannedTypeError> {
        use crate::module_interface;

        let effective_type_name = alias
            .map(str::to_string)
            .unwrap_or_else(|| ts.name.clone());
        // Private types are already excluded from exported_types, and the
        // visibility check in Pass A catches private_names.
        if self.registry.lookup_type(&ts.name).is_none() {
            let export = module_interface::type_summary_to_export_info(ts, path);
            self.registry.register_name(&export.name);
            let constructors = type_registry::register_type_from_export(
                &export,
                &mut self.registry,
                &mut self.gen,
            )
            .map_err(|e| spanned(e, span))?;
            if effective_type_name != ts.name {
                self.registry
                    .register_type_alias(&effective_type_name, &ts.name)
                    .map_err(|e| spanned(e, span))?;
            }
            if path == "prelude" {
                self.registry.set_prelude(&ts.name);
            }
            if matches!(ts.visibility, Visibility::Pub) {
                for (cname, scheme) in constructors {
                    let kind = super::constructor_binding_kind_for_export(&export, &cname);
                    self.imports.bind_imported_constructor(
                        &mut self.env,
                        cname.clone(),
                        scheme,
                        path.to_string(),
                        export.name.clone(),
                        cname,
                        kind,
                        is_synthetic_prelude_import,
                    );
                }
            }
        } else if effective_type_name != ts.name {
            self.registry
                .register_type_alias(&effective_type_name, &ts.name)
                .map_err(|e| spanned(e, span))?;
        }
        self.registry.mark_user_visible(&ts.name);
        self.imports.bind_type_info(
            effective_type_name,
            Some(ts.name.clone()),
            path.to_string(),
            ts.visibility,
        );
        Ok(())
    }

    fn bind_explicit_reexported_type(
        &mut self,
        reex: &crate::module_interface::ReexportedTypeEntry,
        alias: Option<&str>,
        interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
        path: &str,
        span: Span,
        is_synthetic_prelude_import: bool,
    ) -> Result<(), SpannedTypeError> {
        use crate::module_interface;

        let reex_type_name = &reex.local_name;
        let effective_type_name = alias
            .map(str::to_string)
            .unwrap_or_else(|| reex_type_name.clone());
        // Re-exported type explicitly requested — mark user-visible
        self.registry.mark_user_visible(reex_type_name);
        let original_vis = reex.visibility;
        if self.registry.lookup_type(reex_type_name).is_none() {
            let orig_path = reex.canonical_ref.module.0.clone();
            let export_info = interface_cache
                .get(orig_path.as_str())
                .and_then(|orig_iface| {
                    orig_iface
                        .exported_types
                        .iter()
                        .find(|ts| ts.name == *reex_type_name)
                })
                .map(|ts| module_interface::type_summary_to_export_info(ts, &orig_path));
            if let Some(ref export) = export_info {
                self.registry.register_name(&export.name);
                let constructors = type_registry::register_type_from_export(
                    export,
                    &mut self.registry,
                    &mut self.gen,
                )
                .map_err(|e| spanned(e, span))?;
                if effective_type_name != *reex_type_name {
                    self.registry
                        .register_type_alias(&effective_type_name, reex_type_name)
                        .map_err(|e| spanned(e, span))?;
                }
                if path == "prelude" {
                    self.registry.set_prelude(&export.name);
                }
                if matches!(original_vis, Visibility::Pub) {
                    for (cname, scheme) in &constructors {
                        self.imports.bind_imported_constructor(
                            &mut self.env,
                            cname.clone(),
                            scheme.clone(),
                            orig_path.clone(),
                            reex.canonical_ref.symbol.local_name(),
                            cname.clone(),
                            super::constructor_binding_kind_for_export(export, cname),
                            is_synthetic_prelude_import,
                        );
                    }
                }
                self.imports.bind_type_info(
                    effective_type_name,
                    Some(reex.canonical_ref.symbol.local_name()),
                    orig_path,
                    original_vis,
                );
            }
        } else if effective_type_name != *reex_type_name {
            self.registry
                .register_type_alias(&effective_type_name, reex_type_name)
                .map_err(|e| spanned(e, span))?;
            self.imports.bind_type_info(
                effective_type_name,
                Some(reex.canonical_ref.symbol.local_name()),
                reex.canonical_ref.module.0.clone(),
                original_vis,
            );
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_traits_pass(
        &mut self,
        iface: &crate::module_interface::ModuleInterface,
        requested: &FxHashSet<&str>,
        import_all: bool,
        aliases: &FxHashMap<&str, &str>,
        path: &str,
        span: Span,
        is_synthetic_prelude_import: bool,
    ) -> Result<(), SpannedTypeError> {
        use crate::module_interface;

        for trait_summary in &iface.exported_traits {
            let trait_def = module_interface::trait_summary_to_exported_def(trait_summary);
            let effective_name = aliases
                .get(trait_def.name.as_str())
                .map(|a| a.to_string())
                .unwrap_or_else(|| trait_def.name.clone());

            let explicitly_requested = requested.contains(trait_def.name.as_str())
                || trait_def
                    .methods
                    .iter()
                    .any(|m| requested.contains(m.name.as_str()));

            if !(explicitly_requested || import_all) {
                continue;
            }

            // Private check stays — every import of a private trait must
            // error consistently, even if an earlier (e.g. alias-punned)
            // registration happened.
            if matches!(trait_def.visibility, Visibility::Private) {
                if explicitly_requested {
                    return Err(spanned(
                        TypeError::PrivateName {
                            name: trait_def.name.clone(),
                            module_path: path.to_string(),
                        },
                        span,
                    ));
                }
                continue;
            }

            // Build canonical TraitName (always uses original name, not alias).
            let trait_id = TraitName::new(trait_def.module_path.clone(), trait_def.name.clone());
            // Dedup imported_trait_defs so the registry doesn't see the
            // same canonical TraitName twice; trait_names handles
            // bare-name registration and ambiguity separately.
            let def_already_pushed = self
                .imported_trait_defs
                .iter()
                .any(|x| x.name == trait_def.name && x.module_path == trait_def.module_path);
            if !def_already_pushed {
                self.imported_trait_defs.push(trait_def.clone());
            }
            // Upgrade a prior silent (internal) registration by recording
            // the bare name here; `register_imported` is idempotent for
            // matching `TraitName`s so a duplicate user-level import is
            // harmless.
            self.trait_names
                .register_imported(effective_name.clone(), trait_id.clone())
                .map_err(|e| spanned(e, span))?;
            if effective_name != trait_def.name
                && !self
                    .trait_aliases
                    .iter()
                    .any(|(a, tn)| a == &effective_name && tn == &trait_id)
            {
                self.trait_aliases
                    .push((effective_name.clone(), trait_id.clone()));
            }

            let origin = Some(trait_id);
            // Bind visible trait methods as imported functions (skip if
            // already imported via fn_types). Runs on every import that
            // names the trait or one of its methods, so a name-only first
            // import does not poison a later method import of the same
            // trait.
            for method in &trait_def.methods {
                let is_visible = import_all || requested.contains(method.name.as_str());
                let already_imported = self.imports.contains_name(&method.name);
                if is_visible && !already_imported {
                    let scheme = build_trait_method_scheme(
                        &trait_def.type_var_ids,
                        &method.param_types,
                        &method.return_type,
                    );
                    self.imports.bind_import(
                        &mut self.env,
                        crate::infer::ImportBinding {
                            name: method.name.clone(),
                            scheme,
                            origin: origin.clone(),
                            source_module: path.to_string(),
                            original_name: method.name.clone(),
                            is_prelude: is_synthetic_prelude_import,
                            span,
                        },
                    )?;
                }
            }
        }
        Ok(())
    }

    fn bind_qualified_exports_for_import_all(
        &mut self,
        iface: &crate::module_interface::ModuleInterface,
        interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
        path: &str,
        qualifier_name: &str,
        is_synthetic_prelude_import: bool,
        qualified_exports: &mut FxHashMap<String, QualifiedExport>,
    ) {
        for ef in &iface.exported_fns {
            let hidden_name = format!("__qual${}${}", qualifier_name, ef.name);
            qualified_exports.insert(
                ef.name.clone(),
                QualifiedExport {
                    local_name: hidden_name.clone(),
                    scheme: ef.scheme.clone(),
                    resolved_ref: Some(imported_binding_ref(path.to_string(), ef.name.clone())),
                },
            );
            self.imports.bind_hidden_fn(
                hidden_name,
                ef.scheme.clone(),
                ef.origin.clone(),
                (path.to_string(), ef.name.clone()),
                is_synthetic_prelude_import,
            );
        }

        for ef in &iface.reexported_fns {
            let hidden_name = format!("__qual${}${}", qualifier_name, ef.local_name);
            let canonical_name = ef.canonical_ref.symbol.local_name();
            let original_prov = (ef.canonical_ref.module.0.clone(), canonical_name.clone());
            qualified_exports.insert(
                ef.local_name.clone(),
                QualifiedExport {
                    local_name: hidden_name.clone(),
                    scheme: ef.scheme.clone(),
                    resolved_ref: Some(match &ef.canonical_ref.symbol {
                        crate::module_interface::LocalSymbolKey::Constructor {
                            parent_type,
                            name,
                        } => constructor_binding_ref(
                            original_prov.0.clone(),
                            parent_type.clone(),
                            name.clone(),
                            match interface_cache
                                .get(original_prov.0.as_str())
                                .and_then(|orig_iface| {
                                    orig_iface
                                        .exported_types
                                        .iter()
                                        .find(|ts| ts.name == *parent_type)
                                })
                                .map(constructor_kind_from_summary)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "ICE: constructor parent type '{}' not in exported_types for module {}",
                                        parent_type, original_prov.0
                                    )
                                }) {
                                crate::types::ConstructorBindingKind::Record => {
                                    crate::typed_ast::ConstructorKind::Record
                                }
                                crate::types::ConstructorBindingKind::Variant => {
                                    crate::typed_ast::ConstructorKind::Variant
                                }
                            },
                        ),
                        _ => imported_binding_ref(original_prov.0.clone(), original_prov.1.clone()),
                    }),
                },
            );
            match &ef.canonical_ref.symbol {
                crate::module_interface::LocalSymbolKey::Constructor { .. } => {
                    self.imports.bind_hidden_constructor(
                        hidden_name,
                        ef.scheme.clone(),
                        original_prov.0,
                        original_prov.1,
                        is_synthetic_prelude_import,
                    );
                }
                _ => {
                    self.imports.bind_hidden_fn(
                        hidden_name,
                        ef.scheme.clone(),
                        ef.origin.clone(),
                        original_prov,
                        is_synthetic_prelude_import,
                    );
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_types_pass(
        &mut self,
        iface: &crate::module_interface::ModuleInterface,
        requested: &FxHashSet<&str>,
        import_all: bool,
        path: &str,
        qualifier_name: &str,
        span: Span,
        is_synthetic_prelude_import: bool,
        qualified_exports: &mut FxHashMap<String, QualifiedExport>,
    ) -> Result<(), SpannedTypeError> {
        use crate::module_interface;

        for ts in &iface.exported_types {
            if requested.contains(ts.name.as_str()) {
                // Explicit-name binding for this type already happened in Pass B.
                continue;
            }
            if import_all {
                if matches!(ts.visibility, Visibility::Private) {
                    continue;
                }
                self.registry.mark_user_visible(&ts.name);
                if self.registry.lookup_type(&ts.name).is_none() {
                    let export = module_interface::type_summary_to_export_info(ts, path);
                    self.registry.register_name(&export.name);
                    let constructors = type_registry::register_type_from_export(
                        &export,
                        &mut self.registry,
                        &mut self.gen,
                    )
                    .map_err(|e| spanned(e, span))?;
                    if path == "prelude" {
                        self.registry.set_prelude(&ts.name);
                    }
                    if matches!(ts.visibility, Visibility::Pub) {
                        for (cname, scheme) in constructors {
                            let hidden_name = format!("__qual${}${}", qualifier_name, cname);
                            let kind = super::constructor_binding_kind_for_export(&export, &cname);
                            qualified_exports.insert(
                                cname.clone(),
                                QualifiedExport {
                                    local_name: hidden_name.clone(),
                                    scheme: scheme.clone(),
                                    resolved_ref: Some(constructor_binding_ref(
                                        path.to_string(),
                                        export.name.clone(),
                                        cname.clone(),
                                        match kind {
                                            crate::types::ConstructorBindingKind::Record => {
                                                crate::typed_ast::ConstructorKind::Record
                                            }
                                            crate::types::ConstructorBindingKind::Variant => {
                                                crate::typed_ast::ConstructorKind::Variant
                                            }
                                        },
                                    )),
                                },
                            );
                            self.imports.bind_hidden_constructor(
                                hidden_name,
                                scheme.clone(),
                                path.to_string(),
                                cname.clone(),
                                is_synthetic_prelude_import,
                            );
                            self.env.bind_constructor(
                                cname.clone(),
                                scheme,
                                path.to_string(),
                                export.name.clone(),
                                cname.clone(),
                                kind,
                            );
                        }
                    }
                }
            } else if self.registry.lookup_type(&ts.name).is_none() {
                // Not explicitly requested and not import_all — register
                // type silently (needed for constructor resolution).
                let export = module_interface::type_summary_to_export_info(ts, path);
                self.registry.register_name(&export.name);
                let constructors = type_registry::register_type_from_export(
                    &export,
                    &mut self.registry,
                    &mut self.gen,
                )
                .map_err(|e| spanned(e, span))?;
                for (cname, scheme) in constructors {
                    let kind = super::constructor_binding_kind_for_export(&export, &cname);
                    self.env.bind_constructor(
                        cname.clone(),
                        scheme,
                        path.to_string(),
                        export.name.clone(),
                        cname,
                        kind,
                    );
                }
                self.imports.bind_type_info(
                    ts.name.clone(),
                    Some(ts.name.clone()),
                    path.to_string(),
                    ts.visibility,
                );
            }
        }
        Ok(())
    }

    fn bind_extern_type_visibility(
        &mut self,
        iface: &crate::module_interface::ModuleInterface,
        requested: &FxHashSet<&str>,
        import_all: bool,
        path: &str,
    ) {
        for et in &iface.extern_types {
            let name = &et.krypton_name;
            if requested.contains(name.as_str()) || import_all {
                self.registry.mark_user_visible(name);
            }
            let vis = iface
                .type_visibility
                .get(name)
                .copied()
                .unwrap_or(Visibility::Private);
            self.imports
                .bind_type_info(name.clone(), Some(name.clone()), path.to_string(), vis);
        }
    }

}

/// Build the generalized `TypeScheme` for a trait method, generalizing
/// over both trait-level params and the method's own type parameters.
/// Trait-declaration order comes first (so `[a, b]` on `Convert[a, b]`
/// stays `a, b`), then method-signature order for the remaining vars.
/// Ordering is load-bearing — user pins like `xs.map[String]` resolve
/// positionally against this list.
fn build_trait_method_scheme(
    trait_type_var_ids: &[crate::types::TypeVarId],
    param_types: &[(crate::types::ParamMode, Type)],
    return_type: &Type,
) -> TypeScheme {
    let fn_ty = Type::Fn(param_types.to_vec(), Box::new(return_type.clone()));
    let mut vars: Vec<crate::types::TypeVarId> = trait_type_var_ids.to_vec();
    let mut seen: FxHashSet<crate::types::TypeVarId> = vars.iter().copied().collect();
    for tv in super::free_vars_ordered(&fn_ty) {
        if seen.insert(tv) {
            vars.push(tv);
        }
    }
    TypeScheme {
        vars,
        constraints: Vec::new(),
        ty: fn_ty,
        var_names: FxHashMap::default(),
    }
}
