use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, ImportName, Module, Span, TypeDecl, Visibility};

use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::ExportedTypeInfo;
use crate::typed_ast::{self as typed_ast, TraitName, TypedModule};
use crate::types::{Type, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::{
    build_type_param_map, constructor_names, find_type_decl, process_extern_methods, spanned,
    ModuleInferenceState, QualifiedExport, QualifiedModuleBinding,
};

/// Register a type using pre-resolved export info if available,
/// falling back to processing the type declaration from AST.
fn register_type_with_fallback(
    export_info: Option<&ExportedTypeInfo>,
    td: &TypeDecl,
    registry: &mut TypeRegistry,
    gen: &mut TypeVarGen,
    span: Span,
) -> Result<Vec<(String, TypeScheme)>, SpannedTypeError> {
    if let Some(export) = export_info {
        registry.register_name(&export.name);
        type_registry::register_type_from_export(export, registry, gen)
            .map_err(|e| spanned(e, span))
    } else {
        registry.register_name(&td.name);
        type_registry::process_type_decl(td, registry, gen)
            .map_err(|e| spanned(e, span))
    }
}

impl ModuleInferenceState {
    /// Build a synthetic `Decl::Import` for the prelude, gathering all re-exported names
    /// from the cached prelude module. Returns `None` when we ARE the prelude or it
    /// isn't cached yet.
    pub(super) fn build_synthetic_prelude_import(
        &mut self,
        is_prelude_tree: bool,
        cache: &HashMap<String, TypedModule>,
        parsed_modules: &HashMap<String, &Module>,
    ) -> Option<Decl> {
        if is_prelude_tree {
            return None;
        }
        let cached = cache.get("prelude")?;

        let mut names: Vec<ImportName> = Vec::new();

        // Re-exported type names (e.g. Option, Result, List, Ordering)
        for type_name in &cached.reexported_type_names {
            names.push(ImportName {
                name: type_name.clone(),
                alias: None,
            });
        }

        // Build set of constructor names from pub (transparent) re-exported types,
        // so we can exclude them from the re-exported fn list (they come from type processing).
        let mut prelude_constructor_names: HashSet<String> = HashSet::new();
        for type_name in &cached.reexported_type_names {
            let vis = cached
                .reexported_type_visibility
                .get(type_name)
                .cloned()
                .unwrap_or(Visibility::Opaque);
            if matches!(vis, Visibility::Pub) {
                if let Some(orig_path) = cached.type_provenance.get(type_name) {
                    if let Some(orig_module) = parsed_modules.get(orig_path.as_str()) {
                        if let Some(td) = find_type_decl(&orig_module.decls, type_name) {
                            prelude_constructor_names.extend(constructor_names(td));
                        }
                    }
                }
            }
        }

        // Re-exported trait names (e.g. Eq, Show, Semigroup, etc.)
        for trait_def in &cached.exported_trait_defs {
            names.push(ImportName {
                name: trait_def.name.clone(),
                alias: None,
            });
        }

        // Re-exported functions (e.g. println), excluding constructors
        // that will be bound via type processing
        for ef in &cached.reexported_fn_types {
            if !prelude_constructor_names.contains(&ef.name) {
                names.push(ImportName {
                    name: ef.name.clone(),
                    alias: None,
                });
            }
        }

        // Track which names came from the prelude so we can remove shadowed
        // entries from imported_fn_constraint_requirements later.
        for n in &names {
            self.prelude_imported_names.insert(n.name.clone());
        }

        Some(Decl::Import {
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
        cache: &mut HashMap<String, TypedModule>,
        parsed_modules: &HashMap<String, &Module>,
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
            } = decl
            {
                self.process_single_import(
                    *is_pub,
                    path,
                    names,
                    *span,
                    cache,
                    parsed_modules,
                )?;
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
        cache: &mut HashMap<String, TypedModule>,
        parsed_modules: &HashMap<String, &Module>,
    ) -> Result<(), SpannedTypeError> {
        // Graph builder already validated: no cycles and no unknown modules.
        let imported_module = parsed_modules
            .get(path)
            .expect("module graph should contain all imported modules");

        // Module should already be type-checked (topological order guarantees this)
        assert!(
            cache.contains_key(path),
            "module {path} should be in cache (topological order)"
        );

        let requested: HashSet<&str> = names.iter().map(|n| n.name.as_str()).collect();
        let import_all = names.is_empty();

        // Build alias map from ImportName
        let aliases: HashMap<String, String> = names
            .iter()
            .filter_map(|n| n.alias.as_ref().map(|a| (n.name.clone(), a.clone())))
            .collect();

        // Extract type signatures from cached module and bind with provenance.
        let cached = cache.get(path).unwrap();
        let qualifier_name = path.rsplit('/').next().unwrap_or(path).to_string();
        let mut qualified_exports: HashMap<String, QualifiedExport> = HashMap::new();

        // Check for explicitly requested names that exist in fn_types but not
        // in exported_fn_types — these are private/non-exported names.
        let exported_fn_names: HashSet<&str> = cached
            .exported_fn_types
            .iter()
            .map(|ef| ef.name.as_str())
            .collect();
        let reexported_fn_names: HashSet<&str> = cached
            .reexported_fn_types
            .iter()
            .map(|ef| ef.name.as_str())
            .collect();
        // Build set of names importable via type/trait paths (not fn_types)
        let type_or_trait_names: HashSet<&str> = {
            let mut s: HashSet<&str> = HashSet::new();
            for d in &imported_module.decls {
                if let Decl::DefType(td) = d {
                    if !matches!(td.visibility, Visibility::Private) {
                        s.insert(&td.name);
                    }
                }
                if let Decl::DefTrait { name, .. } = d {
                    s.insert(name);
                }
                // Extern java type aliases (e.g. `extern "..." as Ref[m] {}`)
                if let Decl::ExternJava { alias: Some(name), .. } = d {
                    s.insert(name);
                }
            }
            for tn in &cached.reexported_type_names {
                s.insert(tn);
            }
            for td in &cached.exported_trait_defs {
                s.insert(&td.name);
                for m in &td.methods {
                    s.insert(&m.name);
                }
            }
            s
        };
        // Build fn visibility map from parsed imported module (needed for extern method privacy)
        let mut fn_vis: HashMap<&str, &Visibility> = HashMap::new();
        for d in &imported_module.decls {
            if let Decl::ExternJava { methods, .. } = d {
                for m in methods {
                    fn_vis.entry(m.name.as_str()).or_insert(&m.visibility);
                }
            }
        }

        for name in &requested {
            if !exported_fn_names.contains(name) && !reexported_fn_names.contains(name)
                && !type_or_trait_names.contains(name)
            {
                // Check if the name exists in fn_types (i.e. it's private, not missing)
                let exists_in_fn_types = cached.fn_types.iter().any(|e| e.name.as_str() == *name);
                if exists_in_fn_types {
                    return Err(spanned(
                        TypeError::PrivateName {
                            name: name.to_string(),
                            module_path: path.to_string(),
                        },
                        span,
                    ));
                }
                // Check if it's a private type
                let is_private_type = imported_module.decls.iter().any(|d| {
                    matches!(d, Decl::DefType(td) if td.name.as_str() == *name && matches!(td.visibility, Visibility::Private))
                });
                if is_private_type {
                    return Err(spanned(
                        TypeError::PrivateName {
                            name: name.to_string(),
                            module_path: path.to_string(),
                        },
                        span,
                    ));
                }
                // Extern methods are handled separately below
                if fn_vis.contains_key(name) {
                    continue;
                }
                // Name truly doesn't exist in the module
                return Err(spanned(
                    TypeError::UnknownExport {
                        name: name.to_string(),
                        module_path: path.to_string(),
                    },
                    span,
                ));
            }
        }

        // Check visibility of explicitly requested extern methods
        for name in &requested {
            if let Some(vis) = fn_vis.get(name) {
                if matches!(vis, Visibility::Private) {
                    return Err(spanned(
                        TypeError::PrivateName {
                            name: name.to_string(),
                            module_path: path.to_string(),
                        },
                        span,
                    ));
                }
            }
        }

        for ef in &cached.exported_fn_types {
            if reexported_fn_names.contains(ef.name.as_str()) {
                continue;
            }
            if requested.contains(ef.name.as_str()) {
                let effective_name = aliases.get(&ef.name).cloned().unwrap_or_else(|| ef.name.clone());
                self.imports.bind_import(&mut self.env, effective_name.clone(), ef.scheme.clone(), ef.origin.clone(), path.to_string(), ef.name.clone(), &self.prelude_imported_names, &mut self.gen, span, &mut self.imported_fn_constraint_requirements)?;
                // Store definition span for imported function
                if let Some(ds) = ef.def_span {
                    self.env.bind_with_def_span(
                        effective_name.clone(),
                        ef.scheme.clone(),
                        crate::types::DefSpan { span: ds, source_module: Some(path.to_string()) },
                    );
                }
                if let Some(quals) = cached.exported_fn_qualifiers.get(&ef.name) {
                    self.imports.imported_fn_qualifiers.insert(effective_name, quals.clone());
                }
            } else if import_all {
                let hidden_name = format!("__qual${}${}", qualifier_name, ef.name);
                qualified_exports.insert(
                    ef.name.clone(),
                    QualifiedExport {
                        local_name: hidden_name.clone(),
                        scheme: ef.scheme.clone(),
                    },
                );
                self.imports.bind_hidden_fn(hidden_name, ef.scheme.clone(), ef.origin.clone(), (path.to_string(), ef.name.clone()));
            }
        }

        for ef in &cached.reexported_fn_types {
            if import_all {
                let hidden_name = format!("__qual${}${}", qualifier_name, ef.name);
                let original_prov = cached.fn_types.iter()
                    .find(|e| e.name == ef.name)
                    .and_then(|e| e.provenance.clone())
                    .unwrap_or_else(|| (path.to_string(), ef.name.clone()));
                qualified_exports.insert(
                    ef.name.clone(),
                    QualifiedExport {
                        local_name: hidden_name.clone(),
                        scheme: ef.scheme.clone(),
                    },
                );
                self.imports.bind_hidden_fn(hidden_name, ef.scheme.clone(), ef.origin.clone(), original_prov);
            }
        }

        // Process re-exported functions from the cached module.
        for ef in &cached.reexported_fn_types {
            if requested.contains(ef.name.as_str()) {
                let effective_name = aliases.get(&ef.name).cloned().unwrap_or_else(|| ef.name.clone());
                let original_prov = cached.fn_types.iter()
                    .find(|e| e.name == ef.name)
                    .and_then(|e| e.provenance.clone())
                    .unwrap_or_else(|| (path.to_string(), ef.name.clone()));
                self.env.bind_with_provenance(effective_name.clone(), ef.scheme.clone(), path.to_string());
                // Store definition span for re-exported function
                if let Some(ds) = ef.def_span {
                    let source_module = original_prov.0.clone();
                    self.env.bind_with_def_span(
                        effective_name.clone(),
                        ef.scheme.clone(),
                        crate::types::DefSpan { span: ds, source_module: Some(source_module) },
                    );
                }
                self.imports.imported_fn_types.push(typed_ast::ImportedFn {
                    name: effective_name.clone(),
                    scheme: ef.scheme.clone(),
                    origin: ef.origin.clone(),
                    source_module: original_prov.0,
                    original_name: original_prov.1,
                });
                if let Some(quals) = cached.exported_fn_qualifiers.get(&ef.name) {
                    self.imports.imported_fn_qualifiers.insert(effective_name, quals.clone());
                }
            }
        }

        // Process re-exported types from the cached module
        for reex_type_name in &cached.reexported_type_names {
            if requested.contains(reex_type_name.as_str()) {
                let effective_type_name = aliases
                    .get(reex_type_name)
                    .cloned()
                    .unwrap_or_else(|| reex_type_name.clone());
                // Re-exported type explicitly requested — mark user-visible
                // mark_user_visible canonicalizes internally, so one call suffices
                self.registry.mark_user_visible(reex_type_name);
                let original_vis = cached
                    .reexported_type_visibility
                    .get(reex_type_name)
                    .cloned()
                    .unwrap_or(Visibility::Opaque);
                if self.registry.lookup_type(reex_type_name).is_none() {
                    let original_path = cached.type_provenance.get(reex_type_name);
                    // Try pre-resolved export from the original source module's cache
                    let export_info = original_path.as_ref().and_then(|orig_path| {
                        cache.get(orig_path.as_str())
                            .and_then(|orig_cached| orig_cached.exported_type_infos.get(reex_type_name.as_str()))
                            .cloned()
                    });
                    if let Some(ref export) = export_info {
                        let orig_path = original_path.unwrap();
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
                                self.imports.bind_import(&mut self.env, cname.clone(), scheme.clone(), None, orig_path.clone(), cname.clone(), &self.prelude_imported_names, &mut self.gen, span, &mut self.imported_fn_constraint_requirements)?;
                            }
                        }
                        self.imports.bind_type_info(
                            effective_type_name.clone(),
                            orig_path.clone(),
                            original_vis.clone(),
                        );
                        self.type_provenance.insert(export.name.clone(), orig_path.clone());
                    } else if let Some(orig_path) = original_path {
                        if let Some(orig_module) = parsed_modules.get(orig_path.as_str()) {
                            if let Some(td) = find_type_decl(&orig_module.decls, reex_type_name)
                            {
                                self.registry.register_name(&td.name);
                                let constructors = type_registry::process_type_decl(
                                    td,
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
                                    self.registry.set_prelude(&td.name);
                                }
                                if matches!(original_vis, Visibility::Pub) {
                                    for (cname, scheme) in &constructors {
                                        self.imports.bind_import(&mut self.env, cname.clone(), scheme.clone(), None, orig_path.clone(), cname.clone(), &self.prelude_imported_names, &mut self.gen, span, &mut self.imported_fn_constraint_requirements)?;
                                    }
                                }
                                self.imports.bind_type_info(
                                    effective_type_name.clone(),
                                    orig_path.clone(),
                                    original_vis.clone(),
                                );
                                self.type_provenance.insert(td.name.clone(), orig_path.clone());
                            }
                        }
                    }
                } else if effective_type_name != *reex_type_name {
                    self.registry
                        .register_type_alias(&effective_type_name, reex_type_name)
                        .map_err(|e| spanned(e, span))?;
                    self.imports.bind_type_info(
                        effective_type_name.clone(),
                        path.to_string(),
                        original_vis.clone(),
                    );
                }
            }
        }

        // Process type declarations from imported module source with visibility enforcement
        for sdecl in &imported_module.decls {
            if let Decl::DefType(td) = sdecl {
                if requested.contains(td.name.as_str()) {
                    let effective_type_name = aliases
                        .get(&td.name)
                        .cloned()
                        .unwrap_or_else(|| td.name.clone());
                    if matches!(td.visibility, Visibility::Private) {
                        return Err(spanned(
                            TypeError::PrivateName {
                                name: td.name.clone(),
                                module_path: path.to_string(),
                            },
                            span,
                        ));
                    }
                    if self.registry.lookup_type(&td.name).is_none() {
                        let constructors = register_type_with_fallback(
                            cached.exported_type_infos.get(td.name.as_str()),
                            td, &mut self.registry, &mut self.gen, span,
                        )?;
                        if effective_type_name != td.name {
                            self.registry
                                .register_type_alias(&effective_type_name, &td.name)
                                .map_err(|e| spanned(e, span))?;
                        }
                        if path == "prelude" {
                            self.registry.set_prelude(&td.name);
                        }
                        if matches!(td.visibility, Visibility::Pub) {
                            for (cname, scheme) in constructors {
                                self.env.bind(cname, scheme);
                            }
                        }
                    } else if effective_type_name != td.name {
                        self.registry
                            .register_type_alias(&effective_type_name, &td.name)
                            .map_err(|e| spanned(e, span))?;
                    }
                    // Branch A: type explicitly requested — mark user-visible
                    // mark_user_visible canonicalizes internally, so one call suffices
                    self.registry.mark_user_visible(&td.name);
                    self.imports.bind_type_info(effective_type_name.clone(), path.to_string(), td.visibility.clone());
                    self.type_provenance.insert(td.name.clone(), path.to_string());
                } else if import_all {
                    if matches!(td.visibility, Visibility::Private) {
                        continue;
                    }
                    // Branch B: import_all — mark user-visible
                    self.registry.mark_user_visible(&td.name);
                    if self.registry.lookup_type(&td.name).is_none() {
                        let constructors = register_type_with_fallback(
                            cached.exported_type_infos.get(td.name.as_str()),
                            td, &mut self.registry, &mut self.gen, span,
                        )?;
                        if path == "prelude" {
                            self.registry.set_prelude(&td.name);
                        }
                        if matches!(td.visibility, Visibility::Pub) {
                            for (cname, scheme) in constructors {
                                let hidden_name =
                                    format!("__qual${}${}", qualifier_name, cname);
                                qualified_exports.insert(
                                    cname.clone(),
                                    QualifiedExport {
                                        local_name: hidden_name.clone(),
                                        scheme: scheme.clone(),
                                    },
                                );
                                self.imports.bind_hidden_fn(hidden_name, scheme.clone(), None, (path.to_string(), cname.clone()));
                                self.env.bind(cname, scheme);
                            }
                        }
                    }
                } else if self.registry.lookup_type(&td.name).is_none() {
                    let constructors = register_type_with_fallback(
                        cached.exported_type_infos.get(td.name.as_str()),
                        td, &mut self.registry, &mut self.gen, span,
                    )?;
                    for (cname, scheme) in constructors {
                        self.env.bind(cname, scheme);
                    }
                    // Track the parent type so codegen can resolve it
                    // (importing constructors implicitly depends on the type)
                    self.imports.bind_type_info(td.name.clone(), path.to_string(), td.visibility.clone());
                    self.type_provenance.insert(td.name.clone(), path.to_string());
                }
            }
        }

        // Store qualified module binding *after* type processing so pub (transparent) constructor
        // entries added above are captured in qualified_exports.
        if import_all {
            self.qualified_modules.insert(
                qualifier_name.clone(),
                QualifiedModuleBinding {
                    module_path: path.to_string(),
                    exports: qualified_exports.clone(),
                },
            );
        }

        // Process extern declarations from imported module
        for sdecl in &imported_module.decls {
            if let Decl::ExternJava {
                class_name,
                alias,
                type_params,
                methods,
                span: ext_span,
                ..
            } = sdecl
            {
                // Register extern java type binding if present
                let mut tp_map: Option<HashMap<String, TypeVarId>> = None;
                let mut tp_arity: Option<HashMap<String, usize>> = None;
                if let Some(name) = alias {
                    let type_param_vars = if let Some(existing) = self.registry.lookup_type(name) {
                        existing.type_param_vars.clone()
                    } else {
                        let vars: Vec<_> = type_params.iter().map(|_| self.gen.fresh()).collect();
                        let _ = self.registry.register_type(crate::type_registry::TypeInfo {
                            name: name.clone(),
                            type_params: type_params.clone(),
                            type_param_vars: vars.clone(),
                            kind: crate::type_registry::TypeKind::Record { fields: vec![] },
                            is_prelude: false,
                        });
                        self.imported_extern_java_types.push((name.clone(), class_name.clone()));
                        vars
                    };
                    // Mark user-visible if explicitly requested or import_all
                    if requested.contains(name.as_str()) || import_all {
                        self.registry.mark_user_visible(name);
                    }
                    // Track visibility so pub re-exports can find this type
                    let vis = cached.type_visibility.get(name).cloned().unwrap_or(Visibility::Private);
                    self.imports.bind_type_info(name.clone(), path.to_string(), vis);

                    // Build type_param_map for method resolution
                    if !type_params.is_empty() {
                        let (map, arity) = build_type_param_map(type_params, &type_param_vars, name);
                        tp_map = Some(map);
                        tp_arity = Some(arity);
                    }
                }

                let tp_names = type_params.as_slice();
                let mut fns = process_extern_methods(
                    class_name, methods, &mut self.env, &mut self.gen, &self.registry, *ext_span, None,
                    &aliases, tp_map.as_ref(), tp_arity.as_ref(),
                    if tp_map.is_some() { Some(tp_names) } else { None },
                )?;
                self.imported_extern_fns.append(&mut fns);
            }
        }

        // Copy imported extern fns for codegen
        for ext in &cached.extern_fns {
            self.imported_extern_fns.push(ext.clone());
        }
        for ext in &cached.imported_extern_fns {
            self.imported_extern_fns.push(ext.clone());
        }

        // Copy imported extern java types for codegen
        for entry in &cached.extern_java_types {
            self.imported_extern_java_types.push(entry.clone());
        }
        for entry in &cached.imported_extern_java_types {
            self.imported_extern_java_types.push(entry.clone());
        }

        // Propagate fn_constraint_requirements (TypeVarId-based) for cross-module codegen.
        for (name, requirements) in &cached.fn_constraint_requirements {
            let effective_name = aliases.get(name).cloned().unwrap_or_else(|| name.clone());
            if requested.contains(name.as_str()) || import_all {
                self.imported_fn_constraint_requirements
                    .entry(effective_name)
                    .or_insert_with(|| requirements.clone());
            }
        }
        for (name, requirements) in &cached.imported_fn_constraint_requirements {
            let effective_name = aliases.get(name).cloned().unwrap_or_else(|| name.clone());
            if requested.contains(name.as_str()) || import_all {
                self.imported_fn_constraint_requirements
                    .entry(effective_name)
                    .or_insert_with(|| requirements.clone());
            }
        }

        // Propagate trait definitions from the imported module
        for trait_def in &cached.exported_trait_defs {
            let explicitly_requested = requested.contains(trait_def.name.as_str())
                || trait_def
                    .methods
                    .iter()
                    .any(|m| requested.contains(m.name.as_str()));
            if (explicitly_requested || import_all)
                && !self.imported_trait_names.contains(&trait_def.name)
            {
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
                self.imported_trait_defs.push(trait_def.clone());
                self.imported_trait_names.insert(trait_def.name.clone());
                // Bind visible trait methods as imported functions (skip if already imported via fn_types)
                let trait_id = TraitName::new(
                    trait_def.module_path.clone().or_else(|| Some(path.to_string())),
                    trait_def.name.clone(),
                );
                let origin = Some(trait_id);
                for method in &trait_def.methods {
                    let is_visible = import_all || requested.contains(method.name.as_str());
                    let already_imported = self.imports.imported_fn_types.iter().any(|f| f.name == method.name);
                    if is_visible && !already_imported {
                        let fn_ty = Type::Fn(method.param_types.clone(), Box::new(method.return_type.clone()));
                        let scheme = TypeScheme {
                            vars: vec![trait_def.type_var_id],
                            ty: fn_ty,
                            var_names: HashMap::new(),
                        };
                        self.imports.bind_import(&mut self.env, method.name.clone(), scheme, origin.clone(), path.to_string(), method.name.clone(), &self.prelude_imported_names, &mut self.gen, span, &mut self.imported_fn_constraint_requirements)?;
                    }
                }
                let prov = cached
                    .type_provenance
                    .get(&trait_def.name)
                    .cloned()
                    .unwrap_or_else(|| path.to_string());
                self.type_provenance.insert(trait_def.name.clone(), prov);
            }
        }

        // Process pub import re-exports
        if is_pub {
            for import_name in names {
                let effective_name = import_name
                    .alias
                    .as_ref()
                    .unwrap_or(&import_name.name)
                    .clone();
                let found_fn = self.imports.imported_fn_types.iter().any(|f| f.name == effective_name);
                let found_type = self.imports.imported_type_info.contains_key(&effective_name);
                let found_trait = self.imported_trait_names.contains(&effective_name);

                if !found_fn && !found_type && !found_trait {
                    return Err(spanned(
                        TypeError::PrivateReexport {
                            name: effective_name.clone(),
                        },
                        span,
                    ));
                }
                if found_fn {
                    if let Some(f) = self.imports.imported_fn_types
                        .iter()
                        .find(|f| f.name == effective_name)
                    {
                        // Try to propagate def_span from the source module's exports
                        let reexport_def_span = self.env.get_def_span(&effective_name)
                            .map(|d| d.span);
                        self.reexported_fn_types.push(typed_ast::ExportedFn {
                            name: effective_name.clone(),
                            scheme: f.scheme.clone(),
                            origin: f.origin.clone(),
                            def_span: reexport_def_span,
                        });
                    }
                }
                if found_type {
                    self.reexported_type_names.push(effective_name.clone());
                    let original_vis = self.imports.imported_type_info
                        .get(&effective_name)
                        .map(|(_, vis)| vis.clone())
                        .unwrap_or(Visibility::Opaque);
                    self.reexported_type_visibility.insert(effective_name.clone(), original_vis);
                }
                if found_trait {
                    if let Some(td) = self.imported_trait_defs
                        .iter()
                        .find(|td| td.name == effective_name)
                    {
                        self.reexported_trait_defs.push(td.clone());
                    }
                }
            }
        }

        Ok(())
    }
}
