use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, ImportName, Module, Span, Visibility};

use crate::type_registry::{self};
use crate::typed_ast::{FnOrigin, TypedModule};
use crate::types::{Type, TypeScheme};
use crate::unify::{SpannedTypeError, TypeError};

use super::{
    constructor_names, find_type_decl, process_extern_methods, spanned, ModuleInferenceState,
    QualifiedExport, QualifiedModuleBinding,
};

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

        // Re-exported trait names (e.g. Eq, Show, Add, etc.)
        for trait_def in &cached.exported_trait_defs {
            names.push(ImportName {
                name: trait_def.name.clone(),
                alias: None,
            });
        }

        // Re-exported functions (e.g. println), excluding constructors
        // that will be bound via type processing
        for (name, _, _) in &cached.reexported_fn_types {
            if !prelude_constructor_names.contains(name) {
                names.push(ImportName {
                    name: name.clone(),
                    alias: None,
                });
            }
        }

        // Track which names came from the prelude so we can remove shadowed
        // entries from imported_fn_constraints later.
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
            .map(|(n, _, _)| n.as_str())
            .collect();
        let reexported_fn_names: HashSet<&str> = cached
            .reexported_fn_types
            .iter()
            .map(|(n, _, _)| n.as_str())
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
        for name in &requested {
            if !exported_fn_names.contains(name) && !reexported_fn_names.contains(name)
                && !type_or_trait_names.contains(name)
            {
                // Check if the name exists in fn_types (i.e. it's private, not missing)
                let exists_in_fn_types = cached.fn_types.iter().any(|(n, _, _)| n.as_str() == *name);
                if exists_in_fn_types {
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

        // Build fn visibility map from parsed imported module (needed for extern method privacy)
        let mut fn_vis: HashMap<&str, &Visibility> = HashMap::new();
        for d in &imported_module.decls {
            if let Decl::ExternJava { methods, .. } = d {
                for m in methods {
                    fn_vis.entry(m.name.as_str()).or_insert(&m.visibility);
                }
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

        for (name, scheme, origin) in &cached.exported_fn_types {
            if reexported_fn_names.contains(name.as_str()) {
                continue;
            }
            if requested.contains(name.as_str()) {
                let effective_name = aliases.get(name).cloned().unwrap_or_else(|| name.clone());
                self.env.bind_with_provenance(effective_name.clone(), scheme.clone(), path.to_string());
                self.imported_fn_types.push((effective_name.clone(), scheme.clone(), origin.clone()));
                self.fn_provenance_map.insert(effective_name, (path.to_string(), name.clone()));
            } else if import_all {
                let hidden_name = format!("__qual${}${}", qualifier_name, name);
                qualified_exports.insert(
                    name.clone(),
                    QualifiedExport {
                        local_name: hidden_name.clone(),
                        scheme: scheme.clone(),
                    },
                );
                self.imported_fn_types.push((hidden_name.clone(), scheme.clone(), origin.clone()));
                self.fn_provenance_map.insert(hidden_name, (path.to_string(), name.clone()));
            }
        }

        for (name, scheme, origin) in &cached.reexported_fn_types {
            if import_all {
                let hidden_name = format!("__qual${}${}", qualifier_name, name);
                let original_prov = cached
                    .fn_provenance
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| (path.to_string(), name.clone()));
                qualified_exports.insert(
                    name.clone(),
                    QualifiedExport {
                        local_name: hidden_name.clone(),
                        scheme: scheme.clone(),
                    },
                );
                self.imported_fn_types.push((hidden_name.clone(), scheme.clone(), origin.clone()));
                self.fn_provenance_map.insert(hidden_name, original_prov);
            }
        }

        // Process re-exported functions from the cached module.
        for (name, scheme, origin) in &cached.reexported_fn_types {
            if requested.contains(name.as_str()) {
                let effective_name = aliases.get(name).cloned().unwrap_or_else(|| name.clone());
                self.env.bind_with_provenance(effective_name.clone(), scheme.clone(), path.to_string());
                self.imported_fn_types.push((effective_name.clone(), scheme.clone(), origin.clone()));
                let original_prov = cached
                    .fn_provenance
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| (path.to_string(), name.clone()));
                self.fn_provenance_map.insert(effective_name, original_prov);
            }
        }

        // Process re-exported types from the cached module
        for reex_type_name in &cached.reexported_type_names {
            if requested.contains(reex_type_name.as_str()) {
                let effective_type_name = aliases
                    .get(reex_type_name)
                    .cloned()
                    .unwrap_or_else(|| reex_type_name.clone());
                let original_vis = cached
                    .reexported_type_visibility
                    .get(reex_type_name)
                    .cloned()
                    .unwrap_or(Visibility::Opaque);
                if self.registry.lookup_type(reex_type_name).is_none() {
                    let original_path = cached.type_provenance.get(reex_type_name);
                    if let Some(orig_path) = original_path {
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
                                        self.env.bind(cname.clone(), scheme.clone());
                                        self.imported_fn_types.push((cname.clone(), scheme.clone(), FnOrigin::Regular));
                                        self.fn_provenance_map.insert(
                                            cname.clone(),
                                            (orig_path.clone(), cname.clone()),
                                        );
                                    }
                                }
                                self.imported_type_info.insert(
                                    effective_type_name.clone(),
                                    (orig_path.clone(), original_vis.clone()),
                                );
                                self.type_provenance.insert(td.name.clone(), orig_path.clone());
                            }
                        }
                    }
                } else if effective_type_name != *reex_type_name {
                    self.registry
                        .register_type_alias(&effective_type_name, reex_type_name)
                        .map_err(|e| spanned(e, span))?;
                    self.imported_type_info.insert(
                        effective_type_name.clone(),
                        (path.to_string(), original_vis.clone()),
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
                        self.registry.register_name(&td.name);
                        let constructors =
                            type_registry::process_type_decl(td, &mut self.registry, &mut self.gen)
                                .map_err(|e| spanned(e, span))?;
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
                    self.imported_type_info
                        .insert(effective_type_name.clone(), (path.to_string(), td.visibility.clone()));
                    self.type_provenance.insert(td.name.clone(), path.to_string());
                } else if import_all {
                    if matches!(td.visibility, Visibility::Private) {
                        continue;
                    }
                    if self.registry.lookup_type(&td.name).is_none() {
                        self.registry.register_name(&td.name);
                        let constructors =
                            type_registry::process_type_decl(td, &mut self.registry, &mut self.gen)
                                .map_err(|e| spanned(e, span))?;
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
                                self.imported_fn_types.push((hidden_name.clone(), scheme.clone(), FnOrigin::Regular));
                                self.fn_provenance_map.insert(
                                    hidden_name,
                                    (path.to_string(), cname.clone()),
                                );
                                self.env.bind(cname, scheme);
                            }
                        }
                    }
                } else if self.registry.lookup_type(&td.name).is_none() {
                    self.registry.register_name(&td.name);
                    let constructors =
                        type_registry::process_type_decl(td, &mut self.registry, &mut self.gen)
                            .map_err(|e| spanned(e, span))?;
                    for (cname, scheme) in constructors {
                        self.env.bind(cname, scheme);
                    }
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
                methods,
                span: ext_span,
            } = sdecl
            {
                let mut fns = process_extern_methods(
                    class_name, methods, &mut self.env, &mut self.gen, &self.registry, *ext_span, None,
                    &aliases,
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

        // Collect fn_constraints from imported module for cross-module constraint checking.
        for (name, constraints) in &cached.fn_constraints {
            let effective_name = aliases.get(name).cloned().unwrap_or_else(|| name.clone());
            if requested.contains(name.as_str()) || import_all {
                self.imported_fn_constraints.insert(effective_name, constraints.clone());
            }
        }
        for (name, constraints) in &cached.imported_fn_constraints {
            let effective_name = aliases.get(name).cloned().unwrap_or_else(|| name.clone());
            if requested.contains(name.as_str()) || import_all {
                self.imported_fn_constraints.insert(effective_name, constraints.clone());
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
                let origin = FnOrigin::TraitMethod { trait_name: trait_def.name.clone() };
                for method in &trait_def.methods {
                    let is_visible = import_all || requested.contains(method.name.as_str());
                    let already_imported = self.imported_fn_types.iter().any(|(n, _, _)| n == &method.name);
                    if is_visible && !already_imported {
                        let fn_ty = Type::Fn(method.param_types.clone(), Box::new(method.return_type.clone()));
                        let scheme = TypeScheme {
                            vars: vec![trait_def.type_var_id],
                            ty: fn_ty,
                        };
                        self.env.bind_with_provenance(method.name.clone(), scheme.clone(), path.to_string());
                        self.imported_fn_types.push((method.name.clone(), scheme, origin.clone()));
                        self.fn_provenance_map.insert(method.name.clone(), (path.to_string(), method.name.clone()));
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
                let found_fn = self.imported_fn_types.iter().any(|(n, _, _)| n == &effective_name);
                let found_type = self.imported_type_info.contains_key(&effective_name);
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
                    if let Some((_, scheme, origin)) = self.imported_fn_types
                        .iter()
                        .find(|(n, _, _)| n == &effective_name)
                    {
                        self.reexported_fn_types.push((effective_name.clone(), scheme.clone(), origin.clone()));
                    }
                }
                if found_type {
                    self.reexported_type_names.push(effective_name.clone());
                    let original_vis = self.imported_type_info
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
