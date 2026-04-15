use std::collections::HashMap;

use krypton_parser::ast::{Span, Visibility};

use crate::typed_ast::{self, TraitName};
use crate::types::{BindingSource, ConstructorBindingKind, TypeEnv, TypeScheme};
use crate::unify::{SpannedTypeError, TypeError};

use super::helpers::spanned;

pub(crate) struct ImportContext {
    pub(super) imported_fn_types: Vec<typed_ast::ImportedFn>,
    /// Index: function name → indices into `imported_fn_types` for O(1) name lookups.
    imported_fn_index: HashMap<String, Vec<usize>>,
    pub(super) imported_type_info: HashMap<String, (String, Visibility)>,
    pub(super) imported_fn_qualifiers: HashMap<String, Vec<(typed_ast::ParamQualifier, String)>>,
    /// Prelude functions that were shadowed by explicit imports: (name, source_module)
    pub(super) shadowed_prelude_fns: Vec<(String, String)>,
}

impl ImportContext {
    pub(super) fn new() -> Self {
        ImportContext {
            imported_fn_types: Vec::new(),
            imported_fn_index: HashMap::new(),
            imported_type_info: HashMap::new(),
            imported_fn_qualifiers: HashMap::new(),
            shadowed_prelude_fns: Vec::new(),
        }
    }

    /// Push into imported_fn_types and update the index.
    fn push_fn(&mut self, entry: typed_ast::ImportedFn) {
        let idx = self.imported_fn_types.len();
        self.imported_fn_index
            .entry(entry.name.clone())
            .or_default()
            .push(idx);
        self.imported_fn_types.push(entry);
    }

    fn remove_prelude_entries(&mut self, name: &str) {
        let shadowed: Vec<_> = self
            .get_by_name(name)
            .filter(|f| f.is_prelude)
            .map(|f| (f.name.clone(), f.qualified_name.module_path.clone()))
            .collect();
        if shadowed.is_empty() {
            return;
        }
        self.shadowed_prelude_fns.extend(shadowed);
        self.imported_fn_types
            .retain(|f| f.name != name || !f.is_prelude);
        self.rebuild_index();
    }

    /// Rebuild the entire index (called after retain, which is rare).
    fn rebuild_index(&mut self) {
        self.imported_fn_index.clear();
        for (i, f) in self.imported_fn_types.iter().enumerate() {
            self.imported_fn_index
                .entry(f.name.clone())
                .or_default()
                .push(i);
        }
    }

    /// Get all imported functions with the given name.
    pub(super) fn get_by_name(&self, name: &str) -> impl Iterator<Item = &typed_ast::ImportedFn> {
        let indices = self.imported_fn_index.get(name);
        indices
            .into_iter()
            .flat_map(|idxs| idxs.iter())
            .map(|&i| &self.imported_fn_types[i])
    }

    /// Check if any imported function has the given name.
    pub(super) fn contains_name(&self, name: &str) -> bool {
        self.imported_fn_index.contains_key(name)
    }

    /// Register imported-function metadata and compute its canonical binding source.
    /// Returns an error if the same name is already imported from a different
    /// (non-prelude) module. The user must alias one import to resolve the conflict.
    fn register_import_binding(
        &mut self,
        b: ImportBinding,
    ) -> Result<BindingSource, SpannedTypeError> {
        let ImportBinding {
            name,
            scheme,
            origin,
            source_module,
            original_name,
            is_prelude,
            span,
        } = b;
        let same_symbol_as_prelude = !is_prelude
            && self.get_by_name(&name).any(|existing| {
                existing.is_prelude
                    && existing.qualified_name.module_path == source_module
                    && existing.qualified_name.local_name == original_name
            });

        // Explicit import shadows only actual prelude entries for the same name.
        if !is_prelude {
            self.remove_prelude_entries(&name);
        }

        // Importing the original prelude export directly should keep behaving like
        // prelude-origin shadowing for later local-definition checks.
        let effective_is_prelude = is_prelude || same_symbol_as_prelude;

        // Check same-name imports from different modules for overload compatibility.
        let same_name: Vec<_> = self.get_by_name(&name).collect();
        for existing in same_name {
            if existing.qualified_name.module_path != source_module {
                let existing_params = crate::overload::fn_param_types(&existing.scheme.ty);
                let new_params = crate::overload::fn_param_types(&scheme.ty);

                match (existing_params, new_params) {
                    (Some(ep), Some(np)) => {
                        if ep.len() != np.len() {
                            return Err(spanned(
                                TypeError::ImportOverloadArityMismatch {
                                    name: name.clone(),
                                    arities: vec![
                                        (existing.qualified_name.module_path.clone(), ep.len()),
                                        (source_module.clone(), np.len()),
                                    ],
                                },
                                span,
                            ));
                        }
                        if crate::overload::types_overlap(&ep, &np) {
                            return Err(spanned(
                                TypeError::DuplicateImport {
                                    name: name.clone(),
                                    modules: vec![
                                        existing.qualified_name.module_path.clone(),
                                        source_module.clone(),
                                    ],
                                    signatures: vec![
                                        format!("{}", existing.scheme),
                                        format!("{}", scheme),
                                    ],
                                },
                                span,
                            ));
                        }
                    }
                    _ => {
                        return Err(spanned(
                            TypeError::DuplicateImport {
                                name: name.clone(),
                                modules: vec![
                                    existing.qualified_name.module_path.clone(),
                                    source_module.clone(),
                                ],
                                signatures: vec![
                                    format!("{}", existing.scheme),
                                    format!("{}", scheme),
                                ],
                            },
                            span,
                        ));
                    }
                }
            }
        }

        let binding_source = if let Some(trait_name) = &origin {
            BindingSource::TraitMethod {
                trait_module_path: trait_name.module_path.clone(),
                trait_name: trait_name.local_name.clone(),
                method_name: original_name.clone(),
                is_prelude: effective_is_prelude,
            }
        } else {
            BindingSource::ImportedFunction {
                qualified_name: crate::types::BindingQualifiedName {
                    module_path: source_module.clone(),
                    local_name: original_name.clone(),
                },
                is_prelude: effective_is_prelude,
            }
        };
        self.push_fn(typed_ast::ImportedFn {
            name: name.clone(),
            scheme,
            origin,
            qualified_name: typed_ast::QualifiedName::new(source_module, original_name),
            is_prelude: effective_is_prelude,
        });
        Ok(binding_source)
    }

    /// Atomically bind an imported function: env + fn_types + provenance.
    pub(super) fn bind_import(
        &mut self,
        env: &mut TypeEnv,
        b: ImportBinding,
    ) -> Result<BindingSource, SpannedTypeError> {
        let name = b.name.clone();
        let scheme = b.scheme.clone();
        let is_prelude_import = b.is_prelude;
        let already_bound = env.lookup(&name).is_some();
        let binding_source = self.register_import_binding(b)?;
        if !already_bound {
            env.bind_with_source(name, scheme, binding_source.clone());
        } else {
            let existing_is_prelude = env
                .lookup_entry(&name)
                .map(|e| match &e.source {
                    BindingSource::ImportedFunction { is_prelude, .. } => *is_prelude,
                    BindingSource::TraitMethod { is_prelude, .. } => *is_prelude,
                    _ => false,
                })
                .unwrap_or(false);

            if existing_is_prelude && !is_prelude_import {
                // Full by-name prelude eviction: the prelude is always processed
                // before user imports (prepended via .chain() in process_imports),
                // so at this point every existing overload candidate is
                // prelude-sourced.  Clearing them is correct — subsequent user
                // imports of the same name will build a fresh overload set via
                // the else branch below.
                if let Some(entry) = env.lookup_entry_mut(&name) {
                    entry.scheme = scheme;
                    entry.source = binding_source.clone();
                    entry.overload_candidates = None;
                }
            } else {
                // Only create overload candidates when the same name is imported
                // from genuinely different source modules (validated as non-overlapping
                // by register_import_binding). Trait method re-imports from the same
                // module should not create overloads.
                let distinct_modules: std::collections::HashSet<&str> = self
                    .get_by_name(&name)
                    .map(|f| f.qualified_name.module_path.as_str())
                    .collect();
                if distinct_modules.len() > 1 {
                    if let Some(entry) = env.lookup_entry_mut(&name) {
                        entry.add_overload_candidate(scheme, binding_source.clone());
                    }
                }
            }
        }
        Ok(binding_source)
    }

    /// Bind a hidden (qualified) function: fn_types + provenance, no env bind.
    pub(super) fn bind_hidden_fn(
        &mut self,
        name: String,
        scheme: TypeScheme,
        origin: Option<TraitName>,
        provenance: (String, String),
        is_prelude: bool,
    ) {
        self.push_fn(typed_ast::ImportedFn {
            name,
            scheme,
            origin,
            qualified_name: typed_ast::QualifiedName::new(provenance.0, provenance.1),
            is_prelude,
        });
    }

    // Imported constructor binding takes one arg per distinct surface attribute
    // (binding name, scheme, defining type info, kind, prelude flag); a wrapping
    // struct here would just be a namespace shim for one call site.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn bind_imported_constructor(
        &mut self,
        env: &mut TypeEnv,
        binding_name: String,
        scheme: TypeScheme,
        type_module_path: String,
        type_name: String,
        constructor_name: String,
        kind: ConstructorBindingKind,
        is_prelude: bool,
    ) {
        self.push_fn(typed_ast::ImportedFn {
            name: binding_name.clone(),
            scheme: scheme.clone(),
            origin: None,
            qualified_name: typed_ast::QualifiedName::new(
                type_module_path.clone(),
                constructor_name.clone(),
            ),
            is_prelude,
        });
        env.bind_constructor(
            binding_name,
            scheme,
            type_module_path,
            type_name,
            constructor_name,
            kind,
        );
    }

    pub(super) fn bind_hidden_constructor(
        &mut self,
        name: String,
        scheme: TypeScheme,
        type_module_path: String,
        constructor_name: String,
        is_prelude: bool,
    ) {
        self.push_fn(typed_ast::ImportedFn {
            name,
            scheme,
            origin: None,
            qualified_name: typed_ast::QualifiedName::new(type_module_path, constructor_name),
            is_prelude,
        });
    }

    /// Bind type info for an imported type.
    pub(super) fn bind_type_info(
        &mut self,
        name: String,
        canonical_name: Option<String>,
        source: String,
        vis: Visibility,
    ) {
        self.imported_type_info.insert(name, (source.clone(), vis));
        if let Some(canonical_name) = canonical_name {
            self.imported_type_info
                .entry(canonical_name)
                .or_insert((source, vis));
        }
    }

    pub(super) fn remove_prelude_fn(&mut self, name: &str) {
        let shadowed: Vec<_> = self
            .get_by_name(name)
            .filter(|f| f.is_prelude)
            .map(|f| (f.name.clone(), f.qualified_name.module_path.clone()))
            .collect();
        if shadowed.is_empty() {
            return;
        }
        self.shadowed_prelude_fns.extend(shadowed);
        self.imported_fn_types
            .retain(|f| f.name != name || !f.is_prelude);
        self.rebuild_index();
    }
}

/// All inputs needed to register an imported function binding.
/// Bundled to keep `register_import_binding`/`bind_import` arity manageable —
/// every field is a distinct lexical input from the surface import statement.
pub(crate) struct ImportBinding {
    pub(crate) name: String,
    pub(crate) scheme: TypeScheme,
    pub(crate) origin: Option<TraitName>,
    pub(crate) source_module: String,
    pub(crate) original_name: String,
    pub(crate) is_prelude: bool,
    pub(crate) span: Span,
}
