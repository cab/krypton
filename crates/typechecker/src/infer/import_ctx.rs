use rustc_hash::FxHashMap;

use krypton_parser::ast::{Decl, Module, Span, Visibility};

use crate::overload::{fn_param_types, types_overlap};
use crate::typed_ast::{self, TraitName};
use crate::types::{BindingSource, ConstructorBindingKind, TypeEnv, TypeScheme};
use crate::unify::{SpannedTypeError, TypeError};

use super::helpers::spanned;
use super::state::ModuleInferenceState;

pub(crate) struct ImportContext {
    pub(super) imported_fn_types: Vec<typed_ast::ImportedFn>,
    /// Index: function name → indices into `imported_fn_types` for O(1) name lookups.
    imported_fn_index: FxHashMap<String, Vec<usize>>,
    pub(super) imported_type_info: FxHashMap<String, (String, Visibility)>,
    pub(super) imported_fn_qualifiers: FxHashMap<String, Vec<(typed_ast::ParamQualifier, String)>>,
    /// Prelude functions that were shadowed by explicit imports: (name, source_module)
    pub(super) shadowed_prelude_fns: Vec<(String, String)>,
}

impl ImportContext {
    pub(super) fn new() -> Self {
        ImportContext {
            imported_fn_types: Vec::new(),
            imported_fn_index: FxHashMap::default(),
            imported_type_info: FxHashMap::default(),
            imported_fn_qualifiers: FxHashMap::default(),
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
                // Create an overload candidate whenever the same local name
                // has more than one import entry with a genuinely distinct
                // signature. Covers both cross-module and same-source-module
                // overloads. The distinctness guard prevents a false overload
                // when the same function reaches the environment via multiple
                // import paths (e.g., repeated imports or a re-export that
                // shadows an existing binding).
                let new_params = crate::overload::fn_param_types(&scheme.ty);
                let is_duplicate = env
                    .lookup_entry(&name)
                    .map(|entry| {
                        let primary_match =
                            binding_sources_share_identity(&entry.source, &binding_source)
                                && crate::overload::fn_param_types(&entry.scheme.ty) == new_params;
                        let candidate_match = entry
                            .overload_candidates
                            .as_ref()
                            .map(|cs| {
                                cs.iter().any(|c| {
                                    binding_sources_share_identity(&c.source, &binding_source)
                                        && crate::overload::fn_param_types(&c.scheme.ty)
                                            == new_params
                                })
                            })
                            .unwrap_or(false);
                        primary_match || candidate_match
                    })
                    .unwrap_or(false);
                if !is_duplicate && self.get_by_name(&name).count() > 1 {
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

/// Whether two `BindingSource` values refer to the same underlying symbol
/// (same trait method, same imported function by qualified name, etc.).
/// Used to detect duplicate imports that reach the environment through
/// multiple paths, so a duplicate import does not fabricate a phantom
/// overload candidate.
fn binding_sources_share_identity(a: &BindingSource, b: &BindingSource) -> bool {
    match (a, b) {
        (
            BindingSource::ImportedFunction {
                qualified_name: qa, ..
            },
            BindingSource::ImportedFunction {
                qualified_name: qb, ..
            },
        ) => qa == qb,
        (
            BindingSource::TraitMethod {
                trait_module_path: tma,
                trait_name: ta,
                method_name: ma,
                ..
            },
            BindingSource::TraitMethod {
                trait_module_path: tmb,
                trait_name: tb,
                method_name: mb,
                ..
            },
        ) => tma == tmb && ta == tb && ma == mb,
        (
            BindingSource::Constructor {
                type_qualified_name: qa,
                constructor_name: ca,
                ..
            },
            BindingSource::Constructor {
                type_qualified_name: qb,
                constructor_name: cb,
                ..
            },
        ) => qa == qb && ca == cb,
        (
            BindingSource::TopLevelLocalFunction { qualified_name: qa },
            BindingSource::TopLevelLocalFunction { qualified_name: qb },
        ) => qa == qb,
        (
            BindingSource::IntrinsicFunction { name: a },
            BindingSource::IntrinsicFunction { name: b },
        ) => a == b,
        _ => false,
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

impl ModuleInferenceState {
    pub(super) fn check_explicit_import_shadows(
        &self,
        module: &Module,
    ) -> Result<(), SpannedTypeError> {
        for decl in &module.decls {
            match decl {
                Decl::DefFn(f) => {
                    let non_prelude_imports: Vec<_> = self
                        .imports
                        .get_by_name(&f.name)
                        .filter(|imp| !imp.is_prelude)
                        .collect();
                    if non_prelude_imports.is_empty() {
                        continue;
                    }
                    // Try to resolve local param types for overload checking
                    let local_params =
                        match super::traits_register::resolve_fn_param_types_for_overlap(
                            f,
                            &self.registry,
                        ) {
                            super::traits_register::OverlapResolve::Ok(params) => params,
                            super::traits_register::OverlapResolve::MissingAnnotation
                            | super::traits_register::OverlapResolve::Unresolvable(_) => {
                                // Can't resolve — keep current error behavior
                                let imp = &non_prelude_imports[0];
                                return Err(spanned(
                                    TypeError::DefinitionConflictsWithImport {
                                        def_name: f.name.clone(),
                                        source_module: imp.qualified_name.module_path.clone(),
                                    },
                                    f.span,
                                ));
                            }
                        };
                    for imp in &non_prelude_imports {
                        let imp_params = match fn_param_types(&imp.scheme.ty) {
                            Some(params) => params,
                            None => {
                                // Import is not a function — conflict
                                return Err(spanned(
                                    TypeError::DefinitionConflictsWithImport {
                                        def_name: f.name.clone(),
                                        source_module: imp.qualified_name.module_path.clone(),
                                    },
                                    f.span,
                                ));
                            }
                        };
                        if imp_params.len() != local_params.len() {
                            return Err(spanned(
                                TypeError::ImportOverloadArityMismatch {
                                    name: f.name.clone(),
                                    arities: vec![
                                        ("(local)".to_string(), local_params.len()),
                                        (imp.qualified_name.module_path.clone(), imp_params.len()),
                                    ],
                                },
                                f.span,
                            ));
                        }
                        if types_overlap(&local_params, &imp_params) {
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: f.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                f.span,
                            ));
                        }
                    }
                }
                Decl::Extern { methods, .. } => {
                    for m in methods {
                        if let Some(imp) = self
                            .imports
                            .get_by_name(&m.name)
                            .find(|imp| !imp.is_prelude)
                        {
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: m.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                m.span,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}
