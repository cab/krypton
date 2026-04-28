// Construction and pre-lowering registration: building a `LowerCtx` and
// populating its symbol tables (struct layouts, sum-variant tags, fn-id
// allocations) before any expression lowering runs.

use rustc_hash::{FxHashMap, FxHashSet};

use krypton_typechecker::overload::types_overlap;
use krypton_typechecker::typed_ast::{
    self as typed_ast, AutoCloseInfo, ExportedTypeKind, FnTypeEntry, QualifiedName, TypedModule,
};
use krypton_typechecker::types::{Type, TypeScheme, TypeVarGen, TypeVarId};

use super::ctx::{
    InstanceSourceInfo, LocalFnAlloc, LowerCtx, ParamInstanceInfo, TraitConstraintList,
    TraitMethodConstraintInfo, TraitMethodTypeInfo,
};
use super::type_expr::{build_type_param_map, resolve_type_expr_simple};
use krypton_typechecker::typed_ast::TraitName;

use super::LowerError;

impl<'a> LowerCtx<'a> {
    /// Construct a `LowerCtx` from the artifacts produced by the
    /// pre-context phases. Zero-initializes all per-function scratch state
    /// (`var_scope`, `dict_params`, caches, `lifted_fns`, …) and seeds the
    /// `instance_exact_index` from `all_instances` so exact-match dict
    /// resolution is `O(1)` from the first lookup.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        link_view: &'a krypton_typechecker::link_context::ModuleLinkView<'a>,
        module_path: String,
        auto_close: AutoCloseInfo,
        fn_constraints: FxHashMap<QualifiedName, TraitConstraintList>,
        fn_schemes: FxHashMap<QualifiedName, TypeScheme>,
        param_instances: Vec<ParamInstanceInfo>,
        all_instances: Vec<InstanceSourceInfo>,
        trait_method_types: FxHashMap<TraitName, TraitMethodTypeInfo>,
        trait_method_constraints: FxHashMap<TraitName, TraitMethodConstraintInfo>,
    ) -> Self {
        let mut instance_exact_index: FxHashMap<(String, String), usize> = FxHashMap::default();
        for (i, info) in all_instances.iter().enumerate() {
            let key = (
                info.trait_name.local_name.clone(),
                info.target_type_name.clone(),
            );
            instance_exact_index.entry(key).or_insert(i);
        }
        LowerCtx {
            link_view,
            next_var: 0,
            next_fn: 0,
            type_var_gen: TypeVarGen::new(),
            var_scope: FxHashMap::default(),
            fn_ids: FxHashMap::default(),
            callable_ids: FxHashMap::default(),
            struct_fields: FxHashMap::default(),
            struct_type_params: FxHashMap::default(),
            sum_variants: FxHashMap::default(),
            private_type_params: FxHashMap::default(),
            fn_constraints,
            dict_params: FxHashMap::default(),
            superclass_projection_cache: FxHashMap::default(),
            fn_schemes,
            module_path,
            param_instances,
            trait_method_types,
            trait_method_constraints,
            dict_depth: 0,
            lifted_fns: vec![],
            var_types: FxHashMap::default(),
            recur_join: None,
            early_return_join: None,
            auto_close,
            scope_track_stack: Vec::new(),
            fn_block_scoped_closes: Vec::new(),
            fn_exit_closes: FxHashMap::default(),
            all_instances,
            instance_exact_index,
        }
    }

    /// Populate `struct_fields` and `struct_type_params` for every struct
    /// visible to this module. Both public and private locally-declared
    /// types flow through `exported_type_infos` with the same registry-
    /// allocated `TypeVarId`s, so downstream lookups (struct construction,
    /// field access, pattern matching) all see the same ids regardless of
    /// visibility. The trailing `struct_decls` loop is a defensive fallback
    /// for any decl that somehow isn't in `exported_type_infos`; populates
    /// `private_type_params` only if it fires.
    pub(super) fn register_struct_layouts(&mut self, typed: &TypedModule) {
        let mut sorted_type_infos: Vec<_> = typed.exported_type_infos.iter().collect();
        sorted_type_infos.sort_by_key(|(name, _)| name.as_str());
        for (name, info) in &sorted_type_infos {
            let type_ref = typed_ast::ResolvedTypeRef {
                qualified_name: QualifiedName::new(info.source_module.clone(), (*name).clone()),
            };
            if let ExportedTypeKind::Record { fields } = &info.kind {
                self.struct_fields.insert(type_ref.clone(), fields.clone());
                self.struct_type_params
                    .insert(type_ref, info.type_param_vars.clone());
            }
        }
        for decl in &typed.struct_decls {
            let type_ref = typed_ast::ResolvedTypeRef {
                qualified_name: decl.qualified_name.clone(),
            };
            if !self.struct_fields.contains_key(&type_ref) {
                let type_param_map =
                    build_type_param_map(&decl.type_params, &mut self.type_var_gen);
                let ordered_params: Vec<TypeVarId> = decl
                    .type_params
                    .iter()
                    .map(|name| type_param_map[name])
                    .collect();
                self.private_type_params
                    .insert(decl.name.clone(), ordered_params.clone());
                let fields: Vec<(String, Type)> = decl
                    .fields
                    .iter()
                    .map(|(fname, texpr)| {
                        let ty = resolve_type_expr_simple(texpr, &type_param_map);
                        (fname.clone(), ty)
                    })
                    .collect();
                self.struct_fields.insert(type_ref.clone(), fields);
                self.struct_type_params.insert(type_ref, ordered_params);
            }
        }
    }

    /// Populate `sum_variants` for every sum type visible to this module.
    /// Public and private locally-declared sums both flow through
    /// `exported_type_infos`; the trailing `sum_decls` loop is a defensive
    /// fallback that populates `private_type_params` only when a decl
    /// somehow isn't in `exported_type_infos`.
    pub(super) fn register_sum_variants(&mut self, typed: &TypedModule) {
        let mut sorted_type_infos: Vec<_> = typed.exported_type_infos.iter().collect();
        sorted_type_infos.sort_by_key(|(name, _)| name.as_str());
        for (name, info) in &sorted_type_infos {
            if let ExportedTypeKind::Sum { variants } = &info.kind {
                let type_ref = typed_ast::ResolvedTypeRef {
                    qualified_name: QualifiedName::new(info.source_module.clone(), (*name).clone()),
                };
                for (tag, variant) in variants.iter().enumerate() {
                    self.sum_variants.insert(
                        typed_ast::ResolvedVariantRef {
                            type_ref: type_ref.clone(),
                            variant_name: variant.name.clone(),
                        },
                        (tag as u32, variant.fields.clone()),
                    );
                }
            }
        }
        for decl in &typed.sum_decls {
            let already = decl.variants.iter().any(|v| {
                self.sum_variants
                    .contains_key(&typed_ast::ResolvedVariantRef {
                        type_ref: typed_ast::ResolvedTypeRef {
                            qualified_name: decl.qualified_name.clone(),
                        },
                        variant_name: v.name.clone(),
                    })
            });
            if !already {
                let type_param_map =
                    build_type_param_map(&decl.type_params, &mut self.type_var_gen);
                let ordered_params: Vec<TypeVarId> = decl
                    .type_params
                    .iter()
                    .map(|name| type_param_map[name])
                    .collect();
                self.private_type_params
                    .insert(decl.name.clone(), ordered_params);
                for (tag, variant) in decl.variants.iter().enumerate() {
                    let fields: Vec<Type> = variant
                        .fields
                        .iter()
                        .map(|texpr| resolve_type_expr_simple(texpr, &type_param_map))
                        .collect();
                    self.sum_variants.insert(
                        typed_ast::ResolvedVariantRef {
                            type_ref: typed_ast::ResolvedTypeRef {
                                qualified_name: decl.qualified_name.clone(),
                            },
                            variant_name: variant.name.clone(),
                        },
                        (tag as u32, fields),
                    );
                }
            }
        }
    }

    /// Allocate `FnId`s for every function the module can call: local
    /// decls, local extern fns, imported fns, and compiler intrinsics.
    ///
    /// Overloads share a bare name and qualified_name, so `fn_ids` and
    /// `callable_ids` are vecs of (sig_key, FnId) with one entry per
    /// overload sibling. The returned `Vec<LocalFnAlloc>` aligns 1:1 with
    /// `typed.functions` so `lower_function_bodies` knows which FnId and
    /// resolved param/return types belong to which decl — critical when
    /// `typed.functions` contains overload siblings.
    pub(super) fn allocate_fn_ids(&mut self, typed: &TypedModule) -> Result<Vec<LocalFnAlloc>, LowerError> {
        // Build per-name FIFO queue of local-function fn_types entries. Each
        // `typed.functions[i]` pulls its corresponding entry from the queue
        // for its name. Module_driver appends fn_decls to fn_types in order
        // (module_driver.rs:475-488), so the i-th decl with name N pairs with
        // the i-th local entry with name N.
        let local_decl_names: FxHashSet<&str> =
            typed.functions.iter().map(|d| d.name.as_str()).collect();
        let mut local_decl_entries: FxHashMap<String, std::collections::VecDeque<&FnTypeEntry>> =
            FxHashMap::default();
        for entry in &typed.fn_types {
            if entry.qualified_name.module_path == typed.module_path
                && local_decl_names.contains(entry.name.as_str())
            {
                local_decl_entries
                    .entry(entry.name.clone())
                    .or_default()
                    .push_back(entry);
            }
        }

        let mut local_fn_allocs: Vec<LocalFnAlloc> = Vec::with_capacity(typed.functions.len());
        for decl in &typed.functions {
            let entry = local_decl_entries
                .get_mut(&decl.name)
                .and_then(|q| q.pop_front())
                .ok_or_else(|| {
                    LowerError::InternalError(format!(
                        "no FnTypeEntry for local decl `{}` (overload queue empty)",
                        decl.name
                    ))
                })?;
            let (param_types, return_type) = match &entry.scheme.ty {
                Type::Fn(params, ret) => (
                    params.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>(),
                    (**ret).clone(),
                ),
                other => (Vec::new(), other.clone()),
            };
            let sig_key = param_types.clone();
            let fn_id = self.fresh_fn();
            self.insert_fn_id(
                decl.name.clone(),
                QualifiedName::new(typed.module_path.clone(), decl.name.clone()),
                sig_key,
                fn_id,
            );
            local_fn_allocs.push(LocalFnAlloc {
                fn_id,
                param_types,
                return_type,
            });
        }

        // Extern functions (local). Externs cannot overload (enforced by
        // check_duplicate_function_names), so they are always singletons.
        for ext in &typed.extern_fns {
            if !self.fn_ids.contains_key(&ext.name) {
                let fn_id = self.fresh_fn();
                self.insert_fn_id(
                    ext.name.clone(),
                    QualifiedName::new(ext.declaring_module_path.clone(), ext.name.clone()),
                    Vec::new(),
                    fn_id,
                );
            }
        }

        // Imported functions (from fn_types entries with cross-module
        // provenance). Each entry gets its own FnId so overload siblings
        // resolve independently — we no longer dedup by bare name.
        for entry in &typed.fn_types {
            if !matches!(entry.scheme.ty, Type::Fn(..)) {
                continue;
            }
            if entry.qualified_name.module_path == typed.module_path {
                continue;
            }
            let sig_key: Vec<Type> = match &entry.scheme.ty {
                Type::Fn(params, _) => params.iter().map(|(_, t)| t.clone()).collect(),
                _ => Vec::new(),
            };
            let already = self
                .callable_ids
                .get(&entry.qualified_name)
                .map(|cands| cands.iter().any(|(ps, _)| types_overlap(ps, &sig_key)))
                .unwrap_or(false);
            if already {
                continue;
            }
            let fn_id = self.fresh_fn();
            self.insert_fn_id(
                entry.name.clone(),
                entry.qualified_name.clone(),
                sig_key,
                fn_id,
            );
        }

        // Register compiler intrinsics (always singleton).
        for &name in crate::COMPILER_INTRINSICS {
            if !self.fn_ids.contains_key(name) {
                let fn_id = self.fresh_fn();
                self.insert_fn_id(
                    name.to_string(),
                    QualifiedName::new("__builtin__".to_string(), name.to_string()),
                    Vec::new(),
                    fn_id,
                );
            }
        }

        Ok(local_fn_allocs)
    }
}
