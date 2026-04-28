// Module-pipeline free functions: orchestrate the per-module lowering and
// produce values that feed `LowerCtx::new`. Co-located here so `lower.rs`
// can stay focused on the `LowerCtx` impl block.

use rustc_hash::{FxHashMap, FxHashSet};

use krypton_typechecker::link_context::LinkContext;
use krypton_typechecker::overload::types_overlap;
use krypton_typechecker::typed_ast::{
    self, QualifiedName, TypedModule,
};
use krypton_typechecker::types::{Type, TypeScheme, TypeVarId};

use super::ctx::{
    InstanceSourceInfo, InstanceSubDictList, LocalFnAlloc, LowerCtx, ParamInstanceInfo,
    TraitConstraintList, TraitMethodConstraintInfo, TraitMethodTypeInfo,
};
use krypton_typechecker::typed_ast::TraitName;

use super::type_expr::seed_type_var_gen_past_typed;
use super::util::{collect_tuple_arities_from_fn, collect_tuple_arities_from_type};
use super::LowerError;
use crate::Type as IrType;
use crate::{
    CanonicalRef, ExternCallKind, ExternFnDef, ExternTarget, ExternTraitBridge, ExternTraitDef,
    ExternTraitMethodDef, ExternTypeDef, FnDef, FnId, FnIdentity, ImportedFnDef, InstanceDef,
    LocalSymbolKey, Module, ModulePath, StructDef, SumTypeDef, TraitDef, TraitMethodDef,
    VariantDef,
};

// ---------------------------------------------------------------------------
// Helpers used by build_param_instances / instance source resolution
// ---------------------------------------------------------------------------

/// True if `t` mentions any `Type::Var` anywhere. Used by
/// `build_param_instances` and `LowerCtx::has_param_slots` to decide whether
/// an instance's target slots are parameterized — concrete-target instances
/// must stay out of `param_instances` so dict resolution routes them through
/// the singleton `GetDict` strategy.
pub(super) fn ty_has_vars(t: &Type) -> bool {
    match t {
        Type::Var(_) => true,
        Type::Named(_, args) => args.iter().any(ty_has_vars),
        Type::App(ctor, args) => ty_has_vars(ctor) || args.iter().any(ty_has_vars),
        Type::Fn(params, ret) => params.iter().any(|(_, p)| ty_has_vars(p)) || ty_has_vars(ret),
        Type::Tuple(elems) => elems.iter().any(ty_has_vars),
        Type::Own(inner) => ty_has_vars(inner),
        _ => false,
    }
}

/// True if a parameterized instance carries any dict slot — either an
/// impl-head constraint or an inherited superclass slot from the trait. The
/// link view is needed because superclass info lives at the trait
/// declaration, not on the instance.
pub(super) fn has_param_slots(
    link_view: &krypton_typechecker::link_context::ModuleLinkView,
    trait_name: &TraitName,
    target_types: &[Type],
    constraints: &[typed_ast::ResolvedConstraint],
) -> bool {
    if !target_types.iter().any(ty_has_vars) {
        return false;
    }
    !constraints.is_empty()
        || link_view
            .trait_direct_superclasses(trait_name)
            .map(|v| !v.is_empty())
            .unwrap_or(false)
}

/// Build a `ParamInstanceInfo` from a parameterized instance, copying the
/// pre-computed sub-dict layout off the instance. Keeps the
/// `ParamInstance.constraints` order in sync with
/// `InstanceDef.sub_dict_requirements` (superclass slots first, then
/// impl-head constraints) by construction. See
/// `module_interface::compute_instance_sub_dict_requirements` for the
/// authoritative layout contract.
pub(super) fn build_param_info(
    trait_name: &TraitName,
    target_types: &[Type],
    sub_dict_requirements: &[(TraitName, Vec<Type>)],
    source_module: String,
    target_type_name: String,
) -> ParamInstanceInfo {
    let constraints: Vec<(TraitName, Vec<IrType>)> = sub_dict_requirements
        .iter()
        .map(|(tn, tys)| (tn.clone(), tys.iter().cloned().map(IrType::from).collect()))
        .collect();
    ParamInstanceInfo {
        trait_name: trait_name.clone(),
        target_types: target_types.to_vec(),
        constraints,
        source_module,
        target_type_name,
    }
}


/// Combine constraint sources into the canonical fn-name → trait-dict map:
/// (a) `fn_types` schemes (embedded during inference),
/// (b) `extern_fns` constraints (so dict-passing works for extern calls),
/// (c) per-method instance constraints (impl-head plus method-level), keyed
/// by the shared `mangled_method_name` so `lower_fn` can prepend dict params.
pub(super) fn build_fn_constraints(typed: &TypedModule) -> FxHashMap<QualifiedName, TraitConstraintList> {
    let mut fn_constraints: FxHashMap<QualifiedName, TraitConstraintList> = FxHashMap::default();
    for entry in &typed.fn_types {
        if !entry.scheme.constraints.is_empty() {
            fn_constraints.insert(
                entry.qualified_name.clone(),
                entry.scheme.constraints.clone(),
            );
        }
    }
    for ext in &typed.extern_fns {
        if !ext.constraints.is_empty() {
            fn_constraints.insert(
                QualifiedName::new(typed.module_path.clone(), ext.name.clone()),
                ext.constraints.clone(),
            );
        }
    }
    for inst in &typed.instance_defs {
        let impl_constraint_pairs: TraitConstraintList = inst
            .constraints
            .iter()
            .filter_map(|c| {
                let tvs: Option<Vec<TypeVarId>> = c
                    .type_vars
                    .iter()
                    .map(|name| inst.type_var_ids.get(name).copied())
                    .collect();
                tvs.map(|tvs| (c.trait_name.clone(), tvs))
            })
            .collect();
        for m in &inst.methods {
            let mut all_constraints = impl_constraint_pairs.clone();
            all_constraints.extend(m.constraint_pairs.iter().cloned());
            if all_constraints.is_empty() {
                continue;
            }
            let mangled = typed_ast::mangled_method_name(
                &inst.trait_name.local_name,
                &inst.target_type_name,
                &m.name,
            );
            fn_constraints
                .entry(QualifiedName::new(typed.module_path.clone(), mangled))
                .or_insert_with(|| all_constraints);
        }
    }
    fn_constraints
}

/// Build the qualified-name → `TypeScheme` map used by `resolve_call_dicts`
/// to match type arguments at call sites. Pulls schemes from `fn_types` and
/// synthesizes one for each constrained extern fn (which has no entry in
/// `fn_types`).
pub(super) fn build_fn_schemes(typed: &TypedModule) -> FxHashMap<QualifiedName, TypeScheme> {
    let mut fn_schemes: FxHashMap<QualifiedName, TypeScheme> = FxHashMap::default();
    for entry in &typed.fn_types {
        fn_schemes.insert(entry.qualified_name.clone(), entry.scheme.clone());
    }
    for ext in &typed.extern_fns {
        if !ext.constraints.is_empty() {
            let vars: Vec<TypeVarId> = ext
                .constraints
                .iter()
                .flat_map(|(_, tvs)| tvs.iter().copied())
                .collect();
            let fn_ty = krypton_typechecker::types::Type::fn_consuming(
                ext.param_types.clone(),
                ext.return_type.clone(),
            );
            fn_schemes.insert(
                QualifiedName::new(typed.module_path.clone(), ext.name.clone()),
                TypeScheme {
                    vars,
                    constraints: ext.constraints.clone(),
                    ty: fn_ty,
                    var_names: FxHashMap::default(),
                },
            );
        }
    }
    fn_schemes
}

/// Collect all parameterized trait instances (local + imported) whose target
/// slots contain at least one `Type::Var` AND whose trait carries dict
/// slots. Concrete-target instances route through Strategy 3 (singleton
/// `GetDict`) at resolve time, so they must not appear here.
pub(super) fn build_param_instances(
    typed: &TypedModule,
    link_view: &krypton_typechecker::link_context::ModuleLinkView,
) -> Vec<ParamInstanceInfo> {
    let local_param = typed
        .instance_defs
        .iter()
        .filter(|inst| {
            has_param_slots(
                link_view,
                &inst.trait_name,
                &inst.target_types,
                &inst.constraints,
            )
        })
        .map(|inst| {
            build_param_info(
                &inst.trait_name,
                &inst.target_types,
                &inst.sub_dict_requirements,
                typed.module_path.clone(),
                inst.target_type_name.clone(),
            )
        });
    let imported_param = link_view
        .all_instances()
        .into_iter()
        .filter(|(path, _)| path.as_str() != typed.module_path)
        .filter(|(_, inst)| {
            has_param_slots(
                link_view,
                &inst.trait_name,
                &inst.target_types,
                &inst.constraints,
            )
        })
        .map(|(path, inst)| {
            build_param_info(
                &inst.trait_name,
                &inst.target_types,
                &inst.sub_dict_requirements,
                path.as_str().to_string(),
                inst.target_type_name.clone(),
            )
        });
    local_param.chain(imported_param).collect()
}

/// Collect every reachable instance (local + imported, parameterized or
/// concrete) so dict resolution can build `CanonicalRef`s during `GetDict` /
/// `MakeDict` emission.
pub(super) fn build_all_instances(
    typed: &TypedModule,
    link_view: &krypton_typechecker::link_context::ModuleLinkView,
) -> Vec<InstanceSourceInfo> {
    let mut infos = Vec::new();
    for inst in &typed.instance_defs {
        infos.push(InstanceSourceInfo {
            trait_name: inst.trait_name.clone(),
            target_types: inst.target_types.clone(),
            target_type_name: inst.target_type_name.clone(),
            source_module: typed.module_path.clone(),
        });
    }
    for (path, inst) in link_view.all_instances() {
        if path.as_str() != typed.module_path {
            infos.push(InstanceSourceInfo {
                trait_name: inst.trait_name.clone(),
                target_types: inst.target_types.clone(),
                target_type_name: inst.target_type_name.clone(),
                source_module: path.as_str().to_string(),
            });
        }
    }
    infos
}

/// Build the trait-name → method-signature map used by trait-method
/// dispatch. ICE if a trait is missing its `type_var_ids` — every trait
/// must carry at least one type parameter, populated during trait
/// elaboration.
pub(super) fn build_trait_method_types(typed: &TypedModule) -> FxHashMap<TraitName, TraitMethodTypeInfo> {
    typed
        .trait_defs
        .iter()
        .map(|t| {
            assert!(
                !t.type_var_ids.is_empty(),
                "ICE: trait {} has empty type_var_ids — every trait must carry \
                 at least one type parameter, populated during trait elaboration",
                t.trait_id.local_name
            );
            (
                t.trait_id.clone(),
                (t.type_var_ids.clone(), t.method_tc_types.clone()),
            )
        })
        .collect()
}

/// Build the trait-name → method-name → method-level where-constraint map.
/// Traits whose methods have no where-constraints are omitted entirely.
pub(super) fn build_trait_method_constraints(
    typed: &TypedModule,
) -> FxHashMap<TraitName, TraitMethodConstraintInfo> {
    typed
        .trait_defs
        .iter()
        .filter(|t| !t.method_constraints.is_empty())
        .map(|t| (t.trait_id.clone(), t.method_constraints.clone()))
        .collect()
}

// ---------------------------------------------------------------------------
// Output phases (free fns reading &LowerCtx, producing IR collections)
// ---------------------------------------------------------------------------

/// Lower local struct decls to IR `StructDef`s. Imported structs are
/// excluded (they show up in the importing module's `imported_structs`).
pub(super) fn lower_struct_defs(typed: &TypedModule, ctx: &LowerCtx) -> Vec<StructDef> {
    typed
        .struct_decls
        .iter()
        .filter(|decl| decl.qualified_name.module_path == typed.module_path)
        .map(|decl| {
            // Public and private locally-declared structs both flow through
            // `exported_type_infos` with registry-allocated ids; the
            // `private_type_params` fallback below only fires when the
            // defensive second loop in `register_struct_layouts` populated
            // it for a decl that wasn't in `exported_type_infos`.
            let info = typed.exported_type_infos.get(&decl.name);
            let type_ref = typed_ast::ResolvedTypeRef {
                qualified_name: decl.qualified_name.clone(),
            };
            let type_params = if let Some(info) = info {
                info.type_param_vars.clone()
            } else {
                ctx.private_type_params
                    .get(&decl.name)
                    .cloned()
                    .unwrap_or_default()
            };
            let fields = ctx
                .struct_fields
                .get(&type_ref)
                .cloned()
                .unwrap_or_default();
            StructDef {
                name: decl.name.clone(),
                type_params,
                fields: fields.into_iter().map(|(n, t)| (n, t.into())).collect(),
            }
        })
        .collect()
}

/// Lower local sum-type decls to IR `SumTypeDef`s. Imported sums are
/// excluded.
pub(super) fn lower_sum_type_defs(typed: &TypedModule, ctx: &LowerCtx) -> Vec<SumTypeDef> {
    typed
        .sum_decls
        .iter()
        .filter(|decl| decl.qualified_name.module_path == typed.module_path)
        .map(|decl| {
            // Public and private locally-declared sums both flow through
            // `exported_type_infos`; the `private_type_params` fallback only
            // fires for the defensive second-loop case in
            // `register_sum_variants`.
            let type_params = if let Some(info) = typed.exported_type_infos.get(&decl.name) {
                info.type_param_vars.clone()
            } else {
                ctx.private_type_params
                    .get(&decl.name)
                    .cloned()
                    .unwrap_or_default()
            };
            let variants = decl
                .variants
                .iter()
                .enumerate()
                .map(|(tag, v)| {
                    let variant_ref = typed_ast::ResolvedVariantRef {
                        type_ref: typed_ast::ResolvedTypeRef {
                            qualified_name: decl.qualified_name.clone(),
                        },
                        variant_name: v.name.clone(),
                    };
                    let fields = ctx
                        .sum_variants
                        .get(&variant_ref)
                        .map(|(_, f)| f.clone())
                        .unwrap_or_default();
                    VariantDef {
                        name: v.name.clone(),
                        tag: tag as u32,
                        fields: fields.into_iter().map(|t| t.into()).collect(),
                    }
                })
                .collect();
            SumTypeDef {
                name: decl.name.clone(),
                type_params,
                variants,
            }
        })
        .collect()
}

/// Lower every local `TypedFnDecl` body to an IR `FnDef`, threading the
/// per-decl allocation info from `allocate_fn_ids`. The caller is
/// responsible for appending `ctx.lifted_fns` afterwards (lifted lambdas
/// accumulate as a side effect of `lower_fn`).
pub(super) fn lower_function_bodies(
    typed: &TypedModule,
    ctx: &mut LowerCtx,
    allocs: Vec<LocalFnAlloc>,
) -> Result<Vec<FnDef>, LowerError> {
    let mut functions = Vec::with_capacity(allocs.len());
    for (decl, alloc) in typed.functions.iter().zip(allocs.into_iter()) {
        let LocalFnAlloc {
            fn_id,
            param_types,
            return_type,
        } = alloc;
        let exported_symbol = decl.exported_symbol.clone();
        let fn_def = ctx.lower_fn(decl, fn_id, param_types, return_type, exported_symbol)?;
        functions.push(fn_def);
    }
    Ok(functions)
}

/// Build `ImportedFnDef`s from `fn_types` entries with cross-module
/// provenance. Trait methods (`origin.is_some()`) are dispatched via
/// `TraitCall`, never via `Call`, so they are excluded. Deduplicated by
/// (name, source_module, sig_key); overload siblings share the first two
/// components, so the sig_key distinguishes them. Each entry's
/// `exported_symbol` is read from the source module's `ExportedFnSummary`
/// whose scheme matches this overload, falling back to the bare local name
/// when the interface doesn't publish it.
pub(super) fn build_imported_fns(
    typed: &TypedModule,
    ctx: &LowerCtx,
    link_view: &krypton_typechecker::link_context::ModuleLinkView,
) -> Vec<ImportedFnDef> {
    let mut imported_fns = vec![];
    let mut imported_fn_seen: FxHashSet<(String, String, Vec<Type>)> = FxHashSet::default();
    for entry in &typed.fn_types {
        if entry.origin.is_some() {
            continue;
        }
        if !matches!(entry.scheme.ty, Type::Fn(..)) {
            continue;
        }
        if entry.qualified_name.module_path == typed.module_path {
            continue;
        }
        let Type::Fn(param_types_tc, ret) = &entry.scheme.ty else {
            unreachable!()
        };
        let sig_key: Vec<Type> = param_types_tc.iter().map(|(_, t)| t.clone()).collect();
        let dedup_key = (
            entry.name.clone(),
            entry.qualified_name.module_path.clone(),
            sig_key.clone(),
        );
        if !imported_fn_seen.insert(dedup_key) {
            continue;
        }
        let Some(fn_id) = ctx
            .callable_ids
            .get(&entry.qualified_name)
            .and_then(|cands| {
                if cands.len() == 1 {
                    Some(cands[0].1)
                } else {
                    cands
                        .iter()
                        .find(|(stored, _)| types_overlap(stored, &sig_key))
                        .map(|(_, id)| *id)
                }
            })
        else {
            continue;
        };
        let source_path = ModulePath::new(entry.qualified_name.module_path.clone());
        let exported_symbol = link_view
            .exported_fns_for(&source_path)
            .and_then(|mut fns| {
                fns.find_map(|s| {
                    if s.name != entry.qualified_name.local_name {
                        return None;
                    }
                    match &s.scheme.ty {
                        Type::Fn(p, _) => {
                            let stored: Vec<Type> = p.iter().map(|(_, t)| t.clone()).collect();
                            if types_overlap(&stored, &sig_key) {
                                Some(s.exported_symbol.clone())
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                })
            })
            .unwrap_or_else(|| entry.qualified_name.local_name.clone());
        imported_fns.push(ImportedFnDef {
            id: fn_id,
            name: entry.name.clone(),
            exported_symbol,
            source_module: entry.qualified_name.module_path.clone(),
            original_name: entry.qualified_name.local_name.clone(),
            param_types: param_types_tc
                .iter()
                .map(|(_, t)| t.clone().into())
                .collect(),
            return_type: (**ret).clone().into(),
        });
    }
    imported_fns
}

/// Build the `FnId → FnIdentity` lookup, including lifted lambdas
/// registered in `fn_ids`. `exported_symbol` is read from the
/// source-of-truth already computed earlier:
///
/// - Local fns → `functions[i].exported_symbol` (set by `lower_function_bodies`)
/// - Imported fns → `ImportedFnDef.exported_symbol` (set by `build_imported_fns`)
/// - Lifted synthetics keep `name` (unique names, no overload)
pub(super) fn build_fn_identities(
    ctx: &LowerCtx,
    functions: &[FnDef],
    imported_fns: &[ImportedFnDef],
) -> FxHashMap<FnId, FnIdentity> {
    let callable_by_id: FxHashMap<FnId, &QualifiedName> = ctx
        .callable_ids
        .iter()
        .flat_map(|(qn, cands)| cands.iter().map(move |(_, fid)| (*fid, qn)))
        .collect();
    let local_exported_by_id: FxHashMap<FnId, &str> = functions
        .iter()
        .map(|f| (f.id, f.exported_symbol.as_str()))
        .collect();
    let imported_exported_by_id: FxHashMap<FnId, &str> = imported_fns
        .iter()
        .map(|f| (f.id, f.exported_symbol.as_str()))
        .collect();
    let mut fn_identities = FxHashMap::default();
    for (name, candidates) in &ctx.fn_ids {
        for (_sig_key, id) in candidates {
            let id = *id;
            if fn_identities.contains_key(&id) {
                continue;
            }
            let identity = if crate::COMPILER_INTRINSICS.contains(&name.as_str()) {
                FnIdentity::Intrinsic { name: name.clone() }
            } else if let Some(qn) = callable_by_id.get(&id) {
                if qn.module_path == "__builtin__" {
                    FnIdentity::Intrinsic { name: name.clone() }
                } else if qn.module_path == ctx.module_path {
                    let exported_symbol = local_exported_by_id
                        .get(&id)
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| name.clone());
                    FnIdentity::Local {
                        name: name.clone(),
                        exported_symbol,
                    }
                } else {
                    let exported_symbol = imported_exported_by_id
                        .get(&id)
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| qn.local_name.clone());
                    FnIdentity::Imported {
                        canonical: CanonicalRef {
                            module: ModulePath::new(qn.module_path.clone()),
                            symbol: LocalSymbolKey::Function(qn.local_name.clone()),
                        },
                        local_alias: name.clone(),
                        exported_symbol,
                    }
                }
            } else {
                // Not in callable_ids: lifted synthetics (lambda$, ctor$,
                // fn_ref$, trait_ref$). Unique name, no overload.
                FnIdentity::Local {
                    name: name.clone(),
                    exported_symbol: name.clone(),
                }
            };
            fn_identities.insert(id, identity);
        }
    }
    fn_identities
}

/// Build `ExternFnDef`s from local extern declarations only. Cross-module
/// extern fns travel through `module.imported_extern_fns` instead. Every
/// type-var parameter constrained by an extern trait gets an
/// `ExternTraitBridge` so codegen can emit the correct interface witness.
pub(super) fn build_extern_fns(typed: &TypedModule, ctx: &LowerCtx) -> Vec<ExternFnDef> {
    let extern_trait_lookup: FxHashMap<
        &krypton_typechecker::typed_ast::TraitName,
        &krypton_typechecker::typed_ast::ExternTraitInfo,
    > = typed
        .extern_traits
        .iter()
        .map(|et| (&et.trait_name, et))
        .collect();
    let mut fn_constraints_by_name: FxHashMap<
        &str,
        &[(
            krypton_typechecker::typed_ast::TraitName,
            Vec<krypton_typechecker::types::TypeVarId>,
        )],
    > = typed
        .fn_types
        .iter()
        .filter(|e| !e.scheme.constraints.is_empty())
        .map(|e| (e.name.as_str(), e.scheme.constraints.as_slice()))
        .collect();
    for ext in &typed.extern_fns {
        if !ext.constraints.is_empty() {
            fn_constraints_by_name
                .entry(ext.name.as_str())
                .or_insert(ext.constraints.as_slice());
        }
    }
    let mut extern_fns = vec![];
    for ext in &typed.extern_fns {
        // Externs are singletons in fn_ids (check_duplicate_function_names
        // rejects extern/extern and extern/local collisions), so taking the
        // first entry is safe.
        let extern_fn_id = ctx
            .fn_ids
            .get(&ext.name)
            .and_then(|v| v.first())
            .map(|(_, id)| *id);
        if let Some(fn_id) = extern_fn_id {
            let ir_target = match &ext.target {
                krypton_parser::ast::ExternTarget::Java => ExternTarget::Java {
                    class: ext.module_path.clone(),
                },
                krypton_parser::ast::ExternTarget::Js => ExternTarget::Js {
                    module: ext.module_path.clone(),
                },
            };
            let fn_constraints = fn_constraints_by_name
                .get(ext.name.as_str())
                .copied()
                .unwrap_or(&[]);
            let bridge_params = ext
                .param_types
                .iter()
                .map(|param_ty| {
                    if let krypton_typechecker::types::Type::Var(tv_id) = param_ty {
                        for (trait_name, constrained_tvs) in fn_constraints {
                            if constrained_tvs.contains(tv_id) {
                                if let Some(et_info) = extern_trait_lookup.get(trait_name) {
                                    return Some(ExternTraitBridge {
                                        trait_name: trait_name.clone(),
                                        java_interface: et_info.java_interface.clone(),
                                    });
                                }
                            }
                        }
                    }
                    None
                })
                .collect();
            let call_kind = if ext.constructor {
                ExternCallKind::Constructor
            } else if ext.instance {
                ExternCallKind::Instance
            } else {
                ExternCallKind::Static
            };
            extern_fns.push(ExternFnDef {
                id: fn_id,
                name: ext.name.clone(),
                declaring_module_path: ext.declaring_module_path.clone(),
                span: ext.span,
                target: ir_target,
                nullable: ext.nullable,
                throws: ext.throws,
                call_kind,
                param_types: ext.param_types.iter().cloned().map(Into::into).collect(),
                return_type: ext.return_type.clone().into(),
                bridge_params,
            });
        }
    }
    extern_fns
}

/// Build `ExternTraitDef`s from local extern-trait declarations only.
pub(super) fn build_extern_traits(typed: &TypedModule) -> Vec<ExternTraitDef> {
    typed
        .extern_traits
        .iter()
        .map(|et| ExternTraitDef {
            trait_name: et.trait_name.clone(),
            java_interface: et.java_interface.clone(),
            methods: et
                .methods
                .iter()
                .map(|m| ExternTraitMethodDef {
                    name: m.name.clone(),
                    param_types: m.param_types.iter().cloned().map(Into::into).collect(),
                    return_type: m.return_type.clone().into(),
                })
                .collect(),
        })
        .collect()
}

/// Build `ExternTypeDef`s from local extern-type declarations (JVM
/// targets only). Cross-module extern types travel through
/// `module.imported_extern_types` instead.
pub(super) fn build_extern_types(typed: &TypedModule) -> Vec<ExternTypeDef> {
    let mut extern_types = vec![];
    for info in &typed.extern_types {
        if info.target == krypton_parser::ast::ExternTarget::Java {
            extern_types.push(ExternTypeDef {
                name: info.krypton_name.clone(),
                target: ExternTarget::Java {
                    class: info.host_module.clone(),
                },
            });
        }
    }
    extern_types
}

/// Build sorted `TraitDef`s from `typed.trait_defs`. Returns `LowerError`
/// when a trait method declared in `methods` is missing from
/// `method_tc_types` — that pairing is an upstream invariant the
/// typechecker is supposed to maintain.
pub(super) fn build_traits(typed: &TypedModule) -> Result<Vec<TraitDef>, LowerError> {
    let mut traits = vec![];
    for trait_def in &typed.trait_defs {
        let methods = trait_def
            .methods
            .iter()
            .map(|(method_name, param_count)| {
                let (param_types, return_type) = trait_def
                    .method_tc_types
                    .get(method_name)
                    .cloned()
                    .ok_or_else(|| {
                        LowerError::InternalError(format!(
                            "trait method {method_name} has no type info in method_tc_types"
                        ))
                    })?;
                let method_constraint_count = trait_def
                    .method_constraints
                    .get(method_name)
                    .map(|c| c.len())
                    .unwrap_or(0);
                Ok(TraitMethodDef {
                    name: method_name.clone(),
                    param_count: *param_count + method_constraint_count,
                    param_types: param_types.into_iter().map(|(_, t)| t.into()).collect(),
                    return_type: return_type.into(),
                })
            })
            .collect::<Result<Vec<_>, LowerError>>()?;
        traits.push(TraitDef {
            name: trait_def.name.clone(),
            trait_name: trait_def.trait_id.clone(),
            type_var: trait_def.type_var_id,
            type_var_ids: trait_def.type_var_ids.clone(),
            methods,
            is_imported: trait_def.is_imported,
            // `trait_def.superclasses` is already in the local TypeVarId
            // namespace paired with `trait_def.type_var_ids`; imported
            // traits are remapped to this namespace at import time, so
            // emitting the IR pair locally keeps codegen's substitution
            // input consistent regardless of how we build the lookup map.
            direct_superclasses: trait_def
                .superclasses
                .iter()
                .map(|(n, args)| (n.clone(), args.iter().cloned().map(IrType::from).collect()))
                .collect(),
        });
    }
    traits.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(traits)
}

/// Build `InstanceDef`s for both local and imported instances.
/// Local-instance method `FnId`s must be present (allocated by
/// `allocate_fn_ids`); imported-instance methods may be absent (their
/// definitions live in another module) and are dropped silently.
pub(super) fn build_instances(
    typed: &TypedModule,
    link_view: &krypton_typechecker::link_context::ModuleLinkView,
    ctx: &LowerCtx,
) -> Vec<InstanceDef> {
    // Instance method mangled names are unique per (trait, type, method)
    // — never overloaded — so the singleton entry in fn_ids is the only
    // one. For imported instances, missing methods just mean the def
    // lives elsewhere and we don't emit a stub here.
    let lower_instance = |inst: &krypton_typechecker::typed_ast::InstanceDefInfo,
                          is_imported: bool|
     -> InstanceDef {
        let method_fn_ids: Vec<(String, FnId)> = if is_imported {
            inst.methods
                .iter()
                .filter_map(|m| {
                    let mangled = typed_ast::mangled_method_name(
                        &inst.trait_name.local_name,
                        &inst.target_type_name,
                        &m.name,
                    );
                    ctx.fn_ids
                        .get(&mangled as &str)
                        .and_then(|v| v.first())
                        .map(|(_, fn_id)| (m.name.clone(), *fn_id))
                })
                .collect()
        } else {
            inst.methods
                .iter()
                .map(|m| {
                    let mangled = typed_ast::mangled_method_name(
                        &inst.trait_name.local_name,
                        &inst.target_type_name,
                        &m.name,
                    );
                    let (_, fn_id) = ctx
                        .fn_ids
                        .get(&mangled as &str)
                        .and_then(|v| v.first())
                        .unwrap_or_else(|| panic!("ICE: no FnId for instance method {mangled}"));
                    (m.name.clone(), *fn_id)
                })
                .collect()
        };
        // Dict slot layout: superclass slots first (trait-wide fixed
        // layout, so projections through a type-var dict param can
        // compute field indices without knowing the concrete impl's
        // impl-head count), then impl-head constraint sub_dicts. Layout
        // is pre-computed at the typechecker layer — see
        // `module_interface::compute_instance_sub_dict_requirements`.
        let sub_dict_requirements: InstanceSubDictList = inst
            .sub_dict_requirements
            .iter()
            .map(|(tn, tys)| (tn.clone(), tys.iter().cloned().map(IrType::from).collect()))
            .collect();
        InstanceDef {
            trait_name: inst.trait_name.clone(),
            target_types: inst.target_types.iter().cloned().map(Into::into).collect(),
            target_type_name: inst.target_type_name.clone(),
            method_fn_ids,
            sub_dict_requirements,
            is_intrinsic: inst.is_intrinsic,
            is_imported,
        }
    };
    let mut instances = vec![];
    for inst in &typed.instance_defs {
        instances.push(lower_instance(inst, false));
    }
    // `link_view` is reserved for imported-instance lowering; today we
    // only emit local instances here (imported instances are surfaced
    // through `imported_instances`), but keeping the hook in place
    // documents the eventual extension point.
    let _ = link_view;
    instances
}

/// Sweep every emitted FnDef and instance target type for tuple usage,
/// returning the deduplicated arity set. Codegen reads this to materialize
/// the tuple structs that the module references.
///
/// Named with the `module_` prefix to avoid colliding with the per-fn
/// helpers `collect_tuple_arities_from_fn` / `_from_type` defined further
/// down the file.
pub(super) fn collect_module_tuple_arities(
    functions: &[FnDef],
    instances: &[InstanceDef],
) -> std::collections::BTreeSet<usize> {
    let mut tuple_arities = std::collections::BTreeSet::new();
    for func in functions {
        collect_tuple_arities_from_fn(func, &mut tuple_arities);
    }
    for inst in instances {
        for ty in &inst.target_types {
            collect_tuple_arities_from_type(&ty.clone(), &mut tuple_arities);
        }
    }
    tuple_arities
}

/// Build the FnId-keyed dict-requirement map from `fn_types`,
/// `extern_fns`, and instance-method constraints (via `ctx.fn_constraints`).
/// Keying by FnId rather than by name lets overload siblings carry distinct
/// dict requirements; sig_key matching uses `types_overlap` to pick the
/// right overload from `callable_ids`.
pub(super) fn build_fn_dict_requirements(
    typed: &TypedModule,
    ctx: &LowerCtx,
) -> FxHashMap<FnId, TraitConstraintList> {
    let mut reqs: FxHashMap<FnId, TraitConstraintList> = FxHashMap::default();
    let resolve_fn_id = |callable_ids: &FxHashMap<QualifiedName, Vec<(Vec<Type>, FnId)>>,
                         qn: &QualifiedName,
                         sig_key: &[Type]|
     -> Option<FnId> {
        let cands = callable_ids.get(qn)?;
        if cands.len() == 1 {
            return Some(cands[0].1);
        }
        cands
            .iter()
            .find(|(stored, _)| types_overlap(stored, sig_key))
            .map(|(_, id)| *id)
    };
    for entry in &typed.fn_types {
        if entry.scheme.constraints.is_empty() {
            continue;
        }
        let sig_key: Vec<Type> = match &entry.scheme.ty {
            Type::Fn(p, _) => p.iter().map(|(_, t)| t.clone()).collect(),
            _ => Vec::new(),
        };
        if let Some(fn_id) = resolve_fn_id(&ctx.callable_ids, &entry.qualified_name, &sig_key) {
            reqs.entry(fn_id)
                .or_insert_with(|| entry.scheme.constraints.clone());
        }
    }
    for ext in &typed.extern_fns {
        if ext.constraints.is_empty() {
            continue;
        }
        // Externs are singletons; use the only entry in fn_ids.
        if let Some(cands) = ctx.fn_ids.get(&ext.name) {
            if let Some((_, fn_id)) = cands.first() {
                reqs.entry(*fn_id)
                    .or_insert_with(|| ext.constraints.clone());
            }
        }
    }
    for (qn, v) in &ctx.fn_constraints {
        if qn.module_path != typed.module_path {
            continue;
        }
        // Instance method mangled names map to a single FnId
        // (mangled names are unique per (trait, type, method)).
        if let Some(cands) = ctx.callable_ids.get(qn) {
            if let Some((_, fn_id)) = cands.first() {
                reqs.entry(*fn_id).or_insert_with(|| v.clone());
            }
        }
    }
    reqs
}

/// Lower a `TypedModule` to an IR `Module`.
///
/// Each IR module is a self-contained compilation unit: local definitions plus
/// cross-module metadata (imported_structs, imported_sum_types, imported_extern_fns,
/// imported_extern_types, imported_instances). The codegen compiles each module
/// independently without access to other modules' IR.
///
/// `imported_instances` provides instance defs from other modules needed for
/// cross-module dict-passing resolution during lowering. `imported_extern_fns`
/// provides extern fn declarations from other modules needed for FnId
/// allocation (so calls to imported externs can be resolved).
pub fn lower_module(
    typed: &TypedModule,
    module_name: &str,
    link_view: &krypton_typechecker::link_context::ModuleLinkView,
) -> Result<Module, LowerError> {
    let fn_constraints = build_fn_constraints(typed);
    let fn_schemes = build_fn_schemes(typed);
    let param_instances = build_param_instances(typed, link_view);
    let all_instances = build_all_instances(typed, link_view);
    let trait_method_types = build_trait_method_types(typed);
    let trait_method_constraints = build_trait_method_constraints(typed);

    let mut ctx = LowerCtx::new(
        link_view,
        typed.module_path.clone(),
        typed.auto_close.clone(),
        fn_constraints,
        fn_schemes,
        param_instances,
        all_instances,
        trait_method_types,
        trait_method_constraints,
    );
    // Reserve the IR-side `type_var_gen` past every TypeVarId visible from
    // the typechecker so fresh allocations made during lowering (instance
    // dispatch, defensive private-type fallback, expression freshening)
    // cannot collide with registry-allocated ids carried in
    // `exported_type_infos`, fn schemes, or instance defs.
    seed_type_var_gen_past_typed(typed, &mut ctx.type_var_gen);
    ctx.register_struct_layouts(typed);
    ctx.register_sum_variants(typed);
    let local_fn_allocs = ctx.allocate_fn_ids(typed)?;

    let structs = lower_struct_defs(typed, &ctx);
    let sum_types = lower_sum_type_defs(typed, &ctx);

    let mut functions = lower_function_bodies(typed, &mut ctx, local_fn_allocs)?;
    functions.append(&mut ctx.lifted_fns);

    let imported_fns = build_imported_fns(typed, &ctx, link_view);
    let fn_identities = build_fn_identities(&ctx, &functions, &imported_fns);

    let extern_fns = build_extern_fns(typed, &ctx);
    let extern_traits = build_extern_traits(typed);
    let extern_types = build_extern_types(typed);
    let traits = build_traits(typed)?;
    let instances = build_instances(typed, link_view, &ctx);
    let tuple_arities = collect_module_tuple_arities(&functions, &instances);
    let fn_dict_requirements = build_fn_dict_requirements(typed, &ctx);

    let module = Module {
        name: module_name.to_string(),
        structs,
        sum_types,
        functions,
        fn_identities,
        extern_fns,
        extern_types,
        extern_traits,
        imported_fns,
        traits,
        instances,
        tuple_arities,
        module_path: ModulePath::new(typed.module_path.clone()),
        fn_dict_requirements,
        fn_exit_closes: ctx.fn_exit_closes,
    };

    let reachable_trait_names: FxHashSet<TraitName> = link_view
        .all_traits()
        .iter()
        .map(|(path, t)| TraitName::new(path.as_str().to_string(), t.name.clone()))
        .collect();

    crate::lint::LintPass
        .run_with_known_traits(module, reachable_trait_names)
        .map_err(|e| LowerError::InternalError(format!("{}: {}", e.pass, e.message)))
}

/// Lower all typed modules to IR and collect their source texts.
///
/// The first module is treated as the root: its IR name is set to `root_name`,
/// while subsequent modules keep their `module_path`.
///
/// Returns `(ir_modules, module_sources)` where `module_sources` maps
/// `module_path → source_text` for error rendering during codegen.
pub fn lower_all(
    typed_modules: &[TypedModule],
    root_name: &str,
    link_ctx: &LinkContext,
) -> Result<(Vec<Module>, FxHashMap<String, String>), LowerError> {
    let root_module_path = typed_modules
        .first()
        .map(|tm| tm.module_path.as_str())
        .unwrap_or("");

    let mut ir_modules = Vec::with_capacity(typed_modules.len());
    let mut module_sources: FxHashMap<String, String> = FxHashMap::default();

    for tm in typed_modules {
        let is_root = tm.module_path == root_module_path;
        let mod_name = if is_root { root_name } else { &tm.module_path };
        let view = link_ctx
            .view_for(&krypton_typechecker::module_interface::ModulePath::new(
                &tm.module_path,
            ))
            .unwrap_or_else(|| panic!("ICE: no LinkContext view for module '{}'", tm.module_path));
        let ir = lower_module(tm, mod_name, &view)?;
        ir_modules.push(ir);
        if let Some(src) = &tm.module_source {
            module_sources.insert(tm.module_path.clone(), src.clone());
        }
    }

    Ok((ir_modules, module_sources))
}

