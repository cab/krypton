use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Decl, FnDecl, Module, Span, Visibility};

use crate::overload::types_overlap;
use crate::trait_name_resolver::TraitNameResolver;
use crate::trait_registry::{InstanceInfo, TraitInfo, TraitMethod, TraitRegistry};
use crate::type_registry::{self, ResolutionContext, TypeRegistry};
use crate::typed_ast::{
    ExportedTraitDef, ExportedTraitMethod, ExternTraitInfo, ExternTraitMethodInfo, InstanceDefInfo,
    TraitName,
};
use crate::types::{Type, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::extern_decl::PendingExternTrait;
use super::helpers::{remap_type_vars, require_param_vars, spanned};
use super::state::{ModuleInferenceState, TraitsAndDerivingResult};

pub(super) fn process_traits_and_deriving(
    state: &mut ModuleInferenceState,
    module: &Module,
    interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
    module_path: &str,
    is_core_module: bool,
    pending_extern_traits: Vec<PendingExternTrait>,
) -> Result<TraitsAndDerivingResult, SpannedTypeError> {
    let mut trait_registry = TraitRegistry::new();

    // Phase 1: Import instances from cached modules via orphan-rule lookup
    let imported_instance_defs = import_cached_instances(
        &mut trait_registry,
        &state.imports.imported_type_info,
        &state.imported_trait_defs,
        interface_cache,
    );

    // Phase 2: Register imported trait definitions
    register_imported_trait_defs(
        &mut trait_registry,
        &mut state.trait_names,
        &state.imported_trait_defs,
        &mut state.gen,
        &state.prelude_imported_names,
    );

    // Phase 2b: Register trait aliases from imports
    for (alias, canonical) in &state.trait_aliases {
        trait_registry.register_trait_alias(alias.clone(), canonical.clone());
        state
            .trait_names
            .register_alias(alias.clone(), canonical.clone());
    }

    // Phase 2c: Register extern traits (Java interfaces exposed as Krypton traits)
    let (extern_trait_exported_defs, extern_trait_infos) = register_extern_traits(
        state,
        &mut trait_registry,
        pending_extern_traits,
        module_path,
    )?;

    // Phase 3: Process local DefTrait declarations
    let mut exported_trait_defs =
        register_local_traits(state, &mut trait_registry, module, module_path)?;
    exported_trait_defs.extend(extern_trait_exported_defs);

    // Phase 4: Process DefImpl declarations (register instances). User
    // impls are registered before the deriving pass so that derivings can
    // satisfy their field-constraint obligations against local impls.
    // E.g. `type Conn { s: ~Sock, l: ~Log } deriving (Disposable)` needs
    // `impl Disposable[Sock]` and `impl Disposable[Log]` visible when the
    // derivation is checked. The hard-error on duplicate impls still
    // triggers: `DerivingConflictsWithImpl` is detected at the top of
    // `process_deriving` by scanning `module.decls` directly.
    super::impls::register_impl_instances(state, &mut trait_registry, module, module_path)?;

    // Phase 5: Deriving pass
    let derived_instance_defs = super::deriving_pass::process_deriving(
        &mut trait_registry,
        &state.trait_names,
        module,
        &state.registry,
        module_path,
    )?;

    // Compute trait_method_map between phases 5 and 6, with collision detection
    let mut trait_method_map: FxHashMap<String, TraitName> = FxHashMap::default();
    for (method_name, trait_id, is_prelude) in trait_registry.trait_method_names() {
        if let Some(existing) = trait_method_map.get(&method_name) {
            let existing_is_prelude = trait_registry
                .lookup_trait(existing)
                .is_some_and(|info| info.is_prelude);
            if !existing_is_prelude && !is_prelude {
                // Two non-prelude traits with same method name — check overlap
                let existing_params =
                    trait_method_param_types(&trait_registry, existing, &method_name);
                let new_params = trait_method_param_types(&trait_registry, &trait_id, &method_name);
                let overlaps = match (&existing_params, &new_params) {
                    (Some(a), Some(b)) => {
                        if a.len() != b.len() {
                            true // arity mismatch
                        } else {
                            types_overlap(a, b)
                        }
                    }
                    _ => true, // can't resolve → assume overlap
                };
                if overlaps {
                    return Err(spanned(
                        TypeError::TraitMethodCollision {
                            method_name: method_name.clone(),
                            trait1: existing.local_name.clone(),
                            trait2: trait_id.local_name.clone(),
                        },
                        (0, 0),
                    ));
                }
                // Non-overlapping — first wins for trait_method_map
            } else if existing_is_prelude && !is_prelude {
                // Local shadows prelude
                trait_method_map.insert(method_name, trait_id);
            }
            // If existing is not prelude and new is prelude → skip (local wins)
            // If both prelude → keep existing (prelude is curated, first wins)
        } else {
            trait_method_map.insert(method_name, trait_id);
        }
    }

    // Phase 6: Conflict and reserved-name checks
    check_trait_name_conflicts(
        module,
        &trait_method_map,
        &trait_registry,
        &state.trait_names,
        &state.registry,
        is_core_module,
    )?;

    Ok((
        trait_registry,
        exported_trait_defs,
        extern_trait_infos,
        derived_instance_defs,
        imported_instance_defs,
        trait_method_map,
    ))
}

/// Phase 1: Import instances from cached modules via orphan-rule lookup.
pub(super) fn import_cached_instances(
    trait_registry: &mut TraitRegistry,
    imported_type_info: &FxHashMap<String, (String, Visibility)>,
    imported_trait_defs: &[ExportedTraitDef],
    interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
) -> Vec<InstanceDefInfo> {
    let mut imported_instance_defs = Vec::new();
    // Structural instance lookup: for each type/trait in scope, look up instances
    // in the defining module. The orphan rule guarantees instances live in the
    // module defining the type or the trait.
    let mut source_modules: FxHashSet<&str> = FxHashSet::default();
    for (source_path, _) in imported_type_info.values() {
        source_modules.insert(source_path.as_str());
    }
    // Include modules that define imported traits (covers core modules
    // providing instances for builtin types like Int, Bool, etc.)
    for td in imported_trait_defs {
        source_modules.insert(td.module_path.as_str());
    }
    // Vec is a language-level builtin (array literal syntax []),
    // so always include its defining module for instance resolution.
    source_modules.insert("core/vec");

    let mut seen_instances: FxHashSet<(TraitName, Vec<Type>)> = FxHashSet::default();
    for mod_path in &source_modules {
        if let Some(iface) = interface_cache.get(*mod_path) {
            for inst_summary in &iface.exported_instances {
                let key = (
                    inst_summary.trait_name.clone(),
                    inst_summary.target_types.clone(),
                );
                if seen_instances.insert(key) {
                    let instance = InstanceInfo {
                        trait_name: inst_summary.trait_name.clone(),
                        target_types: inst_summary.target_types.clone(),
                        target_type_name: inst_summary.target_type_name.clone(),
                        type_var_ids: inst_summary.type_var_ids.clone(),
                        constraints: inst_summary.constraints.clone(),
                        span: (0, 0),
                        is_builtin: false,
                    };
                    match trait_registry.register_instance(instance) {
                        Ok(()) => {}
                        Err(boxed) => match *boxed {
                            (TypeError::DuplicateInstance { .. }, _) => {
                                // Expected: same instance imported via multiple transitive paths
                            }
                            (e, span) => {
                                panic!("ICE: unexpected error registering imported instance: {e:?} at {span:?}")
                            }
                        },
                    }
                    imported_instance_defs.push(
                        crate::module_interface::instance_summary_to_def_info(inst_summary),
                    );
                }
            }
        }
    }
    imported_instance_defs
}

/// Phase 2: Register trait definitions imported from other modules.
///
/// The bare-name map is owned by `trait_names` (populated at import time by
/// `process_single_import`); this function only pushes the trait defs into
/// `trait_registry.traits`. Internally-imported origins (from re-exported trait
/// methods) are already tagged via `trait_names.register_internal`, so their
/// defs land here without any bare-name entry.
pub(super) fn register_imported_trait_defs(
    trait_registry: &mut TraitRegistry,
    trait_names: &mut TraitNameResolver,
    imported_trait_defs: &[ExportedTraitDef],
    gen: &mut TypeVarGen,
    prelude_imported_names: &FxHashSet<String>,
) {
    // Register trait definitions imported from other modules
    for trait_def in imported_trait_defs {
        // Skip if this exact trait (same TraitName) is already registered
        let trait_id = TraitName::new(trait_def.module_path.clone(), trait_def.name.clone());
        if trait_registry.lookup_trait(&trait_id).is_some() {
            continue;
        }

        // Build remap table covering primary + all secondary trait type vars.
        // The source module uses its own TypeVarId namespace; we allocate fresh
        // ids in the local namespace so that imported method types unify cleanly.
        let new_tv_id = gen.fresh();
        let mut new_type_var_ids: Vec<TypeVarId> = Vec::with_capacity(trait_def.type_var_ids.len());
        new_type_var_ids.push(new_tv_id);
        let mut remap: FxHashMap<TypeVarId, TypeVarId> = FxHashMap::default();
        if let Some(&primary_old) = trait_def.type_var_ids.first() {
            remap.insert(primary_old, new_tv_id);
        } else {
            remap.insert(trait_def.type_var_id, new_tv_id);
        }
        for &old_id in trait_def.type_var_ids.iter().skip(1) {
            let new_id = gen.fresh();
            remap.insert(old_id, new_id);
            new_type_var_ids.push(new_id);
        }

        let mut trait_methods = Vec::new();
        for method in &trait_def.methods {
            let param_types: Vec<(crate::types::ParamMode, Type)> = method
                .param_types
                .iter()
                .map(|(m, t)| (*m, remap_type_vars(t, &remap)))
                .collect();
            let return_type = remap_type_vars(&method.return_type, &remap);

            // Method constraints use the method's own type vars (not the trait's),
            // so they don't need remapping.
            trait_methods.push(TraitMethod {
                name: method.name.clone(),
                param_types,
                return_type,
                constraints: method.constraints.clone(),
            });
        }

        // Silently-imported trait defs (origin of a re-exported trait method
        // whose bare name is not user-visible in this module) behave like
        // prelude traits for method-dispatch priority: a local `trait Functor`
        // declared in the same module should win over the silent import.
        // At this phase no locals are registered yet, so a bare-name hit
        // means the user explicitly imported the trait; a miss means it
        // arrived silently via a re-exported method origin.
        let is_silently_imported = trait_names.resolve(&trait_def.name).is_none();
        let is_prelude = prelude_imported_names.contains(&trait_def.name) || is_silently_imported;
        // Remap each stored superclass arg so it references the local
        // namespace's TypeVarIds (parallel to how method signatures were
        // remapped above).
        let remapped_superclasses: Vec<(TraitName, Vec<Type>)> = trait_def
            .superclasses
            .iter()
            .map(|(tn, args)| {
                (
                    tn.clone(),
                    args.iter().map(|t| remap_type_vars(t, &remap)).collect(),
                )
            })
            .collect();
        // Bare-name ambiguity is now caught in `TraitNameResolver`; aliases
        // are recorded via `TraitNameResolver::register_alias` before this
        // phase. The only remaining error this `register_trait` call can
        // surface is `DuplicateTrait` — the same trait def arrived via
        // multiple import paths (e.g. direct `import core/eq` plus transitive
        // via prelude). Keep the first registration.
        match trait_registry.register_trait(TraitInfo {
            name: trait_def.name.clone(),
            module_path: trait_def.module_path.clone(),
            type_var: trait_def.type_var.clone(),
            type_var_id: new_tv_id,
            type_var_ids: new_type_var_ids,
            type_var_names: trait_def.type_var_names.clone(),
            type_var_arity: trait_def.type_var_arity,
            superclasses: remapped_superclasses,
            methods: trait_methods,
            span: (0, 0),
            is_prelude,
        }) {
            Ok(()) => {}
            Err(TypeError::DuplicateTrait { .. }) => continue,
            Err(other) => {
                panic!("ICE: unexpected error registering imported trait def: {other:?}");
            }
        }
    }
}

/// Phase 2c: Register extern traits (Java interfaces exposed as Krypton traits).
///
/// Each `extern java "..." as trait Name[a] { ... }` is registered as a real trait
/// in the TraitRegistry. Methods are bound into the environment via `bind_trait_method`,
/// making them callable like any other trait method.
pub(super) fn register_extern_traits(
    state: &mut ModuleInferenceState,
    trait_registry: &mut TraitRegistry,
    pending: Vec<PendingExternTrait>,
    module_path: &str,
) -> Result<(Vec<ExportedTraitDef>, Vec<ExternTraitInfo>), SpannedTypeError> {
    let mut exported_defs = Vec::new();
    let mut extern_trait_infos = Vec::new();

    let empty_tp_arity: FxHashMap<String, usize> = FxHashMap::default();

    for ext in pending {
        // Allocate fresh type var for the trait's type parameter
        if ext.type_params.is_empty() {
            return Err(spanned(
                TypeError::WrongArity {
                    expected: 1,
                    actual: 0,
                },
                ext.span,
            ));
        }

        let tv_id = state.gen.fresh();
        let type_var_name = ext.type_params[0].clone();

        // Build type param map for resolving method types
        let mut tp_map = FxHashMap::default();
        tp_map.insert(type_var_name.clone(), tv_id);
        // Additional type params (rare but supported)
        let mut all_tv_ids = vec![tv_id];
        for tp in &ext.type_params[1..] {
            let id = state.gen.fresh();
            tp_map.insert(tp.clone(), id);
            all_tv_ids.push(id);
        }

        let trait_name = TraitName::new(module_path.to_string(), ext.name.clone());
        let mut trait_methods = Vec::new();
        let mut exported_methods = Vec::new();
        let mut extern_method_infos = Vec::new();

        for method in &ext.methods {
            // Validate: no @nullable or @throws on trait methods
            if method.nullable {
                return Err(spanned(
                    TypeError::InvalidNullableReturn {
                        name: method.name.clone(),
                        actual_return_type: Type::Named("Unit".to_string(), vec![]),
                    },
                    method.span,
                ));
            }
            if method.throws {
                return Err(spanned(
                    TypeError::InvalidThrowsReturn {
                        name: method.name.clone(),
                        actual_return_type: Type::Named("Unit".to_string(), vec![]),
                    },
                    method.span,
                ));
            }

            // Resolve param types using the trait's type param map
            let mut param_types = Vec::new();
            for (_param_name, ty_expr) in &method.params {
                let ty = type_registry::resolve_type_expr(
                    ty_expr,
                    &tp_map,
                    &empty_tp_arity,
                    &state.registry,
                    ResolutionContext::UserAnnotation,
                    None,
                )
                .map_err(|e| spanned(e, method.span))?;
                param_types.push(ty);
            }

            let return_type = type_registry::resolve_type_expr(
                &method.return_type,
                &tp_map,
                &empty_tp_arity,
                &state.registry,
                ResolutionContext::UserAnnotation,
                None,
            )
            .map_err(|e| spanned(e, method.span))?;

            // Build TypeScheme for the method: forall [tv_id]. param_types -> return_type
            let fn_type = Type::fn_consuming(param_types.clone(), return_type.clone());
            let var_names: FxHashMap<TypeVarId, String> = all_tv_ids
                .iter()
                .zip(ext.type_params.iter())
                .map(|(id, name)| (*id, name.clone()))
                .collect();
            let scheme = TypeScheme {
                vars: all_tv_ids.clone(),
                constraints: vec![],
                ty: fn_type,
                var_names,
            };

            // Bind the method into the type environment
            state.env.bind_trait_method(
                method.name.clone(),
                scheme,
                module_path.to_string(),
                ext.name.clone(),
                method.name.clone(),
                false,
            );

            // Collect param types excluding self for the extern trait method info.
            // Only remove the *first* param matching the trait type var (the self
            // param) — later params with the same type should be kept.
            let self_index = param_types
                .iter()
                .position(|t| matches!(t, Type::Var(id) if *id == tv_id));
            let non_self_param_types: Vec<Type> = param_types
                .iter()
                .enumerate()
                .filter(|(i, _)| Some(*i) != self_index)
                .map(|(_, t)| t.clone())
                .collect();

            // Extern trait methods are currently mode-erased to `Consume`:
            // the parser's `ExternMethod` has no per-param mode field, so
            // every extern trait parameter lands in the trait registry as
            // `ParamMode::Consume`. The witness-side exact-mode check in
            // `typecheck_impl_methods` therefore enforces `Consume` on every
            // Krypton-side impl of an extern trait, which matches the only
            // shape a user can currently declare. Widening extern method
            // modes is a follow-up.
            let param_types_with_modes: Vec<(crate::types::ParamMode, Type)> = param_types
                .iter()
                .cloned()
                .map(|t| (crate::types::ParamMode::Consume, t))
                .collect();

            trait_methods.push(TraitMethod {
                name: method.name.clone(),
                param_types: param_types_with_modes.clone(),
                return_type: return_type.clone(),
                constraints: vec![],
            });

            exported_methods.push(ExportedTraitMethod {
                name: method.name.clone(),
                param_types: param_types_with_modes.clone(),
                return_type: return_type.clone(),
                constraints: vec![],
            });

            extern_method_infos.push(ExternTraitMethodInfo {
                name: method.name.clone(),
                param_types: non_self_param_types,
                return_type: return_type.clone(),
            });
        }

        // Register in the trait registry
        trait_registry
            .register_trait(TraitInfo {
                name: ext.name.clone(),
                module_path: module_path.to_string(),
                type_var: type_var_name.clone(),
                type_var_id: tv_id,
                type_var_ids: all_tv_ids.clone(),
                type_var_names: ext.type_params.clone(),
                type_var_arity: 0,
                superclasses: vec![],
                methods: trait_methods,
                span: ext.span,
                is_prelude: false,
            })
            .map_err(|e| spanned(e, ext.span))?;
        state
            .trait_names
            .register_local(ext.name.clone(), trait_name.clone())
            .map_err(|e| spanned(e, ext.span))?;

        exported_defs.push(ExportedTraitDef {
            visibility: Visibility::Pub,
            name: ext.name.clone(),
            module_path: module_path.to_string(),
            type_var: type_var_name,
            type_var_id: tv_id,
            type_var_ids: all_tv_ids,
            type_var_names: ext.type_params.clone(),
            type_var_arity: 0,
            superclasses: vec![],
            methods: exported_methods,
        });

        extern_trait_infos.push(ExternTraitInfo {
            trait_name,
            java_interface: ext.java_interface,
            methods: extern_method_infos,
        });
    }

    Ok((exported_defs, extern_trait_infos))
}

/// Phase 3: Process local DefTrait declarations.
pub(super) fn register_local_traits(
    state: &mut ModuleInferenceState,
    trait_registry: &mut TraitRegistry,
    module: &Module,
    module_path: &str,
) -> Result<Vec<ExportedTraitDef>, SpannedTypeError> {
    // Process DefTrait declarations
    let mut exported_trait_defs: Vec<ExportedTraitDef> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefTrait {
            visibility,
            name,
            type_params: trait_type_params,
            superclasses,
            methods,
            span,
            ..
        } = decl
        {
            // Type-namespace check: `name` must not already exist as a type
            // (or type alias) in this module. Prelude types are shadowable.
            if let Some(existing_type) = state.registry.lookup_type(name) {
                if !existing_type.is_prelude {
                    return Err(spanned(
                        TypeError::TypeTraitNameConflict { name: name.clone() },
                        *span,
                    ));
                }
            }
            // Type-namespace check: `name` must not already be declared as a
            // trait in this module. Prelude traits are shadowable.
            if let Some(existing_trait) = state.resolve_trait(trait_registry, name) {
                if !existing_trait.is_prelude {
                    return Err(spanned(
                        TypeError::DuplicateTrait { name: name.clone() },
                        *span,
                    ));
                }
            }
            // Index the first trait type parameter for arity/InstanceInfo but
            // register ALL trait type parameters in the method resolution
            // environment so multi-parameter trait method bodies can reference
            // `b`, `c`, etc.
            let type_param = &trait_type_params[0];
            let tv_id = state.gen.fresh();
            let type_var_arity = type_param.arity;
            let mut type_param_map = FxHashMap::default();
            let mut type_param_arity = FxHashMap::default();
            type_param_map.insert(type_param.name.clone(), tv_id);
            type_param_arity.insert(type_param.name.clone(), type_param.arity);
            // Track ALL trait type parameter ids in declaration order so the
            // multi-param resolution pass can freshen each one at call sites.
            let mut trait_all_tv_ids: Vec<TypeVarId> = vec![tv_id];
            let mut trait_all_tv_names: Vec<String> = vec![type_param.name.clone()];
            for extra in trait_type_params.iter().skip(1) {
                let extra_id = state.gen.fresh();
                type_param_map.insert(extra.name.clone(), extra_id);
                type_param_arity.insert(extra.name.clone(), extra.arity);
                trait_all_tv_ids.push(extra_id);
                trait_all_tv_names.push(extra.name.clone());
            }

            // Check that all trait methods have explicit return type annotations
            for method in methods {
                if method.return_type.is_none() {
                    return Err(spanned(
                        TypeError::MissingTraitMethodAnnotation {
                            trait_name: name.clone(),
                            method_name: method.name.clone(),
                        },
                        method.span,
                    ));
                }
            }

            let mut trait_methods = Vec::new();
            let mut exported_methods = Vec::new();
            for method in methods {
                let mut method_type_param_map = type_param_map.clone();
                let mut method_type_param_arity = type_param_arity.clone();
                let mut method_tv_ids = Vec::new();
                for tv_param in &method.type_params {
                    if !method_type_param_map.contains_key(&tv_param.name) {
                        let mv_id = state.gen.fresh();
                        method_type_param_map.insert(tv_param.name.clone(), mv_id);
                        method_type_param_arity.insert(tv_param.name.clone(), tv_param.arity);
                        method_tv_ids.push(mv_id);
                    }
                }

                let mut param_types = Vec::new();
                let mut param_modes: Vec<crate::types::ParamMode> = Vec::new();
                for p in &method.params {
                    param_modes.push(p.mode);
                    if let Some(ref ty_expr) = p.ty {
                        param_types.push(
                            type_registry::resolve_type_expr(
                                ty_expr,
                                &method_type_param_map,
                                &method_type_param_arity,
                                &state.registry,
                                ResolutionContext::UserAnnotation,
                                None,
                            )
                            .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                            .map_err(|e| spanned(e, method.span))?,
                        );
                    } else {
                        param_types.push(Type::Var(state.gen.fresh()));
                    }
                }
                let return_type = if let Some(ref ret_expr) = method.return_type {
                    type_registry::resolve_type_expr(
                        ret_expr,
                        &method_type_param_map,
                        &method_type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, method.span))?
                } else {
                    Type::Var(state.gen.fresh())
                };

                // Shape-var cap: at most 6 `shape` variables per trait
                // method. The cap exists to protect the compiler from
                // wedging on cartesian-product enumeration (2^N forks per
                // method body); 6 → 64 forks. `shape` is a def-site
                // polymorphism mechanism and real use cases past N=2 are
                // unknown, so 6 is a sanity bound, not a user restriction.
                // Enforced at trait registration so every impl path sees
                // a well-formed method.
                {
                    let mut shape_vars: Vec<TypeVarId> = Vec::new();
                    let mut seen: rustc_hash::FxHashSet<TypeVarId> =
                        rustc_hash::FxHashSet::default();
                    for pt in &param_types {
                        for v in crate::types::collect_shape_vars(pt) {
                            if seen.insert(v) {
                                shape_vars.push(v);
                            }
                        }
                    }
                    for v in crate::types::collect_shape_vars(&return_type) {
                        if seen.insert(v) {
                            shape_vars.push(v);
                        }
                    }
                    if shape_vars.len() > 6 {
                        return Err(spanned(
                            TypeError::TooManyShapeParameters {
                                trait_name: name.clone(),
                                method_name: method.name.clone(),
                                count: shape_vars.len(),
                            },
                            method.span,
                        ));
                    }
                }

                let fn_ty = Type::Fn(
                    param_modes
                        .iter()
                        .copied()
                        .zip(param_types.iter().cloned())
                        .collect(),
                    Box::new(return_type.clone()),
                );
                // Include ALL trait type parameter ids (not just the primary) so
                // `scheme.instantiate()` freshens secondary trait params at every
                // call site. Without this, `b` in `Convert[a, b]` would leak across
                // call sites and the multi-param solver would never see fresh ids.
                let mut all_vars = trait_all_tv_ids.clone();
                all_vars.extend_from_slice(&method_tv_ids);
                let scheme = TypeScheme {
                    vars: all_vars,
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: FxHashMap::default(),
                };
                state.env.bind_trait_method(
                    method.name.clone(),
                    scheme,
                    module_path.to_string(),
                    name.clone(),
                    method.name.clone(),
                    false,
                );

                // Resolve method-level where constraints
                let mut method_constraints: Vec<(TraitName, Vec<TypeVarId>)> = Vec::new();
                for constraint in &method.constraints {
                    let tv_names = require_param_vars(constraint)?;
                    let tvs: Vec<TypeVarId> = tv_names
                        .iter()
                        .filter_map(|n| method_type_param_map.get(*n).copied())
                        .collect();
                    if tvs.len() == tv_names.len() && !tvs.is_empty() {
                        // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
                        // Validation deferred to instance resolution phase.
                        let tn = state
                            .resolve_trait(trait_registry, &constraint.trait_name)
                            .map(|ti| ti.trait_name())
                            .unwrap_or_else(|| {
                                TraitName::new(
                                    module_path.to_string(),
                                    constraint.trait_name.clone(),
                                )
                            });
                        method_constraints.push((tn, tvs));
                    }
                }

                let param_types_with_modes: Vec<(crate::types::ParamMode, Type)> = param_modes
                    .iter()
                    .copied()
                    .zip(param_types.iter().cloned())
                    .collect();

                exported_methods.push(ExportedTraitMethod {
                    name: method.name.clone(),
                    param_types: param_types_with_modes.clone(),
                    return_type: return_type.clone(),
                    constraints: method_constraints.clone(),
                });

                trait_methods.push(TraitMethod {
                    name: method.name.clone(),
                    param_types: param_types_with_modes,
                    return_type,
                    constraints: method_constraints,
                });
            }

            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
            // Validation deferred to instance resolution phase. `require_param_vars`
            // also rejects any arg that isn't a bare type variable.
            let mut superclass_entries: Vec<(TraitName, Vec<Type>)> =
                Vec::with_capacity(superclasses.len());
            for sc in superclasses {
                require_param_vars(sc)?;
                let sc_trait_name = state
                    .resolve_trait(trait_registry, &sc.trait_name)
                    .map(|ti| ti.trait_name())
                    .unwrap_or_else(|| {
                        TraitName::new(module_path.to_string(), sc.trait_name.clone())
                    });
                let mut sc_args: Vec<Type> = Vec::with_capacity(sc.type_args.len());
                for ta in &sc.type_args {
                    let ty = type_registry::resolve_type_expr(
                        ta,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, sc.span))?;
                    sc_args.push(ty);
                }
                superclass_entries.push((sc_trait_name, sc_args));
            }
            let local_trait_name = TraitName::new(module_path.to_string(), name.clone());
            trait_registry
                .register_trait(TraitInfo {
                    name: name.clone(),
                    module_path: module_path.to_string(),
                    type_var: type_param.name.clone(),
                    type_var_id: tv_id,
                    type_var_ids: trait_all_tv_ids.clone(),
                    type_var_names: trait_all_tv_names.clone(),
                    type_var_arity,
                    superclasses: superclass_entries.clone(),
                    methods: trait_methods,
                    span: *span,
                    is_prelude: false,
                })
                .map_err(|e| spanned(e, *span))?;
            state
                .trait_names
                .register_local(name.clone(), local_trait_name)
                .map_err(|e| spanned(e, *span))?;

            exported_trait_defs.push(ExportedTraitDef {
                visibility: *visibility,
                name: name.clone(),
                module_path: module_path.to_string(),
                type_var: type_param.name.clone(),
                type_var_id: tv_id,
                type_var_ids: trait_all_tv_ids,
                type_var_names: trait_all_tv_names,
                type_var_arity,
                superclasses: superclass_entries,
                methods: exported_methods,
            });
        }
    }
    Ok(exported_trait_defs)
}
pub(super) fn resolve_fn_param_types_for_overlap(
    f: &FnDecl,
    registry: &TypeRegistry,
) -> Option<Vec<Type>> {
    let type_exprs: Vec<&krypton_parser::ast::TypeExpr> = f
        .params
        .iter()
        .map(|p| p.ty.as_ref())
        .collect::<Option<Vec<_>>>()?;

    let mut gen = TypeVarGen::new();
    let mut type_param_map = FxHashMap::default();
    let mut type_param_arity = FxHashMap::default();
    for tp in &f.type_params {
        let id = gen.fresh();
        type_param_map.insert(tp.name.clone(), id);
        type_param_arity.insert(tp.name.clone(), tp.arity);
    }

    let mut types = Vec::new();
    for texpr in type_exprs {
        match type_registry::resolve_type_expr(
            texpr,
            &type_param_map,
            &type_param_arity,
            registry,
            ResolutionContext::UserAnnotation,
            None,
        ) {
            Ok(ty) => types.push(ty),
            Err(_) => return None,
        }
    }
    Some(types)
}

pub(super) fn trait_method_param_types(
    trait_registry: &TraitRegistry,
    trait_name: &TraitName,
    method_name: &str,
) -> Option<Vec<Type>> {
    let info = trait_registry.lookup_trait(trait_name)?;
    let method = info.methods.iter().find(|m| m.name == method_name)?;
    Some(
        method
            .param_types
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect(),
    )
}

/// Phase 6: Check for trait method name conflicts and reserved name usage.
pub(super) fn check_trait_name_conflicts(
    module: &Module,
    trait_method_map: &FxHashMap<String, TraitName>,
    trait_registry: &TraitRegistry,
    trait_names: &TraitNameResolver,
    type_registry: &TypeRegistry,
    is_core_module: bool,
) -> Result<(), SpannedTypeError> {
    // Check for top-level def names conflicting with trait method names
    {
        let has_trait_usage = module
            .decls
            .iter()
            .any(|d| matches!(d, Decl::DefTrait { .. } | Decl::DefImpl { .. }))
            || module.decls.iter().any(|d| {
                if let Decl::DefType(td) = d {
                    !td.deriving.is_empty()
                } else {
                    false
                }
            });

        let mut user_trait_methods: FxHashMap<String, (String, Span)> = FxHashMap::default();
        for decl in &module.decls {
            if let Decl::DefTrait { name, methods, .. } = decl {
                for method in methods {
                    user_trait_methods.insert(method.name.clone(), (name.clone(), method.span));
                }
            }
        }
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if let Some((trait_name, method_span)) = user_trait_methods.get(&f.name) {
                    // Try overlap check: resolve free fn params and trait method params
                    let should_error = if let Some(fn_params) =
                        resolve_fn_param_types_for_overlap(f, type_registry)
                    {
                        if let Some(trait_info) = trait_names
                            .resolve(trait_name)
                            .and_then(|tn| trait_registry.lookup_trait(tn))
                        {
                            if let Some(method) =
                                trait_info.methods.iter().find(|m| m.name == f.name)
                            {
                                let method_params: Vec<Type> = method
                                    .param_types
                                    .iter()
                                    .map(|(_, ty)| ty.clone())
                                    .collect();
                                if fn_params.len() != method_params.len() {
                                    true // arity mismatch
                                } else {
                                    types_overlap(&fn_params, &method_params)
                                }
                            } else {
                                true
                            }
                        } else {
                            true
                        }
                    } else {
                        true // unannotated → can't prove non-overlap
                    };
                    if should_error {
                        return Err(SpannedTypeError {
                            error: Box::new(TypeError::DefinitionConflictsWithTraitMethod {
                                def_name: f.name.clone(),
                                trait_name: trait_name.clone(),
                            }),
                            span: f.span,
                            note: None,
                            secondary_span: Some(Box::new(crate::unify::SecondaryLabel {
                                span: *method_span,
                                message: "trait method defined here".into(),
                                source_file: None,
                            })),
                            source_file: None,
                            var_names: None,
                        });
                    }
                }
                if !user_trait_methods.contains_key(&f.name) && has_trait_usage {
                    if let Some(trait_id) = trait_method_map.get(&f.name) {
                        // Try overlap check for imported trait method
                        let should_error = if let Some(fn_params) =
                            resolve_fn_param_types_for_overlap(f, type_registry)
                        {
                            if let Some(method_params) =
                                trait_method_param_types(trait_registry, trait_id, &f.name)
                            {
                                if fn_params.len() != method_params.len() {
                                    true // arity mismatch
                                } else {
                                    types_overlap(&fn_params, &method_params)
                                }
                            } else {
                                true
                            }
                        } else {
                            true // unannotated → can't prove non-overlap
                        };
                        if should_error {
                            return Err(SpannedTypeError {
                                error: Box::new(TypeError::DefinitionConflictsWithTraitMethod {
                                    def_name: f.name.clone(),
                                    trait_name: trait_id.local_name.clone(),
                                }),
                                span: f.span,
                                note: None,
                                secondary_span: None,
                                source_file: None,
                                var_names: None,
                            });
                        }
                    }
                }
            }
        }
    }

    // Reject user-defined functions and trait methods with reserved names.
    // `__krypton_` is a hard-reserved prefix for runtime shims. `dictN`
    // (where N is one or more ASCII digits) collides with the synthetic
    // abstract methods the JVM backend emits on trait interfaces for each
    // direct superclass slot, so user code may not define a function or
    // trait method with that name either.
    fn is_reserved_name(name: &str) -> bool {
        if name.starts_with("__krypton_") {
            return true;
        }
        if let Some(rest) = name.strip_prefix("dict") {
            if !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()) {
                return true;
            }
        }
        false
    }
    if !is_core_module {
        for decl in &module.decls {
            match decl {
                Decl::DefFn(f) => {
                    if is_reserved_name(&f.name) {
                        return Err(spanned(
                            TypeError::ReservedName {
                                name: f.name.clone(),
                            },
                            f.span,
                        ));
                    }
                }
                Decl::DefTrait { methods, .. } => {
                    for method in methods {
                        if is_reserved_name(&method.name) {
                            return Err(spanned(
                                TypeError::ReservedName {
                                    name: method.name.clone(),
                                },
                                method.span,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    Ok(())
}
