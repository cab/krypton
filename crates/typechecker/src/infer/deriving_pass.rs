use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, Module, Span};

use crate::trait_registry::{InstanceInfo, TraitRegistry};
use crate::type_registry::TypeRegistry;
use crate::typed_ast::{self, InstanceDefInfo, ResolvedConstraint, TraitName};
use crate::types::{Type, TypeScheme, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::derive;
use super::helpers::{duplicate_instance_spanned, spanned};

pub(super) fn process_deriving(
    trait_registry: &mut TraitRegistry,
    module: &Module,
    registry: &TypeRegistry,
    module_path: &str,
) -> Result<Vec<InstanceDefInfo>, SpannedTypeError> {
    // Deriving pass
    let mut derived_instance_defs: Vec<InstanceDefInfo> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            if type_decl.deriving.is_empty() {
                continue;
            }
            let type_info = registry.lookup_type(&type_decl.name).unwrap();

            for trait_name in &type_decl.deriving {
                if trait_registry.lookup_trait_by_name(trait_name).is_none() {
                    return Err(spanned(
                        TypeError::UnknownTrait {
                            name: trait_name.clone(),
                        },
                        type_decl.span,
                    ));
                }

                let field_types: Vec<&Type> = match &type_info.kind {
                    crate::type_registry::TypeKind::Record { fields } => {
                        fields.iter().map(|(_, ty)| ty).collect()
                    }
                    crate::type_registry::TypeKind::Sum { variants } => {
                        variants.iter().flat_map(|v| v.fields.iter()).collect()
                    }
                };

                let derived_type_var_ids: HashMap<String, TypeVarId> = type_decl
                    .type_params
                    .iter()
                    .cloned()
                    .zip(type_info.type_param_vars.iter().copied())
                    .collect();
                let local_type_params: HashMap<TypeVarId, String> = derived_type_var_ids
                    .iter()
                    .map(|(name, id)| (*id, name.clone()))
                    .collect();
                let mut derived_constraints: Vec<ResolvedConstraint> = Vec::new();
                let mut visited_constraints: HashSet<(String, String)> = HashSet::new();

                for ft in &field_types {
                    // Disposable: only owned fields contribute constraints;
                    // plain fields are skipped entirely — the derived dispose
                    // body binds them but does nothing with them.
                    let check_ty: &Type = if trait_name == "Disposable" {
                        match ft {
                            Type::Own(inner) => inner.as_ref(),
                            _ => continue,
                        }
                    } else {
                        ft
                    };
                    if !derive::collect_derived_constraints_for_type(
                        trait_registry,
                        trait_name,
                        check_ty,
                        &local_type_params,
                        &type_decl.name,
                        &mut visited_constraints,
                        &mut derived_constraints,
                    ) {
                        return Err(spanned(
                            TypeError::CannotDerive {
                                trait_name: trait_name.clone(),
                                type_name: type_decl.name.clone(),
                                field_type: format!("{}", check_ty),
                            },
                            type_decl.span,
                        ));
                    }
                }

                let type_args: Vec<Type> = type_info
                    .type_param_vars
                    .iter()
                    .map(|&v| Type::Var(v))
                    .collect();
                let target_type = Type::Named(type_decl.name.clone(), type_args);
                let target_type_name = type_decl.name.clone();

                let method_name = match trait_name.as_str() {
                    "Eq" => "eq",
                    "Show" => "show",
                    "Hash" => "hash",
                    "Disposable" => "dispose",
                    _ => continue,
                };

                // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
                // Validation deferred to instance resolution phase.
                let derive_full_trait_name = trait_registry
                    .lookup_trait_by_name(trait_name)
                    .map(|ti| ti.trait_name())
                    .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));
                // A hand-written `impl Trait[T]` for the same (trait, type)
                // conflicts with the `deriving` clause. `register_impl_instances`
                // has already populated the instance table, so we can query it
                // directly — this uses the same unification-based equality as
                // `register_instance` and correctly handles `Own`/`Shape`
                // wrapper stripping and arity. The default error
                // (`DuplicateInstance` fired from `register_instance` below)
                // points at the impl's span and uses generic wording — emit
                // a targeted diagnostic at the `deriving` clause instead so
                // the user sees "remove the deriving or the impl".
                if trait_registry
                    .find_instance_multi(&derive_full_trait_name, &[target_type.clone()])
                    .is_some()
                {
                    return Err(spanned(
                        TypeError::DerivingConflictsWithImpl {
                            trait_name: trait_name.clone(),
                            type_name: type_decl.name.clone(),
                        },
                        type_decl.span,
                    ));
                }

                let instance = InstanceInfo {
                    trait_name: derive_full_trait_name.clone(),
                    target_types: vec![target_type.clone()],
                    target_type_name: target_type_name.clone(),
                    type_var_ids: derived_type_var_ids.clone(),
                    constraints: derived_constraints.clone(),
                    span: type_decl.span,
                    is_builtin: false,
                };
                trait_registry
                    .register_instance(instance)
                    .map_err(|boxed| {
                        let (e, existing_span) = *boxed;
                        duplicate_instance_spanned(e, type_decl.span, existing_span)
                    })?;

                let syn_span: Span = (0, 0);
                let trait_id_for_synth = Some(derive_full_trait_name.clone());
                let (body, fn_ty) = match trait_name.as_str() {
                    "Eq" => derive::synthesize_eq_body(type_info, &target_type, syn_span),
                    "Show" => derive::synthesize_show_body(
                        type_info,
                        &target_type,
                        syn_span,
                        trait_id_for_synth.clone(),
                    ),
                    "Hash" => derive::synthesize_hash_body(
                        type_info,
                        &target_type,
                        syn_span,
                        trait_id_for_synth.clone(),
                    ),
                    "Disposable" => derive::synthesize_dispose_body(
                        type_info,
                        &target_type,
                        syn_span,
                        trait_id_for_synth.clone(),
                    ),
                    _ => continue,
                };

                let mk_param = |n: &str| crate::typed_ast::TypedParam {
                    name: n.to_string(),
                    mode: crate::types::ParamMode::Consume,
                };
                let params: Vec<crate::typed_ast::TypedParam> = match trait_name.as_str() {
                    "Eq" => vec![mk_param("__a"), mk_param("__b")],
                    "Show" | "Hash" | "Disposable" => vec![mk_param("__a")],
                    _ => vec![],
                };

                let scheme = TypeScheme {
                    vars: vec![],
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };

                derived_instance_defs.push(InstanceDefInfo {
                    trait_name: derive_full_trait_name.clone(),
                    target_type_name,
                    target_types: vec![target_type],
                    type_var_ids: derived_type_var_ids.clone(),
                    constraints: derived_constraints.clone(),
                    methods: vec![typed_ast::InstanceMethod {
                        name: method_name.to_string(),
                        params,
                        body,
                        scheme,
                        constraint_pairs: vec![],
                    }],
                    is_intrinsic: false,
                });
            }
        }

        // Extern type deriving
        if let Decl::Extern {
            alias: Some(name),
            deriving,
            is_trait: false,
            span,
            ..
        } = decl
        {
            for trait_name in deriving {
                if trait_name != "Disposable" {
                    return Err(spanned(
                        TypeError::CannotDerive {
                            trait_name: trait_name.clone(),
                            type_name: name.clone(),
                            field_type: name.clone(),
                        },
                        *span,
                    ));
                }

                let type_info = registry.lookup_type(name).unwrap();
                let type_args: Vec<Type> = type_info
                    .type_param_vars
                    .iter()
                    .map(|&v| Type::Var(v))
                    .collect();
                let target_type = Type::Named(name.clone(), type_args);

                let derive_full_trait_name = trait_registry
                    .lookup_trait_by_name(trait_name)
                    .map(|ti| ti.trait_name())
                    .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));

                if trait_registry
                    .find_instance_multi(&derive_full_trait_name, &[target_type.clone()])
                    .is_some()
                {
                    return Err(spanned(
                        TypeError::DerivingConflictsWithImpl {
                            trait_name: trait_name.clone(),
                            type_name: name.clone(),
                        },
                        *span,
                    ));
                }

                let instance = InstanceInfo {
                    trait_name: derive_full_trait_name.clone(),
                    target_types: vec![target_type.clone()],
                    target_type_name: name.clone(),
                    type_var_ids: HashMap::new(),
                    constraints: vec![],
                    span: *span,
                    is_builtin: false,
                };
                trait_registry
                    .register_instance(instance)
                    .map_err(|boxed| {
                        let (e, existing_span) = *boxed;
                        duplicate_instance_spanned(e, *span, existing_span)
                    })?;

                let syn_span: Span = (0, 0);
                let (body, fn_ty) =
                    derive::synthesize_extern_dispose_body(&target_type, syn_span);

                let mk_param = |n: &str| crate::typed_ast::TypedParam {
                    name: n.to_string(),
                    mode: crate::types::ParamMode::Consume,
                };

                let scheme = TypeScheme {
                    vars: vec![],
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };

                derived_instance_defs.push(InstanceDefInfo {
                    trait_name: derive_full_trait_name,
                    target_type_name: name.clone(),
                    target_types: vec![target_type],
                    type_var_ids: HashMap::new(),
                    constraints: vec![],
                    methods: vec![typed_ast::InstanceMethod {
                        name: "dispose".to_string(),
                        params: vec![mk_param("__a")],
                        body,
                        scheme,
                        constraint_pairs: vec![],
                    }],
                    is_intrinsic: false,
                });
            }
        }
    }
    Ok(derived_instance_defs)
}
