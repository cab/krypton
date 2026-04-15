use std::collections::HashMap;

use krypton_parser::ast::{Decl, ExternMethod, ExternTarget, Module, Span, Visibility};

use crate::type_registry::{self, ResolutionContext, TypeRegistry};
use crate::typed_ast::{ExternFnInfo, ExternTypeInfo, TraitName};
use crate::types::{Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::display::build_type_param_map;
use super::helpers::{require_param_vars, spanned};
use super::state::ModuleInferenceState;

/// Result of processing a module's local extern declarations.
pub(crate) type LocalExternResult = (
    Vec<ExternFnInfo>,
    Vec<ExternTypeInfo>,
    Vec<ExternBindingInfo>,
    HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
    Vec<PendingExternTrait>,
);

/// Result of processing extern methods: function info for codegen + dict requirements.
pub(crate) struct ExternMethodsResult {
    pub(crate) extern_fns: Vec<ExternFnInfo>,
    pub(crate) bindings: Vec<ExternBindingInfo>,
    /// Dict requirements for extern functions with `where` clauses.
    pub(crate) fn_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
}

#[derive(Clone)]
pub(crate) struct ExternBindingInfo {
    pub(crate) name: String,
    pub(crate) scheme: TypeScheme,
    pub(crate) visibility: Visibility,
    pub(crate) def_span: Span,
}

/// Extern trait declaration collected during extern processing,
/// to be registered as a real trait in the trait registration phase.
pub(crate) struct PendingExternTrait {
    pub(crate) name: String,
    pub(crate) java_interface: String,
    pub(crate) type_params: Vec<String>,
    pub(crate) methods: Vec<ExternMethod>,
    pub(crate) span: Span,
}

/// Process extern methods from an `extern "class" { ... }` block, binding their
/// types into the environment and returning `ExternFnInfo` entries for codegen.
// Extern method processing — each arg reflects a distinct lexical input from
// the surface `extern` declaration (target language, env, gen, registry, trait
// lookup, type-param map/arity/names, alias). Bundling them into a struct
// would just be a namespace shim, since this is only called from a couple of
// extern-loading sites and shares no fields with anything else.
#[allow(clippy::too_many_arguments)]
pub(crate) fn process_extern_methods(
    class_name: &str,
    target: &ExternTarget,
    methods: &[ExternMethod],
    env: &mut TypeEnv,
    gen: &mut TypeVarGen,
    registry: &TypeRegistry,
    trait_name_lookup: &HashMap<String, TraitName>,
    module_path_str: &str,
    span: Span,
    type_param_map: Option<&HashMap<String, TypeVarId>>,
    type_param_arity: Option<&HashMap<String, usize>>,
    type_param_names: Option<&[String]>,
    alias_name: Option<&str>,
) -> Result<ExternMethodsResult, SpannedTypeError> {
    let empty_map = HashMap::new();
    let empty_arity = HashMap::new();
    let resolve_map = type_param_map.unwrap_or(&empty_map);
    let resolve_arity = type_param_arity.unwrap_or(&empty_arity);
    // Collect type param vars for scheme quantification in declaration order
    let base_scheme_vars: Vec<TypeVarId> = match (type_param_names, type_param_map) {
        (Some(names), Some(map)) => names.iter().filter_map(|n| map.get(n).copied()).collect(),
        _ => vec![],
    };
    let mut extern_fns = Vec::new();
    let mut bindings = Vec::new();
    let mut fn_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> = HashMap::new();
    for method in methods {
        let bind_name = &method.name;

        let mut scheme_vars = base_scheme_vars.clone();

        // Build method-level type param map (merged with block-level)
        let mut method_resolve_map;
        let mut method_resolve_arity;
        let effective_resolve_map: &HashMap<String, TypeVarId>;
        let effective_resolve_arity: &HashMap<String, usize>;
        if !method.type_params.is_empty() {
            method_resolve_map = resolve_map.clone();
            method_resolve_arity = resolve_arity.clone();
            for tp_name in &method.type_params {
                let fresh = gen.fresh();
                method_resolve_map.insert(tp_name.clone(), fresh);
                method_resolve_arity.insert(tp_name.clone(), 0);
                scheme_vars.push(fresh);
            }
            effective_resolve_map = &method_resolve_map;
            effective_resolve_arity = &method_resolve_arity;
        } else {
            effective_resolve_map = resolve_map;
            effective_resolve_arity = resolve_arity;
        }

        let mut param_types = Vec::new();
        for (_, ty_expr) in &method.params {
            let resolved = type_registry::resolve_type_expr(
                ty_expr,
                effective_resolve_map,
                effective_resolve_arity,
                registry,
                ResolutionContext::UserAnnotation,
                None,
            )
            .map_err(|e| spanned(e, span))?;
            param_types.push(resolved);
        }

        let return_type = type_registry::resolve_type_expr(
            &method.return_type,
            effective_resolve_map,
            effective_resolve_arity,
            registry,
            ResolutionContext::UserAnnotation,
            None,
        )
        .map_err(|e| spanned(e, span))?;
        let ret = return_type.clone();

        // Validate @nullable: return type must be Option[T]
        if method.nullable {
            let is_option = matches!(&ret, Type::Named(n, _) if n == "Option");
            if !is_option {
                return Err(spanned(
                    TypeError::InvalidNullableReturn {
                        name: bind_name.clone(),
                        actual_return_type: ret.clone(),
                    },
                    method.span,
                ));
            }
        }

        // Validate @throws: return type must be Result[String, T]
        if method.throws {
            let is_result_string = matches!(&ret, Type::Named(n, args) if n == "Result" && args.len() == 2 && args[0] == Type::String);
            if !is_result_string {
                return Err(spanned(
                    TypeError::InvalidThrowsReturn {
                        name: bind_name.clone(),
                        actual_return_type: ret.clone(),
                    },
                    method.span,
                ));
            }
        }

        // Validate @instance / @constructor
        if method.instance && method.constructor {
            return Err(spanned(
                TypeError::InstanceConstructorConflict {
                    name: bind_name.clone(),
                },
                method.span,
            ));
        }

        if (method.instance || method.constructor) && matches!(target, ExternTarget::Js) {
            return Err(spanned(
                TypeError::InstanceConstructorOnJsTarget {
                    name: bind_name.clone(),
                },
                method.span,
            ));
        }

        if method.constructor {
            if let Some(alias) = alias_name {
                // Return type must be Own(Named(alias, _)), possibly wrapped in
                // Result[String, _] for @throws or Option[_] for @nullable.
                let inner_ret = if method.throws {
                    // Result[String, ~Alias] → check the second type arg
                    match &ret {
                        Type::Named(n, args) if n == "Result" && args.len() == 2 => &args[1],
                        _ => &ret,
                    }
                } else if method.nullable {
                    // Option[~Alias] → check the inner type
                    match &ret {
                        Type::Named(n, args) if n == "Option" && args.len() == 1 => &args[0],
                        _ => &ret,
                    }
                } else {
                    &ret
                };
                let is_own_alias = matches!(inner_ret, Type::Own(inner) if matches!(inner.as_ref(), Type::Named(n, _) if n == alias));
                if !is_own_alias {
                    return Err(spanned(
                        TypeError::InvalidConstructorReturn {
                            name: bind_name.clone(),
                            expected_type: alias.to_string(),
                            actual_return_type: ret.clone(),
                        },
                        method.span,
                    ));
                }
                // First param must NOT be the extern type
                if let Some((_, _first_ty)) = method.params.first() {
                    let first_resolved = &param_types[0];
                    let matches_alias = matches!(first_resolved, Type::Named(n, _) if n == alias)
                        || matches!(first_resolved, Type::Own(inner) if matches!(inner.as_ref(), Type::Named(n, _) if n == alias));
                    if matches_alias {
                        return Err(spanned(
                            TypeError::ConstructorWithSelf {
                                name: bind_name.clone(),
                            },
                            method.span,
                        ));
                    }
                }
            }
        }

        if method.instance {
            if let Some(alias) = alias_name {
                // First param must be the extern type
                let first_matches = if let Some(first_resolved) = param_types.first() {
                    matches!(first_resolved, Type::Named(n, _) if n == alias)
                        || matches!(first_resolved, Type::Own(inner) if matches!(inner.as_ref(), Type::Named(n, _) if n == alias))
                } else {
                    false
                };
                if !first_matches {
                    return Err(spanned(
                        TypeError::InvalidInstanceFirstParam {
                            name: bind_name.clone(),
                            expected_type: alias.to_string(),
                        },
                        method.span,
                    ));
                }
            }
        }

        // Build where clause dict requirements before TypeScheme construction
        // so constraints are embedded in the scheme.
        let mut requirements = Vec::new();
        if !method.where_clauses.is_empty() {
            for constraint in &method.where_clauses {
                let tv_names = require_param_vars(constraint)?;
                let type_vars: Vec<TypeVarId> = tv_names
                    .iter()
                    .filter_map(|n| effective_resolve_map.get(*n).copied())
                    .collect();
                if !type_vars.is_empty() && type_vars.len() == tv_names.len() {
                    let tn = trait_name_lookup
                        .get(&constraint.trait_name)
                        .cloned()
                        .unwrap_or_else(|| {
                            TraitName::new(
                                module_path_str.to_string(),
                                constraint.trait_name.clone(),
                            )
                        });
                    requirements.push((tn, type_vars));
                }
            }
            if !requirements.is_empty() {
                fn_constraints.insert(bind_name.clone(), requirements.clone());
            }
        }

        let fn_ty = Type::fn_consuming(param_types.clone(), ret);
        let scheme = if scheme_vars.is_empty() {
            TypeScheme::mono(fn_ty)
        } else {
            TypeScheme {
                vars: scheme_vars,
                constraints: requirements.clone(),
                ty: fn_ty,
                var_names: HashMap::new(),
            }
        };
        env.bind_top_level_function(
            bind_name.clone(),
            scheme.clone(),
            module_path_str.to_string(),
            bind_name.clone(),
        );
        bindings.push(ExternBindingInfo {
            name: bind_name.clone(),
            scheme,
            visibility: method.visibility,
            def_span: method.span,
        });

        // Store concrete types for codegen — resolve with the type param map
        // so container types like Vec[a] resolve to Named("Vec", [Var(a)])
        // rather than being erased entirely to a bare Var. The type args
        // (which map to Var) will be erased to Object by JVM codegen, matching
        // Java's own type erasure behavior.
        let mut concrete_params = Vec::new();
        for (_, ty_expr) in &method.params {
            let resolved = type_registry::resolve_type_expr(
                ty_expr,
                effective_resolve_map,
                effective_resolve_arity,
                registry,
                ResolutionContext::UserAnnotation,
                None,
            )
            .map_err(|e| spanned(e, span))?;
            concrete_params.push(resolved);
        }
        let codegen_return = type_registry::resolve_type_expr(
            &method.return_type,
            effective_resolve_map,
            effective_resolve_arity,
            registry,
            ResolutionContext::UserAnnotation,
            None,
        )
        .map_err(|e| spanned(e, span))?;
        extern_fns.push(ExternFnInfo {
            name: bind_name.clone(),
            declaring_module_path: module_path_str.to_string(),
            span: method.span,
            module_path: class_name.to_string(),
            target: target.clone(),
            nullable: method.nullable,
            throws: method.throws,
            instance: method.instance,
            constructor: method.constructor,
            param_types: concrete_params,
            return_type: codegen_return,
            constraints: requirements,
        });
    }
    Ok(ExternMethodsResult {
        extern_fns,
        bindings,
        fn_constraints,
    })
}

impl ModuleInferenceState {
    pub(super) fn process_local_externs(
        &mut self,
        module: &Module,
        mod_path: &str,
    ) -> Result<LocalExternResult, SpannedTypeError> {
        let mut extern_fns: Vec<ExternFnInfo> = Vec::new();
        let mut extern_types: Vec<ExternTypeInfo> = Vec::new();
        let mut extern_bindings: Vec<ExternBindingInfo> = Vec::new();
        let mut extern_fn_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> =
            HashMap::new();
        let mut pending_extern_traits: Vec<PendingExternTrait> = Vec::new();

        // Build trait name lookup from imported trait defs
        let mut trait_name_lookup: HashMap<String, TraitName> = HashMap::new();
        for td in &self.imported_trait_defs {
            trait_name_lookup.insert(
                td.name.clone(),
                TraitName::new(td.module_path.clone(), td.name.clone()),
            );
        }

        for decl in &module.decls {
            if let Decl::Extern {
                target,
                module_path,
                alias,
                is_trait,
                type_params,
                lifts,
                methods,
                span,
                ..
            } = decl
            {
                // Extern traits are collected for registration in the trait phase
                if *is_trait {
                    if matches!(target, ExternTarget::Js) {
                        return Err(spanned(
                            TypeError::ExternTraitOnJsTarget {
                                name: alias.clone().unwrap_or_default(),
                            },
                            *span,
                        ));
                    }
                    if let Some(name) = alias {
                        pending_extern_traits.push(PendingExternTrait {
                            name: name.clone(),
                            java_interface: module_path.clone(),
                            type_params: type_params.clone(),
                            methods: methods.clone(),
                            span: *span,
                        });
                    }
                    continue;
                }

                // Register type binding if `as Name[params]` is present
                let mut tp_map: Option<HashMap<String, TypeVarId>> = None;
                let mut tp_arity: Option<HashMap<String, usize>> = None;
                if let Some(name) = alias {
                    // Check if already registered (e.g. Vec is a builtin)
                    let type_param_vars = if let Some(existing) = self.registry.lookup_type(name) {
                        existing.type_param_vars.clone()
                    } else {
                        let vars: Vec<_> = type_params.iter().map(|_| self.gen.fresh()).collect();
                        self.registry
                            .register_type(crate::type_registry::TypeInfo {
                                name: name.clone(),
                                type_params: type_params.clone(),
                                type_param_vars: vars.clone(),
                                kind: crate::type_registry::TypeKind::Record { fields: vec![] },
                                lifts: lifts.clone(),
                                is_prelude: false,
                            })
                            .map_err(|e| spanned(e, *span))?;
                        vars
                    };
                    self.registry.mark_user_visible(name);
                    extern_types.push(ExternTypeInfo {
                        krypton_name: name.clone(),
                        host_module: module_path.clone(),
                        target: target.clone(),
                        lifts: lifts.clone(),
                    });

                    // Build type_param_map for method resolution
                    if !type_params.is_empty() {
                        let (map, arity) =
                            build_type_param_map(type_params, &type_param_vars, name);
                        tp_map = Some(map);
                        tp_arity = Some(arity);
                    }
                }

                {
                    let tp_names = type_params.as_slice();
                    let result = process_extern_methods(
                        module_path,
                        target,
                        methods,
                        &mut self.env,
                        &mut self.gen,
                        &self.registry,
                        &trait_name_lookup,
                        mod_path,
                        *span,
                        tp_map.as_ref(),
                        tp_arity.as_ref(),
                        if tp_map.is_some() {
                            Some(tp_names)
                        } else {
                            None
                        },
                        alias.as_deref(),
                    )?;

                    for (name, reqs) in result.fn_constraints {
                        extern_fn_constraints.insert(name, reqs);
                    }
                    extern_bindings.extend(result.bindings);
                    extern_fns.extend(result.extern_fns);
                }
            }
        }
        Ok((
            extern_fns,
            extern_types,
            extern_bindings,
            extern_fn_constraints,
            pending_extern_traits,
        ))
    }
}
