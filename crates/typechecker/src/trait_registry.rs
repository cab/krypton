use std::collections::HashMap;

use krypton_parser::ast::Span;

use crate::types::{Substitution, Type, TypeVarGen, TypeVarId};
use crate::unify::{unify, TypeError};

use crate::typed_ast::{ResolvedConstraint, TraitName};

/// Result of a partial multi-parameter instance lookup.
pub enum PartialMatch<'a> {
    Unique(&'a InstanceInfo),
    Multiple,
    None_,
}

pub struct TraitInfo {
    pub name: String,
    pub module_path: String,
    pub type_var: String,
    pub type_var_id: TypeVarId,
    /// All trait type parameter ids in declaration order (`type_var_ids[0] == type_var_id`).
    /// For single-parameter traits this has length 1; for multi-parameter traits like
    /// `trait Convert[a, b]` it carries `[a_id, b_id]`. Used by the multi-param
    /// resolution pass to freshen and unify all trait params at call sites.
    pub type_var_ids: Vec<TypeVarId>,
    /// Names of all trait type parameters in declaration order, parallel to `type_var_ids`.
    pub type_var_names: Vec<String>,
    /// 0 = kind *, 1 = * -> *, 2 = * -> * -> *, etc.
    pub type_var_arity: usize,
    pub superclasses: Vec<TraitName>,
    pub methods: Vec<TraitMethod>,
    pub span: Span,
    /// True if this trait was imported from the prelude.
    pub is_prelude: bool,
}

impl TraitInfo {
    /// Build a `TraitName` from this trait's module_path and name.
    pub fn trait_name(&self) -> TraitName {
        TraitName::new(self.module_path.clone(), self.name.clone())
    }
}

pub struct TraitMethod {
    pub name: String,
    pub param_types: Vec<(crate::types::ParamMode, Type)>,
    pub return_type: Type,
    /// Constraints on the method's own type parameters (not the trait's type param).
    /// e.g., `fun traverse[b](x: f[a]) -> f[b] where b: Default` stores `[(Default, TypeVarId_for_b)]`
    pub constraints: Vec<(TraitName, Vec<TypeVarId>)>,
}

pub struct InstanceInfo {
    pub trait_name: TraitName,
    /// Type arguments of the instance. Length 1 for single-parameter traits,
    /// N for multi-parameter traits like `impl Convert[Int, String]`.
    pub target_types: Vec<Type>,
    /// Display form, joining multiple arguments with ", " for multi-param traits.
    pub target_type_name: String,
    pub type_var_ids: HashMap<String, TypeVarId>,
    pub constraints: Vec<ResolvedConstraint>,
    pub span: Span,
    pub is_builtin: bool,
}

pub struct TraitRegistry {
    traits: HashMap<TraitName, TraitInfo>,
    /// Secondary index: bare trait name → TraitName, for O(1) lookup_trait_by_name.
    bare_name_index: HashMap<String, TraitName>,
    instances: Vec<InstanceInfo>,
    /// Index: trait_name → indices into `instances`, for fast overlap/lookup.
    instances_by_trait: HashMap<TraitName, Vec<usize>>,
    trait_aliases: HashMap<String, TraitName>,
}

impl Default for TraitRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl TraitRegistry {
    pub fn new() -> Self {
        TraitRegistry {
            traits: HashMap::new(),
            bare_name_index: HashMap::new(),
            instances: Vec::new(),
            instances_by_trait: HashMap::new(),
            trait_aliases: HashMap::new(),
        }
    }

    pub fn register_trait(&mut self, info: TraitInfo) -> Result<(), TypeError> {
        let key = info.trait_name();
        if self.traits.contains_key(&key) {
            return Err(TypeError::OrphanInstance {
                trait_name: info.name.clone(),
                ty: info.name.clone(),
                modules_checked: vec![],
            });
        }
        // Check bare-name collision with a trait from a different module
        if let Some(existing_key) = self.bare_name_index.get(&info.name) {
            if *existing_key != key {
                let existing = &self.traits[existing_key];
                return Err(TypeError::AmbiguousTraitName {
                    name: info.name.clone(),
                    existing_module: existing.module_path.clone(),
                    new_module: info.module_path.clone(),
                });
            }
        }
        self.bare_name_index.insert(info.name.clone(), key.clone());
        self.traits.insert(key, info);
        Ok(())
    }

    pub fn register_instance(&mut self, info: InstanceInfo) -> Result<(), Box<(TypeError, Span)>> {
        // Check for overlapping (trait, type tuple) pairs via positionwise unification
        // (only same-trait instances)
        let trait_indices = self
            .instances_by_trait
            .get(&info.trait_name)
            .cloned()
            .unwrap_or_default();
        for &idx in &trait_indices {
            let existing = &self.instances[idx];
            if instances_overlap(&existing.target_types, &info.target_types) {
                let names: std::collections::HashMap<crate::types::TypeVarId, &str> = info
                    .type_var_ids
                    .iter()
                    .map(|(name, &id)| (id, name.as_str()))
                    .collect();
                let existing_names: std::collections::HashMap<crate::types::TypeVarId, &str> =
                    existing
                        .type_var_ids
                        .iter()
                        .map(|(name, &id)| (id, name.as_str()))
                        .collect();
                return Err(Box::new((
                    TypeError::DuplicateInstance {
                        trait_name: info.trait_name.local_name.clone(),
                        ty: format_type_tuple_with_var_map(&info.target_types, &names),
                        existing_ty: format_type_tuple_with_var_map(
                            &existing.target_types,
                            &existing_names,
                        ),
                    },
                    existing.span,
                )));
            }
        }
        let idx = self.instances.len();
        self.instances_by_trait
            .entry(info.trait_name.clone())
            .or_default()
            .push(idx);
        self.instances.push(info);
        Ok(())
    }

    pub fn lookup_trait(&self, name: &TraitName) -> Option<&TraitInfo> {
        self.traits.get(name)
    }

    /// Look up a trait by bare name. Also checks trait aliases as a fallback.
    pub fn lookup_trait_by_name(&self, name: &str) -> Option<&TraitInfo> {
        self.bare_name_index
            .get(name)
            .and_then(|tn| self.traits.get(tn))
            .or_else(|| {
                self.trait_aliases
                    .get(name)
                    .and_then(|tn| self.traits.get(tn))
            })
    }

    pub fn find_instance(&self, trait_name: &TraitName, ty: &Type) -> Option<&InstanceInfo> {
        debug_assert!(
            self.lookup_trait(trait_name)
                .map(|t| t.type_var_arity <= 1 && t.type_var_ids.len() <= 1)
                .unwrap_or(true),
            "find_instance called with single type on multi-parameter trait {}; \
             callers with a tuple must use find_instance_for",
            trait_name.local_name
        );
        let mut resolution_stack = Vec::new();
        self.find_instance_inner(trait_name, std::slice::from_ref(ty), &mut resolution_stack)
    }

    /// Canonical multi-arg entry point for instance lookup.
    ///
    /// Accepts the full tuple of trait type arguments. For single-parameter
    /// traits, pass a 1-element slice (equivalent to `find_instance`).
    pub fn find_instance_for(&self, trait_name: &TraitName, tys: &[Type]) -> Option<&InstanceInfo> {
        let mut resolution_stack = Vec::new();
        self.find_instance_inner(trait_name, tys, &mut resolution_stack)
    }

    /// Partial-match lookup for multi-parameter trait instances.
    ///
    /// Unlike `find_instance_multi` which requires every position to match concretely,
    /// this allows positions whose resolved type is `Type::Var(_)` to act as wildcards.
    /// Returns `Unique` only when exactly one instance passes; `Multiple` if more than
    /// one passes; `None_` if zero pass. Where-clause constraints on candidate instances
    /// are only enforced when *all* positions in the query are concrete — otherwise the
    /// candidate is left "potentially valid" for a later resolver pass.
    pub fn find_instance_multi_partial(
        &self,
        trait_name: &TraitName,
        tys: &[Type],
    ) -> PartialMatch<'_> {
        let Some(indices) = self.instances_by_trait.get(trait_name) else {
            return PartialMatch::None_;
        };
        let all_concrete = tys.iter().all(|t| !contains_type_var(t));
        let mut found: Option<&InstanceInfo> = None;
        for &idx in indices {
            let inst = &self.instances[idx];
            if inst.target_types.len() != tys.len() {
                continue;
            }
            let mut bindings = HashMap::new();
            let positions_match =
                inst.target_types
                    .iter()
                    .zip(tys.iter())
                    .all(|(pattern, actual)| {
                        // Wildcard: actual is a free type var → matches anything
                        if matches!(actual, Type::Var(_)) {
                            return true;
                        }
                        types_match_with_bindings(pattern, actual, &mut bindings)
                    });
            if !positions_match {
                continue;
            }
            // Where-clause constraints only enforced when all positions are concrete.
            if all_concrete && !inst.constraints.is_empty() {
                let constraints_ok = inst.constraints.iter().all(|c| {
                    let bound_tys: Option<Vec<Type>> = c
                        .type_vars
                        .iter()
                        .map(|name| {
                            let id = inst.type_var_ids.get(name)?;
                            bindings.get(id).cloned()
                        })
                        .collect();
                    let Some(bound_tys) = bound_tys else {
                        return false;
                    };
                    self.find_instance_multi(&c.trait_name, &bound_tys)
                        .is_some()
                });
                if !constraints_ok {
                    continue;
                }
            }
            if found.is_some() {
                return PartialMatch::Multiple;
            }
            found = Some(inst);
        }
        match found {
            Some(inst) => PartialMatch::Unique(inst),
            None => PartialMatch::None_,
        }
    }

    /// Look up an instance by trait name and a tuple of type arguments.
    ///
    /// This is the multi-parameter analogue of `find_instance`. Matching is
    /// positionwise using a shared bindings map, so type variables consistently
    /// resolve across all positions. For single-parameter traits, passing a
    /// 1-element slice is equivalent to `find_instance`.
    pub fn find_instance_multi(
        &self,
        trait_name: &TraitName,
        tys: &[Type],
    ) -> Option<&InstanceInfo> {
        let indices = self.instances_by_trait.get(trait_name)?;
        indices.iter().map(|&i| &self.instances[i]).find(|inst| {
            if inst.target_types.len() != tys.len() {
                return false;
            }
            let mut bindings = HashMap::new();
            inst.target_types
                .iter()
                .zip(tys.iter())
                .all(|(pattern, actual)| types_match_with_bindings(pattern, actual, &mut bindings))
        })
    }

    fn find_instance_inner<'a>(
        &'a self,
        trait_name: &TraitName,
        target_tys: &[Type],
        resolution_stack: &mut Vec<(TraitName, String)>,
    ) -> Option<&'a InstanceInfo> {
        let key_ty = target_tys
            .iter()
            .map(|t| format!("{t}"))
            .collect::<Vec<_>>()
            .join(", ");
        let key = (trait_name.clone(), key_ty);
        if resolution_stack.contains(&key) {
            return None;
        }

        // For HK traits (arity > 0), match by extracting the outermost type constructor.
        // HK matching only inspects position 0 — higher-kinded multi-param traits are
        // not yet expressible in the language, so `target_tys[1..]` go through the
        // regular zip path below.
        let trait_info = self.lookup_trait(trait_name);
        if let Some(info) = trait_info {
            if info.type_var_arity > 0 {
                let primary = target_tys.first()?;
                resolution_stack.push(key);
                let indices = self.instances_by_trait.get(trait_name);
                let matched = indices.and_then(|idxs| {
                    idxs.iter().map(|&i| &self.instances[i]).find(|inst| {
                        if inst.target_types.len() != target_tys.len() {
                            return false;
                        }
                        let Some(inst_primary) = inst.target_types.first() else {
                            return false;
                        };
                        let Some((actual_ctor, actual_bound_args)) =
                            split_type_constructor(primary)
                        else {
                            return false;
                        };
                        let Some((inst_ctor, inst_bound_args)) =
                            split_instance_type_constructor(inst_primary)
                        else {
                            return false;
                        };

                        let actual_len = actual_bound_args.len();
                        let inst_len = inst_bound_args.len();
                        if actual_ctor != inst_ctor
                            || (actual_len != inst_len
                                && actual_len != inst_len + info.type_var_arity)
                        {
                            return false;
                        }

                        let mut bindings = HashMap::new();
                        if !inst_bound_args.iter().zip(actual_bound_args.iter()).all(
                            |(pattern_arg, actual_arg)| {
                                types_match_with_bindings(pattern_arg, actual_arg, &mut bindings)
                            },
                        ) {
                            return false;
                        }

                        // Zip remaining (non-HK) positions in lockstep.
                        for (pattern, actual) in
                            inst.target_types.iter().zip(target_tys.iter()).skip(1)
                        {
                            if !types_match_with_bindings(pattern, actual, &mut bindings) {
                                return false;
                            }
                        }

                        let bound = &actual_bound_args[..inst_len];
                        let ctor_binding = reconstruct_ctor_type(&actual_ctor, bound);

                        inst.constraints.iter().all(|constraint| {
                            let bound_tys: Option<Vec<Type>> = constraint
                                .type_vars
                                .iter()
                                .map(|name| {
                                    let id = inst.type_var_ids.get(name)?;
                                    Some(
                                        bindings
                                            .get(id)
                                            .cloned()
                                            .unwrap_or_else(|| ctor_binding.clone()),
                                    )
                                })
                                .collect();
                            let Some(bound_tys) = bound_tys else {
                                return false;
                            };
                            self.find_instance_inner(
                                &constraint.trait_name,
                                &bound_tys,
                                resolution_stack,
                            )
                            .is_some()
                        })
                    })
                });
                resolution_stack.pop();
                return matched;
            }
        }

        resolution_stack.push(key);
        let indices = self.instances_by_trait.get(trait_name);
        let matched = indices.and_then(|idxs| {
            idxs.iter().map(|&i| &self.instances[i]).find(|inst| {
                if inst.target_types.len() != target_tys.len() {
                    return false;
                }
                let mut bindings = HashMap::new();
                for (pattern, actual) in inst.target_types.iter().zip(target_tys.iter()) {
                    if !types_match_with_bindings(pattern, actual, &mut bindings) {
                        return false;
                    }
                }

                inst.constraints.iter().all(|constraint| {
                    let bound_tys: Option<Vec<Type>> = constraint
                        .type_vars
                        .iter()
                        .map(|name| {
                            let id = inst.type_var_ids.get(name)?;
                            bindings.get(id).cloned()
                        })
                        .collect();
                    let Some(bound_tys) = bound_tys else {
                        return false;
                    };
                    self.find_instance_inner(&constraint.trait_name, &bound_tys, resolution_stack)
                        .is_some()
                })
            })
        });
        resolution_stack.pop();
        matched
    }

    pub fn check_superclasses(&self, instance: &InstanceInfo) -> Result<(), TypeError> {
        let trait_info = match self.lookup_trait(&instance.trait_name) {
            Some(t) => t,
            None => return Ok(()),
        };
        debug_assert!(
            instance.target_types.len() == 1 || trait_info.superclasses.is_empty(),
            "multi-parameter traits with superclasses are not supported yet (M30-T5)"
        );
        for superclass in &trait_info.superclasses {
            if self
                .find_instance_for(superclass, &instance.target_types)
                .is_none()
            {
                return Err(TypeError::NoInstance {
                    trait_name: superclass.local_name.clone(),
                    ty: instance.target_type_name.clone(),
                    required_by: Some(instance.trait_name.local_name.clone()),
                });
            }
        }
        Ok(())
    }

    pub fn find_instance_by_trait_and_span(
        &self,
        trait_name: &TraitName,
        span: Span,
    ) -> Option<&InstanceInfo> {
        self.instances_by_trait.get(trait_name).and_then(|idxs| {
            idxs.iter()
                .map(|&i| &self.instances[i])
                .find(|inst| inst.span == span)
        })
    }

    pub fn trait_method_names(&self) -> Vec<(String, TraitName, bool)> {
        let mut result = Vec::new();
        for (trait_id, info) in &self.traits {
            for method in &info.methods {
                result.push((method.name.clone(), trait_id.clone(), info.is_prelude));
            }
        }
        result
    }

    pub fn register_trait_alias(&mut self, alias: String, canonical: TraitName) {
        self.trait_aliases.insert(alias, canonical);
    }

    pub fn traits(&self) -> &HashMap<TraitName, TraitInfo> {
        &self.traits
    }

    pub fn instances(&self) -> &[InstanceInfo] {
        &self.instances
    }

    /// When `find_instance` returns None, explain why by finding instances that
    /// structurally match but have failing `where` constraints.
    /// Called only on the error path — zero impact on the happy path.
    pub fn diagnose_missing_instance(
        &self,
        trait_name: &TraitName,
        ty: &Type,
    ) -> Option<InstanceDiagnostic> {
        let trait_info = self.lookup_trait(trait_name);

        let empty_indices = Vec::new();
        let trait_indices = self
            .instances_by_trait
            .get(trait_name)
            .unwrap_or(&empty_indices);

        // HK trait path (arity > 0)
        if let Some(info) = trait_info {
            if info.type_var_arity > 0 {
                for &idx in trait_indices {
                    let inst = &self.instances[idx];
                    if inst.constraints.is_empty() {
                        continue;
                    }
                    // Single-type diagnostic only covers single-parameter HK traits.
                    if inst.target_types.len() != 1 {
                        continue;
                    }

                    let Some((actual_ctor, actual_bound_args)) = split_type_constructor(ty) else {
                        continue;
                    };
                    let Some((inst_ctor, inst_bound_args)) =
                        split_instance_type_constructor(&inst.target_types[0])
                    else {
                        continue;
                    };

                    let actual_len = actual_bound_args.len();
                    let inst_len = inst_bound_args.len();
                    if actual_ctor != inst_ctor
                        || (actual_len != inst_len && actual_len != inst_len + info.type_var_arity)
                    {
                        continue;
                    }

                    let mut bindings = HashMap::new();
                    if !inst_bound_args.iter().zip(actual_bound_args.iter()).all(
                        |(pattern_arg, actual_arg)| {
                            types_match_with_bindings(pattern_arg, actual_arg, &mut bindings)
                        },
                    ) {
                        continue;
                    }

                    let bound = &actual_bound_args[..inst_len];
                    let ctor_binding = reconstruct_ctor_type(&actual_ctor, bound);

                    let unsatisfied: Vec<UnsatisfiedBound> = inst
                        .constraints
                        .iter()
                        .filter_map(|constraint| {
                            let bound_tys: Option<Vec<Type>> = constraint
                                .type_vars
                                .iter()
                                .map(|name| {
                                    let id = inst.type_var_ids.get(name)?;
                                    Some(
                                        bindings
                                            .get(id)
                                            .cloned()
                                            .unwrap_or_else(|| ctor_binding.clone()),
                                    )
                                })
                                .collect();
                            let bound_tys = bound_tys?;
                            let satisfied = self
                                .find_instance_for(&constraint.trait_name, &bound_tys)
                                .is_some();
                            if !satisfied {
                                Some(UnsatisfiedBound {
                                    trait_name: constraint.trait_name.local_name.clone(),
                                    ty: bound_tys
                                        .iter()
                                        .map(|t| format!("{}", t.strip_own()))
                                        .collect::<Vec<_>>()
                                        .join(", "),
                                })
                            } else {
                                None
                            }
                        })
                        .collect();

                    if !unsatisfied.is_empty() {
                        return Some(InstanceDiagnostic {
                            instance_type: instance_type_display(inst),
                            unsatisfied,
                        });
                    }
                }
                return None;
            }
        }

        // Regular (non-HK) path — single-type diagnostic only covers single-parameter traits.
        for &idx in trait_indices {
            let inst = &self.instances[idx];
            if inst.constraints.is_empty() {
                continue;
            }
            if inst.target_types.len() != 1 {
                continue;
            }

            let mut bindings = HashMap::new();
            if !types_match_with_bindings(&inst.target_types[0], ty, &mut bindings) {
                continue;
            }

            let unsatisfied: Vec<UnsatisfiedBound> = inst
                .constraints
                .iter()
                .filter_map(|constraint| {
                    let bound_tys: Option<Vec<Type>> = constraint
                        .type_vars
                        .iter()
                        .map(|name| {
                            let id = inst.type_var_ids.get(name)?;
                            bindings.get(id).cloned()
                        })
                        .collect();
                    let bound_tys = bound_tys?;
                    let satisfied = self
                        .find_instance_for(&constraint.trait_name, &bound_tys)
                        .is_some();
                    if !satisfied {
                        Some(UnsatisfiedBound {
                            trait_name: constraint.trait_name.local_name.clone(),
                            ty: bound_tys
                                .iter()
                                .map(|t| format!("{}", t.strip_own()))
                                .collect::<Vec<_>>()
                                .join(", "),
                        })
                    } else {
                        None
                    }
                })
                .collect();

            if !unsatisfied.is_empty() {
                return Some(InstanceDiagnostic {
                    instance_type: instance_type_display(inst),
                    unsatisfied,
                });
            }
        }

        None
    }
}

/// Format a type, substituting TypeVarIds back to their user-written names.
fn format_type_with_names(ty: &Type, id_to_name: &HashMap<TypeVarId, &str>) -> String {
    match ty {
        Type::Var(id) => {
            if let Some(name) = id_to_name.get(id) {
                name.to_string()
            } else {
                format!("{ty}")
            }
        }
        Type::Named(name, args) if args.is_empty() => name.clone(),
        Type::Named(name, args) => {
            let arg_strs: Vec<String> = args
                .iter()
                .map(|a| format_type_with_names(a, id_to_name))
                .collect();
            format!("{name}[{}]", arg_strs.join(", "))
        }
        Type::Own(inner) => format!("own {}", format_type_with_names(inner, id_to_name)),
        Type::App(ctor, args) => {
            let ctor_str = format_type_with_names(ctor, id_to_name);
            let arg_strs: Vec<String> = args
                .iter()
                .map(|a| format_type_with_names(a, id_to_name))
                .collect();
            format!("{ctor_str}[{}]", arg_strs.join(", "))
        }
        _ => format!("{ty}"),
    }
}

fn instance_type_display(inst: &InstanceInfo) -> String {
    let id_to_name: HashMap<TypeVarId, &str> = inst
        .type_var_ids
        .iter()
        .map(|(name, id)| (*id, name.as_str()))
        .collect();
    inst.target_types
        .iter()
        .map(|t| format_type_with_names(t, &id_to_name))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Describes why a conditional instance failed to match.
pub struct InstanceDiagnostic {
    /// The instance pattern, e.g. "Vec[a]"
    pub instance_type: String,
    /// Unsatisfied constraints with their concrete types
    pub unsatisfied: Vec<UnsatisfiedBound>,
}

pub struct UnsatisfiedBound {
    pub trait_name: String,
    /// The concrete type that didn't implement the trait
    pub ty: String,
}

impl InstanceDiagnostic {
    pub fn to_note(&self) -> String {
        let failures: Vec<String> = self
            .unsatisfied
            .iter()
            .map(|u| format!("`{}` is not implemented for `{}`", u.trait_name, u.ty))
            .collect();
        format!(
            "an impl for `{}` exists, but {}",
            self.instance_type,
            failures.join(" and "),
        )
    }
}

fn types_match_with_bindings(
    pattern: &Type,
    actual: &Type,
    bindings: &mut HashMap<TypeVarId, Type>,
) -> bool {
    match (pattern, actual) {
        // Type variable in instance type matches anything
        (Type::Var(id), _) => match bindings.get(id) {
            Some(existing) => existing == actual,
            None => {
                bindings.insert(*id, actual.clone());
                true
            }
        },
        (Type::Int, Type::Int)
        | (Type::Float, Type::Float)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Unit, Type::Unit) => true,
        (Type::Named(n1, args1), Type::Named(n2, args2)) => {
            n1 == n2
                && args1.len() == args2.len()
                && args1
                    .iter()
                    .zip(args2)
                    .all(|(a, b)| types_match_with_bindings(a, b, bindings))
        }
        (Type::Own(a), Type::Own(b)) => types_match_with_bindings(a, b, bindings),
        // own T matches T for instance lookup
        (Type::Own(inner), other) => types_match_with_bindings(inner, other, bindings),
        (other, Type::Own(inner)) => types_match_with_bindings(other, inner, bindings),
        // MaybeOwn/Shape treated same as Own for trait matching (transparent)
        (Type::MaybeOwn(_, inner), other)
        | (other, Type::MaybeOwn(_, inner))
        | (Type::Shape(inner), other)
        | (other, Type::Shape(inner)) => types_match_with_bindings(inner, other, bindings),
        // App reduces to Named for matching purposes
        (Type::App(ctor, args1), Type::Named(n, args2)) => {
            if let Type::Named(cn, ca) = ctor.as_ref() {
                ca.is_empty()
                    && cn == n
                    && args1.len() == args2.len()
                    && args1
                        .iter()
                        .zip(args2)
                        .all(|(a, b)| types_match_with_bindings(a, b, bindings))
            } else {
                false
            }
        }
        (Type::Named(n, args2), Type::App(ctor, args1)) => {
            if let Type::Named(cn, ca) = ctor.as_ref() {
                ca.is_empty()
                    && cn == n
                    && args1.len() == args2.len()
                    && args2.iter().zip(args1).all(|(pattern_arg, actual_arg)| {
                        types_match_with_bindings(pattern_arg, actual_arg, bindings)
                    })
            } else {
                false
            }
        }
        (Type::Fn(params1, ret1), Type::Fn(params2, ret2)) => {
            params1.len() == params2.len()
                && params1
                    .iter()
                    .zip(params2)
                    .all(|((_, a), (_, b))| types_match_with_bindings(a, b, bindings))
                && types_match_with_bindings(ret1, ret2, bindings)
        }
        (Type::Tuple(a), Type::Tuple(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b)
                    .all(|(x, y)| types_match_with_bindings(x, y, bindings))
        }
        _ => false,
    }
}

/// Identifies a type constructor for HKT instance matching.
#[derive(Debug, Clone, PartialEq, Eq)]
enum CtorId {
    Named(String),
    /// Function type constructor with the given parameter arity.
    /// `(a, b) -> c` has arity 2.
    Fn(usize),
}

/// Reconstruct a type from a split constructor and bound args.
fn reconstruct_ctor_type(ctor: &CtorId, bound_args: &[Type]) -> Type {
    match ctor {
        CtorId::Fn(_) => {
            if bound_args.is_empty() {
                Type::fn_consuming(vec![], Type::FnHole)
            } else {
                let (params, ret) = bound_args.split_at(bound_args.len() - 1);
                Type::fn_consuming(params.to_vec(), ret[0].clone())
            }
        }
        CtorId::Named(name) => Type::Named(name.clone(), bound_args.to_vec()),
    }
}

fn split_type_constructor(ty: &Type) -> Option<(CtorId, Vec<Type>)> {
    match ty {
        Type::Named(name, args) => Some((CtorId::Named(name.clone()), args.clone())),
        Type::Fn(params, ret) => {
            let mut args: Vec<Type> = params.iter().map(|(_, t)| t.clone()).collect();
            args.push(*ret.clone());
            Some((CtorId::Fn(params.len()), args))
        }
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            split_type_constructor(inner)
        }
        _ => None,
    }
}

fn split_instance_type_constructor(ty: &Type) -> Option<(CtorId, Vec<Type>)> {
    match ty {
        Type::Named(name, args) => Some((CtorId::Named(name.clone()), args.clone())),
        Type::Fn(params, ret) => {
            let mut args: Vec<Type> = params.iter().map(|(_, t)| t.clone()).collect();
            args.push(*ret.clone());
            Some((CtorId::Fn(params.len()), args))
        }
        Type::App(ctor, args) => {
            let (ctor_id, mut ctor_args) = split_instance_type_constructor(ctor)?;
            ctor_args.extend(args.iter().cloned());
            Some((ctor_id, ctor_args))
        }
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            split_instance_type_constructor(inner)
        }
        _ => None,
    }
}

/// Check if two instance head types overlap (are unifiable).
/// Freshens type variables from both types into a shared namespace to avoid
/// aliasing, then attempts trial unification. The substitution is discarded —
/// only the success/failure result matters. Because the substitution is local,
/// starting TypeVarGen at 0 is safe (no external ID collision possible).
///
/// Kept for unit-test coverage; the production path uses `instances_overlap`
/// which handles multi-parameter instance tuples with a shared substitution.
#[cfg(test)]
fn types_overlap(a: &Type, b: &Type) -> bool {
    let mut gen = TypeVarGen::new();
    let a_fresh = freshen_type_vars(a, &mut gen);
    let b_fresh = freshen_type_vars(b, &mut gen);
    let mut subst = Substitution::new();
    unify(&a_fresh, &b_fresh, &mut subst).is_ok()
}

/// Check whether two instance type-argument tuples overlap.
///
/// Two tuples overlap iff they have the same arity and each pair of positions
/// unifies **in a single shared substitution** — meaning type variables at
/// different positions within the same instance must resolve consistently.
/// Without a shared substitution, `impl[a] Convert[Array[a], a]` and
/// `impl[b] Convert[Array[Int], String]` would falsely report non-overlap
/// because the `a` in position 0 and `a` in position 1 would be treated as
/// independent free variables.
fn instances_overlap(a: &[Type], b: &[Type]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut gen = TypeVarGen::new();
    // Freshen a's vars together (shared var_map) and b's vars together (own var_map),
    // into a common generator namespace.
    let mut a_map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
    let mut b_map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
    let a_fresh: Vec<Type> = a
        .iter()
        .map(|t| freshen_inner(t, &mut a_map, &mut gen))
        .collect();
    let b_fresh: Vec<Type> = b
        .iter()
        .map(|t| freshen_inner(t, &mut b_map, &mut gen))
        .collect();
    let mut subst = Substitution::new();
    for (x, y) in a_fresh.iter().zip(b_fresh.iter()) {
        if unify(x, y, &mut subst).is_err() {
            return false;
        }
    }
    true
}

fn format_type_tuple_with_var_map(types: &[Type], names: &HashMap<TypeVarId, &str>) -> String {
    types
        .iter()
        .map(|t| crate::types::format_type_with_var_map(t, names))
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
fn freshen_type_vars(ty: &Type, gen: &mut TypeVarGen) -> Type {
    let mut var_map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
    freshen_inner(ty, &mut var_map, gen)
}

/// Returns true if `ty` contains any `Type::Var`.
fn contains_type_var(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Fn(params, ret) => {
            params.iter().any(|(_, p)| contains_type_var(p)) || contains_type_var(ret)
        }
        Type::Named(_, args) => args.iter().any(contains_type_var),
        Type::App(ctor, args) => contains_type_var(ctor) || args.iter().any(contains_type_var),
        Type::Tuple(elems) => elems.iter().any(contains_type_var),
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            contains_type_var(inner)
        }
        Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit | Type::FnHole => false,
    }
}

/// Freshen all free type vars in `ty` using a fresh substitution map.
/// Wrapper around `freshen_inner`, exposed for the multi-param solver.
pub(crate) fn freshen_type(
    ty: &Type,
    var_map: &mut HashMap<TypeVarId, TypeVarId>,
    gen: &mut TypeVarGen,
) -> Type {
    freshen_inner(ty, var_map, gen)
}

fn freshen_inner(
    ty: &Type,
    var_map: &mut HashMap<TypeVarId, TypeVarId>,
    gen: &mut TypeVarGen,
) -> Type {
    match ty {
        Type::Var(id) => {
            let fresh = *var_map.entry(*id).or_insert_with(|| gen.fresh());
            Type::Var(fresh)
        }
        Type::Fn(params, ret) => Type::Fn(
            params
                .iter()
                .map(|(m, p)| (*m, freshen_inner(p, var_map, gen)))
                .collect(),
            Box::new(freshen_inner(ret, var_map, gen)),
        ),
        Type::Named(name, args) => Type::Named(
            name.clone(),
            args.iter()
                .map(|a| freshen_inner(a, var_map, gen))
                .collect(),
        ),
        Type::App(ctor, args) => Type::App(
            Box::new(freshen_inner(ctor, var_map, gen)),
            args.iter()
                .map(|a| freshen_inner(a, var_map, gen))
                .collect(),
        ),
        Type::Own(inner) => Type::Own(Box::new(freshen_inner(inner, var_map, gen))),
        Type::Shape(inner) => Type::Shape(Box::new(freshen_inner(inner, var_map, gen))),
        Type::MaybeOwn(q, inner) => {
            Type::MaybeOwn(*q, Box::new(freshen_inner(inner, var_map, gen)))
        }
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|e| freshen_inner(e, var_map, gen))
                .collect(),
        ),
        Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit | Type::FnHole => {
            ty.clone()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{InstanceInfo, TraitInfo, TraitMethod, TraitRegistry};
    use crate::typed_ast::{ResolvedConstraint, TraitName};
    use crate::types::{Type, TypeVarGen};
    use crate::unify::TypeError;
    use std::collections::HashMap;

    fn tn(name: &str) -> TraitName {
        TraitName::new("test".to_string(), name.to_string())
    }

    fn rc(trait_name: &str, type_var: &str) -> ResolvedConstraint {
        ResolvedConstraint {
            trait_name: tn(trait_name),
            type_vars: vec![type_var.to_string()],
            span: (0, 0),
        }
    }

    fn trait_info(name: &str) -> TraitInfo {
        trait_info_with_arity(name, 0)
    }

    fn trait_info_with_arity(name: &str, type_var_arity: usize) -> TraitInfo {
        let var_a = TypeVarGen::new().fresh();
        TraitInfo {
            name: name.to_string(),
            module_path: "test".to_string(),
            type_var: "a".to_string(),
            type_var_id: var_a,
            type_var_ids: vec![var_a],
            type_var_names: vec!["a".to_string()],
            type_var_arity,
            superclasses: vec![],
            methods: Vec::<TraitMethod>::new(),
            span: (0, 0),
            is_prelude: false,
        }
    }

    fn instance(
        trait_name: &str,
        target_type: Type,
        target_type_name: &str,
        constraints: Vec<ResolvedConstraint>,
    ) -> InstanceInfo {
        let var_a = TypeVarGen::new().fresh();
        InstanceInfo {
            trait_name: tn(trait_name),
            target_types: vec![target_type],
            target_type_name: target_type_name.to_string(),
            type_var_ids: HashMap::from([(String::from("a"), var_a)]),
            constraints,

            span: (0, 0),
            is_builtin: false,
        }
    }

    fn instance_multi(
        trait_name: &str,
        target_types: Vec<Type>,
        type_var_ids: HashMap<String, crate::types::TypeVarId>,
    ) -> InstanceInfo {
        let joined = target_types
            .iter()
            .map(|t| format!("{t}"))
            .collect::<Vec<_>>()
            .join(", ");
        InstanceInfo {
            trait_name: tn(trait_name),
            target_types,
            target_type_name: joined,
            type_var_ids,
            constraints: vec![],
            span: (0, 0),
            is_builtin: false,
        }
    }

    #[test]
    fn constrained_instance_matches_only_when_bounds_are_satisfied() {
        let var_a = TypeVarGen::new().fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Show")).unwrap();
        registry
            .register_instance(instance("Show", Type::Int, "Int", vec![]))
            .unwrap();
        registry
            .register_instance(instance(
                "Show",
                Type::Named("Option".to_string(), vec![Type::Var(var_a)]),
                "Option",
                vec![rc("Show", "a")],
            ))
            .unwrap();

        let option_int = Type::Named("Option".to_string(), vec![Type::Int]);
        let option_blob = Type::Named(
            "Option".to_string(),
            vec![Type::Named("Blob".to_string(), vec![])],
        );

        assert!(registry.find_instance(&tn("Show"), &option_int).is_some());
        assert!(registry.find_instance(&tn("Show"), &option_blob).is_none());
    }

    #[test]
    fn constrained_instance_cycle_returns_none() {
        let var_a = TypeVarGen::new().fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Show")).unwrap();
        registry
            .register_instance(instance(
                "Show",
                Type::Var(var_a),
                "Loop",
                vec![rc("Show", "a")],
            ))
            .unwrap();

        assert!(registry.find_instance(&tn("Show"), &Type::Int).is_none());
    }

    #[test]
    fn unconstrained_hkt_instance_still_matches_by_constructor() {
        let mut registry = TraitRegistry::new();
        registry
            .register_trait(trait_info_with_arity("Functor", 1))
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: tn("Functor"),
                target_types: vec![Type::Named("List".to_string(), vec![])],
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::new(),
                constraints: vec![],

                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();

        let list_int = Type::Named("List".to_string(), vec![Type::Int]);

        assert!(registry.find_instance(&tn("Functor"), &list_int).is_some());
    }

    #[test]
    fn constrained_hkt_instance_requires_constructor_bounds() {
        let mut registry = TraitRegistry::new();
        registry
            .register_trait(trait_info_with_arity("Functor", 1))
            .unwrap();
        registry
            .register_trait(trait_info_with_arity("Foldable", 1))
            .unwrap();
        registry
            .register_trait(trait_info_with_arity("Traversable", 1))
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: tn("Functor"),
                target_types: vec![Type::Named("List".to_string(), vec![])],
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::new(),
                constraints: vec![],

                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: tn("Foldable"),
                target_types: vec![Type::Named("List".to_string(), vec![])],
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::new(),
                constraints: vec![],

                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: tn("Traversable"),
                target_types: vec![Type::Named("List".to_string(), vec![])],
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::from([(String::from("f"), TypeVarGen::new().fresh())]),
                constraints: vec![rc("Functor", "f"), rc("Foldable", "f")],

                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();

        let list_int = Type::Named("List".to_string(), vec![Type::Int]);

        assert!(registry
            .find_instance(&tn("Traversable"), &list_int)
            .is_some());
    }

    #[test]
    fn constrained_hkt_instance_binds_partially_applied_constructor_arguments() {
        let var_e = TypeVarGen::new().fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Show")).unwrap();
        registry
            .register_trait(trait_info_with_arity("Functor", 1))
            .unwrap();
        registry
            .register_instance(instance("Show", Type::Int, "Int", vec![]))
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: tn("Functor"),
                target_types: vec![Type::Named("Result".to_string(), vec![Type::Var(var_e)])],
                target_type_name: "Result".to_string(),
                type_var_ids: HashMap::from([(String::from("e"), var_e)]),
                constraints: vec![rc("Show", "e")],

                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();

        let result_int_string = Type::Named("Result".to_string(), vec![Type::Int, Type::String]);
        let result_blob_string = Type::Named(
            "Result".to_string(),
            vec![Type::Named("Blob".to_string(), vec![]), Type::String],
        );

        assert!(registry
            .find_instance(&tn("Functor"), &result_int_string)
            .is_some());
        assert!(registry
            .find_instance(&tn("Functor"), &result_blob_string)
            .is_none());
    }

    #[test]
    fn full_type_instance_resolution_distinguishes_applied_types() {
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Test")).unwrap();

        // Register (Test, Vec[Int]) and (Test, Vec[String]) — both should succeed
        registry
            .register_instance(instance(
                "Test",
                Type::Named("Vec".to_string(), vec![Type::Int]),
                "Vec$Int",
                vec![],
            ))
            .unwrap();
        registry
            .register_instance(instance(
                "Test",
                Type::Named("Vec".to_string(), vec![Type::String]),
                "Vec$String",
                vec![],
            ))
            .unwrap();

        // Duplicate (Test, Vec[Int]) should fail
        assert!(registry
            .register_instance(instance(
                "Test",
                Type::Named("Vec".to_string(), vec![Type::Int]),
                "Vec$Int",
                vec![],
            ))
            .is_err());
    }

    #[test]
    fn diagnose_single_constraint_failure() {
        let var_a = TypeVarGen::new().fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Test")).unwrap();
        // No instance of Test for String
        registry
            .register_instance(instance(
                "Test",
                Type::Named("Vec".to_string(), vec![Type::Var(var_a)]),
                "Vec",
                vec![rc("Test", "a")],
            ))
            .unwrap();

        let vec_string = Type::Named("Vec".to_string(), vec![Type::String]);
        let diag = registry.diagnose_missing_instance(&tn("Test"), &vec_string);
        assert!(diag.is_some());
        let diag = diag.unwrap();
        assert_eq!(diag.unsatisfied.len(), 1);
        assert_eq!(diag.unsatisfied[0].trait_name, "Test");
        assert_eq!(diag.unsatisfied[0].ty, "String");
        assert!(diag.to_note().contains("an impl for"));
        assert!(diag
            .to_note()
            .contains("`Test` is not implemented for `String`"));
    }

    #[test]
    fn diagnose_multiple_constraint_failures() {
        let mut gen = TypeVarGen::new();
        let var_k = gen.fresh();
        let var_v = gen.fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Show")).unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: tn("Show"),
                target_types: vec![Type::Named(
                    "Map".to_string(),
                    vec![Type::Var(var_k), Type::Var(var_v)],
                )],
                target_type_name: "Map".to_string(),
                type_var_ids: HashMap::from([
                    (String::from("k"), var_k),
                    (String::from("v"), var_v),
                ]),
                constraints: vec![rc("Show", "k"), rc("Show", "v")],

                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();

        let map_blob_opaque = Type::Named(
            "Map".to_string(),
            vec![
                Type::Named("Blob".to_string(), vec![]),
                Type::Named("Opaque".to_string(), vec![]),
            ],
        );
        let diag = registry
            .diagnose_missing_instance(&tn("Show"), &map_blob_opaque)
            .unwrap();
        assert_eq!(diag.unsatisfied.len(), 2);
        let note = diag.to_note();
        assert!(note.contains("`Show` is not implemented for `Blob`"));
        assert!(note.contains("`Show` is not implemented for `Opaque`"));
    }

    #[test]
    fn diagnose_no_candidate_returns_none() {
        let registry = TraitRegistry::new();
        let result = registry.diagnose_missing_instance(&tn("Show"), &Type::Int);
        assert!(result.is_none());
    }

    #[test]
    fn types_overlap_parametric_subsumes_concrete() {
        let mut gen = TypeVarGen::new();
        let a = Type::Named("Vec".into(), vec![Type::Var(gen.fresh())]);
        let b = Type::Named("Vec".into(), vec![Type::Int]);
        assert!(super::types_overlap(&a, &b));
    }

    #[test]
    fn types_overlap_distinct_concrete_args() {
        let a = Type::Named("Vec".into(), vec![Type::Int]);
        let b = Type::Named("Vec".into(), vec![Type::String]);
        assert!(!super::types_overlap(&a, &b));
    }

    #[test]
    fn types_overlap_fully_parametric_overlaps_everything() {
        let mut gen = TypeVarGen::new();
        let a = Type::Var(gen.fresh());
        let b = Type::Int;
        assert!(super::types_overlap(&a, &b));
    }

    #[test]
    fn types_overlap_fn_type_subsumption() {
        let mut gen = TypeVarGen::new();
        let a = Type::fn_consuming(vec![Type::Var(gen.fresh())], Type::Var(gen.fresh()));
        let b = Type::fn_consuming(vec![Type::Int], Type::Var(gen.fresh()));
        assert!(super::types_overlap(&a, &b));
    }

    #[test]
    fn types_overlap_app_with_var_ctor() {
        use crate::types::TypeVarId;
        let a = Type::App(Box::new(Type::Var(TypeVarId(100))), vec![Type::Int]);
        let b = Type::Named("Vec".into(), vec![Type::Int]);
        assert!(super::types_overlap(&a, &b));
    }

    #[test]
    fn diagnose_unconditional_instance_returns_none() {
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Show")).unwrap();
        registry
            .register_instance(instance("Show", Type::Int, "Int", vec![]))
            .unwrap();
        // Int has Show unconditionally, so diagnosis returns None
        let result = registry.diagnose_missing_instance(&tn("Show"), &Type::Int);
        assert!(result.is_none());
    }

    #[test]
    fn trait_alias_lookup() {
        let mut registry = TraitRegistry::new();
        let trait_name = TraitName::new("other/module".to_string(), "Eq".to_string());
        let var_a = TypeVarGen::new().fresh();
        registry
            .register_trait(TraitInfo {
                name: "Eq".to_string(),
                module_path: "other/module".to_string(),
                type_var: "a".to_string(),
                type_var_id: var_a,
                type_var_ids: vec![var_a],
                type_var_names: vec!["a".to_string()],
                type_var_arity: 0,
                superclasses: vec![],
                methods: Vec::<TraitMethod>::new(),
                span: (0, 0),
                is_prelude: false,
            })
            .unwrap();
        registry.register_trait_alias("MyEq".to_string(), trait_name.clone());

        // Lookup by alias should work
        let info = registry.lookup_trait_by_name("MyEq");
        assert!(info.is_some());
        assert_eq!(info.unwrap().name, "Eq");

        // Lookup by original name should also work
        let info = registry.lookup_trait_by_name("Eq");
        assert!(info.is_some());
    }

    #[test]
    fn bare_name_collision_detected() {
        let mut registry = TraitRegistry::new();
        let var_a = TypeVarGen::new().fresh();
        registry
            .register_trait(TraitInfo {
                name: "Eq".to_string(),
                module_path: "module_a".to_string(),
                type_var: "a".to_string(),
                type_var_id: var_a,
                type_var_ids: vec![var_a],
                type_var_names: vec!["a".to_string()],
                type_var_arity: 0,
                superclasses: vec![],
                methods: Vec::<TraitMethod>::new(),
                span: (0, 0),
                is_prelude: false,
            })
            .unwrap();

        // Registering a trait with the same bare name from a different module should error
        let var_a2 = TypeVarGen::new().fresh();
        let result = registry.register_trait(TraitInfo {
            name: "Eq".to_string(),
            module_path: "module_b".to_string(),
            type_var: "a".to_string(),
            type_var_id: var_a2,
            type_var_ids: vec![var_a2],
            type_var_names: vec!["a".to_string()],
            type_var_arity: 0,
            superclasses: vec![],
            methods: Vec::<TraitMethod>::new(),
            span: (0, 0),
            is_prelude: false,
        });
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::AmbiguousTraitName {
                name,
                existing_module,
                new_module,
            } => {
                assert_eq!(name, "Eq");
                assert_eq!(existing_module, "module_a");
                assert_eq!(new_module, "module_b");
            }
            other => panic!("expected AmbiguousTraitName, got {:?}", other),
        }
    }

    #[test]
    fn types_overlap_tuple_matching() {
        let a = Type::Tuple(vec![Type::Int, Type::String]);
        let b = Type::Tuple(vec![Type::Int, Type::String]);
        assert!(super::types_overlap(&a, &b));
    }

    #[test]
    fn types_overlap_tuple_different() {
        let a = Type::Tuple(vec![Type::Int, Type::String]);
        let b = Type::Tuple(vec![Type::Int, Type::Bool]);
        assert!(!super::types_overlap(&a, &b));
    }

    #[test]
    fn types_overlap_tuple_parametric() {
        let mut gen = TypeVarGen::new();
        let a = Type::Tuple(vec![Type::Var(gen.fresh()), Type::String]);
        let b = Type::Tuple(vec![Type::Int, Type::String]);
        assert!(super::types_overlap(&a, &b));
    }

    #[test]
    fn types_match_with_bindings_tuple() {
        let mut gen = TypeVarGen::new();
        let var_a = gen.fresh();
        let pattern = Type::Tuple(vec![Type::Var(var_a), Type::String]);
        let actual = Type::Tuple(vec![Type::Int, Type::String]);
        let mut bindings = HashMap::new();
        assert!(super::types_match_with_bindings(
            &pattern,
            &actual,
            &mut bindings
        ));
        assert_eq!(bindings.get(&var_a), Some(&Type::Int));
    }

    #[test]
    fn types_match_with_bindings_tuple_no_match() {
        let pattern = Type::Tuple(vec![Type::Int, Type::String]);
        let actual = Type::Tuple(vec![Type::Int, Type::Bool]);
        let mut bindings = HashMap::new();
        assert!(!super::types_match_with_bindings(
            &pattern,
            &actual,
            &mut bindings
        ));
    }

    // ---- Multi-parameter instance registration, overlap, lookup ----

    #[test]
    fn register_multi_param_instance_stores_target_types() {
        let mut registry = TraitRegistry::new();
        registry
            .register_trait(trait_info_with_arity("Convert", 0))
            .unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        assert_eq!(
            registry.instances()[0].target_types,
            vec![Type::Int, Type::String]
        );
    }

    #[test]
    fn multi_param_exact_overlap_rejected() {
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        let result = registry.register_instance(instance_multi(
            "Convert",
            vec![Type::Int, Type::String],
            HashMap::new(),
        ));
        assert!(matches!(
            result,
            Err(boxed) if matches!(&*boxed, (TypeError::DuplicateInstance { .. }, _))
        ));
    }

    #[test]
    fn multi_param_parametric_overlap_rejected() {
        let mut gen = TypeVarGen::new();
        let var_a = gen.fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        // impl[a] Convert[Array[a], String]
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![
                    Type::Named("Array".into(), vec![Type::Var(var_a)]),
                    Type::String,
                ],
                HashMap::from([(String::from("a"), var_a)]),
            ))
            .unwrap();
        // impl Convert[Array[Int], String] overlaps
        let result = registry.register_instance(instance_multi(
            "Convert",
            vec![Type::Named("Array".into(), vec![Type::Int]), Type::String],
            HashMap::new(),
        ));
        assert!(matches!(
            result,
            Err(boxed) if matches!(&*boxed, (TypeError::DuplicateInstance { .. }, _))
        ));
    }

    #[test]
    fn multi_param_non_overlap_accepted() {
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::Float],
                HashMap::new(),
            ))
            .unwrap();
        assert_eq!(registry.instances().len(), 2);
    }

    #[test]
    fn multi_param_length_mismatch_does_not_overlap() {
        // A length-1 and a length-2 instance under the same trait name must
        // not be reported as overlapping. This is a safety test; the frontend
        // enforces arity separately, but the registry must be robust.
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi("Convert", vec![Type::Int], HashMap::new()))
            .unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        assert_eq!(registry.instances().len(), 2);
    }

    #[test]
    fn multi_param_shared_var_overlap_rejected() {
        // impl[a] Convert[Array[a], a]  vs  impl Convert[Array[Int], Int]
        // The `a` must be shared across positions in the first instance,
        // so the second must overlap (position 1 is consistently Int).
        let mut gen = TypeVarGen::new();
        let var_a = gen.fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![
                    Type::Named("Array".into(), vec![Type::Var(var_a)]),
                    Type::Var(var_a),
                ],
                HashMap::from([(String::from("a"), var_a)]),
            ))
            .unwrap();
        let result = registry.register_instance(instance_multi(
            "Convert",
            vec![Type::Named("Array".into(), vec![Type::Int]), Type::Int],
            HashMap::new(),
        ));
        assert!(matches!(
            result,
            Err(boxed) if matches!(&*boxed, (TypeError::DuplicateInstance { .. }, _))
        ));
    }

    #[test]
    fn multi_param_shared_var_non_overlap_accepted() {
        // impl[a] Convert[Array[a], a]  vs  impl Convert[Array[Int], String]
        // Position 1 disagrees (a must be Int per pos 0 but is String), so no overlap.
        let mut gen = TypeVarGen::new();
        let var_a = gen.fresh();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![
                    Type::Named("Array".into(), vec![Type::Var(var_a)]),
                    Type::Var(var_a),
                ],
                HashMap::from([(String::from("a"), var_a)]),
            ))
            .unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Named("Array".into(), vec![Type::Int]), Type::String],
                HashMap::new(),
            ))
            .unwrap();
        assert_eq!(registry.instances().len(), 2);
    }

    #[test]
    fn find_instance_multi_partial_unique() {
        use super::PartialMatch;
        let mut gen = TypeVarGen::new();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        // Query: position 0 = Int, position 1 = unknown (var) → unique match
        let var_b = gen.fresh();
        match registry.find_instance_multi_partial(&tn("Convert"), &[Type::Int, Type::Var(var_b)]) {
            PartialMatch::Unique(_) => {}
            _ => panic!("expected unique match"),
        }
    }

    #[test]
    fn find_instance_multi_partial_ambiguous() {
        use super::PartialMatch;
        let mut gen = TypeVarGen::new();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::Float],
                HashMap::new(),
            ))
            .unwrap();
        let var_b = gen.fresh();
        match registry.find_instance_multi_partial(&tn("Convert"), &[Type::Int, Type::Var(var_b)]) {
            PartialMatch::Multiple => {}
            _ => panic!("expected multiple"),
        }
    }

    #[test]
    fn find_instance_multi_partial_zero() {
        use super::PartialMatch;
        let mut gen = TypeVarGen::new();
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        let var_b = gen.fresh();
        match registry.find_instance_multi_partial(&tn("Convert"), &[Type::Bool, Type::Var(var_b)])
        {
            PartialMatch::None_ => {}
            _ => panic!("expected none"),
        }
    }

    #[test]
    fn find_instance_multi_positionwise_match() {
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Convert")).unwrap();
        registry
            .register_instance(instance_multi(
                "Convert",
                vec![Type::Int, Type::String],
                HashMap::new(),
            ))
            .unwrap();
        assert!(registry
            .find_instance_multi(&tn("Convert"), &[Type::Int, Type::String])
            .is_some());
        assert!(registry
            .find_instance_multi(&tn("Convert"), &[Type::Int, Type::Float])
            .is_none());
        assert!(registry
            .find_instance_multi(&tn("Convert"), &[Type::Int])
            .is_none());
    }
}
