use std::collections::HashMap;

use krypton_parser::ast::Span;

use crate::types::{Substitution, Type, TypeVarGen, TypeVarId};
use crate::unify::{unify, TypeError};

use crate::typed_ast::{ResolvedConstraint, TraitName};

pub struct TraitInfo {
    pub name: String,
    pub module_path: String,
    pub type_var: String,
    pub type_var_id: TypeVarId,
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
    pub param_types: Vec<Type>,
    pub return_type: Type,
    /// Constraints on the method's own type parameters (not the trait's type param).
    /// e.g., `fun traverse[b](x: f[a]) -> f[b] where b: Default` stores `[(Default, TypeVarId_for_b)]`
    pub constraints: Vec<(TraitName, TypeVarId)>,
}

pub struct InstanceInfo {
    pub trait_name: TraitName,
    pub target_type: Type,
    pub target_type_name: String,
    pub type_var_ids: HashMap<String, TypeVarId>,
    pub constraints: Vec<ResolvedConstraint>,
    pub span: Span,
    pub is_builtin: bool,
}

pub struct TraitRegistry {
    traits: HashMap<TraitName, TraitInfo>,
    instances: Vec<InstanceInfo>,
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
            instances: Vec::new(),
            trait_aliases: HashMap::new(),
        }
    }

    pub fn register_trait(&mut self, info: TraitInfo) -> Result<(), TypeError> {
        let key = info.trait_name();
        if self.traits.contains_key(&key) {
            return Err(TypeError::OrphanInstance {
                trait_name: info.name.clone(),
                ty: info.name.clone(),
            });
        }
        // Check bare-name collision with a trait from a different module
        if let Some(existing) = self.traits.values().find(|t| t.name == info.name) {
            if existing.trait_name() != key {
                return Err(TypeError::AmbiguousTraitName {
                    name: info.name.clone(),
                    existing_module: existing.module_path.clone(),
                    new_module: info.module_path.clone(),
                });
            }
        }
        self.traits.insert(key, info);
        Ok(())
    }

    pub fn register_instance(&mut self, info: InstanceInfo) -> Result<(), (TypeError, Span)> {
        // Check for overlapping (trait, type) pairs via unification
        for existing in &self.instances {
            if existing.trait_name == info.trait_name
                && types_overlap(&existing.target_type, &info.target_type)
            {
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
                return Err((
                    TypeError::DuplicateInstance {
                        trait_name: info.trait_name.local_name.clone(),
                        ty: crate::types::format_type_with_var_map(&info.target_type, &names),
                        existing_ty: crate::types::format_type_with_var_map(
                            &existing.target_type,
                            &existing_names,
                        ),
                    },
                    existing.span,
                ));
            }
        }
        self.instances.push(info);
        Ok(())
    }

    pub fn lookup_trait(&self, name: &TraitName) -> Option<&TraitInfo> {
        self.traits.get(name)
    }

    /// Look up a trait by bare name (linear scan). Use only when module_path is unknown.
    /// Also checks trait aliases as a fallback.
    pub fn lookup_trait_by_name(&self, name: &str) -> Option<&TraitInfo> {
        self.traits
            .values()
            .find(|info| info.name == name)
            .or_else(|| {
                self.trait_aliases
                    .get(name)
                    .and_then(|tn| self.traits.get(tn))
            })
    }

    pub fn find_instance(&self, trait_name: &TraitName, ty: &Type) -> Option<&InstanceInfo> {
        let mut resolution_stack = Vec::new();
        self.find_instance_inner(trait_name, ty, &mut resolution_stack)
    }

    fn find_instance_inner<'a>(
        &'a self,
        trait_name: &TraitName,
        ty: &Type,
        resolution_stack: &mut Vec<(TraitName, String)>,
    ) -> Option<&'a InstanceInfo> {
        let key = (trait_name.clone(), format!("{ty}"));
        if resolution_stack.contains(&key) {
            return None;
        }

        // For HK traits (arity > 0), match by extracting the outermost type constructor
        let trait_info = self.lookup_trait(trait_name);
        if let Some(info) = trait_info {
            if info.type_var_arity > 0 {
                resolution_stack.push(key);
                let matched = self.instances.iter().find(|inst| {
                    if inst.trait_name != *trait_name {
                        return false;
                    }

                    let Some((actual_ctor, actual_bound_args)) = split_type_constructor(ty) else {
                        return false;
                    };
                    let Some((inst_ctor, inst_bound_args)) =
                        split_instance_type_constructor(&inst.target_type)
                    else {
                        return false;
                    };

                    let actual_len = actual_bound_args.len();
                    let inst_len = inst_bound_args.len();
                    if actual_ctor != inst_ctor
                        || (actual_len != inst_len && actual_len != inst_len + info.type_var_arity)
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

                    let bound = &actual_bound_args[..inst_len];
                    let ctor_binding = reconstruct_ctor_type(&actual_ctor, bound);

                    inst.constraints.iter().all(|constraint| {
                        let Some(type_var_id) = inst.type_var_ids.get(&constraint.type_var) else {
                            return false;
                        };
                        let bound_ty = bindings.get(type_var_id).unwrap_or(&ctor_binding);
                        self.find_instance_inner(&constraint.trait_name, bound_ty, resolution_stack)
                            .is_some()
                    })
                });
                resolution_stack.pop();
                return matched;
            }
        }

        resolution_stack.push(key);
        let matched = self.instances.iter().find(|inst| {
            if inst.trait_name != *trait_name {
                return false;
            }

            let mut bindings = HashMap::new();
            if !types_match_with_bindings(&inst.target_type, ty, &mut bindings) {
                return false;
            }

            inst.constraints.iter().all(|constraint| {
                let Some(type_var_id) = inst.type_var_ids.get(&constraint.type_var) else {
                    return false;
                };
                let Some(bound_ty) = bindings.get(type_var_id) else {
                    return false;
                };
                self.find_instance_inner(&constraint.trait_name, bound_ty, resolution_stack)
                    .is_some()
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
        for superclass in &trait_info.superclasses {
            if self
                .find_instance(superclass, &instance.target_type)
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
        self.instances
            .iter()
            .find(|inst| inst.trait_name == *trait_name && inst.span == span)
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

        // HK trait path (arity > 0)
        if let Some(info) = trait_info {
            if info.type_var_arity > 0 {
                for inst in &self.instances {
                    if inst.trait_name != *trait_name || inst.constraints.is_empty() {
                        continue;
                    }

                    let Some((actual_ctor, actual_bound_args)) = split_type_constructor(ty) else {
                        continue;
                    };
                    let Some((inst_ctor, inst_bound_args)) =
                        split_instance_type_constructor(&inst.target_type)
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
                            let Some(type_var_id) = inst.type_var_ids.get(&constraint.type_var)
                            else {
                                return None;
                            };
                            let bound_ty = bindings.get(type_var_id).unwrap_or(&ctor_binding);
                            if self
                                .find_instance(&constraint.trait_name, bound_ty)
                                .is_none()
                            {
                                Some(UnsatisfiedBound {
                                    trait_name: constraint.trait_name.local_name.clone(),
                                    ty: format!("{}", bound_ty.strip_own()),
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

        // Regular (non-HK) path
        for inst in &self.instances {
            if inst.trait_name != *trait_name || inst.constraints.is_empty() {
                continue;
            }

            let mut bindings = HashMap::new();
            if !types_match_with_bindings(&inst.target_type, ty, &mut bindings) {
                continue;
            }

            let unsatisfied: Vec<UnsatisfiedBound> = inst
                .constraints
                .iter()
                .filter_map(|constraint| {
                    let Some(type_var_id) = inst.type_var_ids.get(&constraint.type_var) else {
                        return None;
                    };
                    let Some(bound_ty) = bindings.get(type_var_id) else {
                        return None;
                    };
                    if self
                        .find_instance(&constraint.trait_name, bound_ty)
                        .is_none()
                    {
                        Some(UnsatisfiedBound {
                            trait_name: constraint.trait_name.local_name.clone(),
                            ty: format!("{}", bound_ty.strip_own()),
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
    format_type_with_names(&inst.target_type, &id_to_name)
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
                    .all(|(a, b)| types_match_with_bindings(a, b, bindings))
                && types_match_with_bindings(ret1, ret2, bindings)
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
                Type::Fn(vec![], Box::new(Type::FnHole))
            } else {
                let (params, ret) = bound_args.split_at(bound_args.len() - 1);
                Type::Fn(params.to_vec(), Box::new(ret[0].clone()))
            }
        }
        CtorId::Named(name) => Type::Named(name.clone(), bound_args.to_vec()),
    }
}

fn split_type_constructor(ty: &Type) -> Option<(CtorId, Vec<Type>)> {
    match ty {
        Type::Named(name, args) => Some((CtorId::Named(name.clone()), args.clone())),
        Type::Fn(params, ret) => {
            let mut args: Vec<Type> = params.clone();
            args.push(*ret.clone());
            Some((CtorId::Fn(params.len()), args))
        }
        Type::Own(inner) => split_type_constructor(inner),
        _ => None,
    }
}

fn split_instance_type_constructor(ty: &Type) -> Option<(CtorId, Vec<Type>)> {
    match ty {
        Type::Named(name, args) => Some((CtorId::Named(name.clone()), args.clone())),
        Type::Fn(params, ret) => {
            let mut args: Vec<Type> = params.clone();
            args.push(*ret.clone());
            Some((CtorId::Fn(params.len()), args))
        }
        Type::App(ctor, args) => {
            let (ctor_id, mut ctor_args) = split_instance_type_constructor(ctor)?;
            ctor_args.extend(args.iter().cloned());
            Some((ctor_id, ctor_args))
        }
        Type::Own(inner) => split_instance_type_constructor(inner),
        _ => None,
    }
}

/// Check if two instance head types overlap (are unifiable).
/// Freshens type variables from both types into a shared namespace to avoid
/// aliasing, then attempts trial unification. The substitution is discarded —
/// only the success/failure result matters. Because the substitution is local,
/// starting TypeVarGen at 0 is safe (no external ID collision possible).
fn types_overlap(a: &Type, b: &Type) -> bool {
    let mut gen = TypeVarGen::new();
    let a_fresh = freshen_type_vars(a, &mut gen);
    let b_fresh = freshen_type_vars(b, &mut gen);
    let mut subst = Substitution::new();
    unify(&a_fresh, &b_fresh, &mut subst).is_ok()
}

fn freshen_type_vars(ty: &Type, gen: &mut TypeVarGen) -> Type {
    let mut var_map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
    freshen_inner(ty, &mut var_map, gen)
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
                .map(|p| freshen_inner(p, var_map, gen))
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
            type_var: type_var.to_string(),
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
            target_type,
            target_type_name: target_type_name.to_string(),
            type_var_ids: HashMap::from([(String::from("a"), var_a)]),
            constraints,

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
                target_type: Type::Named("List".to_string(), vec![]),
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
                target_type: Type::Named("List".to_string(), vec![]),
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
                target_type: Type::Named("List".to_string(), vec![]),
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
                target_type: Type::Named("List".to_string(), vec![]),
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
                target_type: Type::Named("Result".to_string(), vec![Type::Var(var_e)]),
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
                target_type: Type::Named(
                    "Map".to_string(),
                    vec![Type::Var(var_k), Type::Var(var_v)],
                ),
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
        let a = Type::Fn(
            vec![Type::Var(gen.fresh())],
            Box::new(Type::Var(gen.fresh())),
        );
        let b = Type::Fn(vec![Type::Int], Box::new(Type::Var(gen.fresh())));
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
        registry
            .register_trait(TraitInfo {
                name: "Eq".to_string(),
                module_path: "other/module".to_string(),
                type_var: "a".to_string(),
                type_var_id: TypeVarGen::new().fresh(),
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
        registry
            .register_trait(TraitInfo {
                name: "Eq".to_string(),
                module_path: "module_a".to_string(),
                type_var: "a".to_string(),
                type_var_id: TypeVarGen::new().fresh(),
                type_var_arity: 0,
                superclasses: vec![],
                methods: Vec::<TraitMethod>::new(),
                span: (0, 0),
                is_prelude: false,
            })
            .unwrap();

        // Registering a trait with the same bare name from a different module should error
        let result = registry.register_trait(TraitInfo {
            name: "Eq".to_string(),
            module_path: "module_b".to_string(),
            type_var: "a".to_string(),
            type_var_id: TypeVarGen::new().fresh(),
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
}
