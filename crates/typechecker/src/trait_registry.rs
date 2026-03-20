use std::collections::HashMap;

use krypton_parser::ast::TypeConstraint;
use krypton_parser::ast::Span;

use crate::types::Type;
use crate::types::TypeVarId;
use crate::unify::TypeError;

pub struct TraitInfo {
    pub name: String,
    pub module_path: Option<String>,
    pub type_var: String,
    pub type_var_id: TypeVarId,
    /// 0 = kind *, 1 = * -> *, 2 = * -> * -> *, etc.
    pub type_var_arity: usize,
    pub superclasses: Vec<String>,
    pub methods: Vec<TraitMethod>,
    pub span: Span,
}

pub struct TraitMethod {
    pub name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

pub struct InstanceInfo {
    pub trait_name: String,
    pub target_type: Type,
    pub target_type_name: String,
    pub type_var_ids: HashMap<String, TypeVarId>,
    pub constraints: Vec<TypeConstraint>,
    pub methods: Vec<String>,
    pub span: Span,
    pub is_builtin: bool,
}

pub struct TraitRegistry {
    traits: HashMap<String, TraitInfo>,
    instances: Vec<InstanceInfo>,
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
        }
    }

    pub fn register_trait(&mut self, info: TraitInfo) -> Result<(), TypeError> {
        if self.traits.contains_key(&info.name) {
            return Err(TypeError::OrphanInstance {
                trait_name: info.name.clone(),
                ty: info.name.clone(),
            });
        }
        self.traits.insert(info.name.clone(), info);
        Ok(())
    }

    pub fn register_instance(&mut self, info: InstanceInfo) -> Result<(), TypeError> {
        // Check for duplicate (trait, type) pairs
        for existing in &self.instances {
            if existing.trait_name == info.trait_name
                && existing.target_type_name == info.target_type_name
            {
                return Err(TypeError::OrphanInstance {
                    trait_name: info.trait_name.clone(),
                    ty: info.target_type_name.clone(),
                });
            }
        }
        self.instances.push(info);
        Ok(())
    }

    pub fn lookup_trait(&self, name: &str) -> Option<&TraitInfo> {
        self.traits.get(name)
    }

    pub fn find_instance(&self, trait_name: &str, ty: &Type) -> Option<&InstanceInfo> {
        let mut resolution_stack = Vec::new();
        self.find_instance_inner(trait_name, ty, &mut resolution_stack)
    }

    fn find_instance_inner<'a>(
        &'a self,
        trait_name: &str,
        ty: &Type,
        resolution_stack: &mut Vec<(String, String)>,
    ) -> Option<&'a InstanceInfo> {
        let key = (trait_name.to_string(), format!("{ty}"));
        if resolution_stack.contains(&key) {
            return None;
        }

        // For HK traits (arity > 0), match by extracting the outermost type constructor
        let trait_info = self.traits.get(trait_name);
        if let Some(info) = trait_info {
            if info.type_var_arity > 0 {
                resolution_stack.push(key);
                let matched = self.instances.iter().find(|inst| {
                    if inst.trait_name != trait_name {
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
                    if !inst_bound_args
                        .iter()
                        .zip(actual_bound_args.iter())
                        .all(|(pattern_arg, actual_arg)| {
                            types_match_with_bindings(pattern_arg, actual_arg, &mut bindings)
                        })
                    {
                        return false;
                    }

                    let ctor_binding =
                        Type::Named(actual_ctor.clone(), actual_bound_args[..inst_len].to_vec());

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
            if inst.trait_name != trait_name {
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
        let trait_info = match self.traits.get(&instance.trait_name) {
            Some(t) => t,
            None => return Ok(()),
        };
        for superclass in &trait_info.superclasses {
            if self
                .find_instance(superclass, &instance.target_type)
                .is_none()
            {
                return Err(TypeError::NoInstance {
                    trait_name: superclass.clone(),
                    ty: instance.target_type_name.clone(),
                    required_by: Some(instance.trait_name.clone()),
                });
            }
        }
        Ok(())
    }

    pub fn find_instance_by_trait_and_span(
        &self,
        trait_name: &str,
        span: Span,
    ) -> Option<&InstanceInfo> {
        self.instances
            .iter()
            .find(|inst| inst.trait_name == trait_name && inst.span == span)
    }

    pub fn trait_method_names(&self) -> Vec<(String, crate::typed_ast::TraitId)> {
        let mut result = Vec::new();
        for (_trait_name, info) in &self.traits {
            let trait_id = crate::typed_ast::TraitId::new(info.module_path.clone(), info.name.clone());
            for method in &info.methods {
                result.push((method.name.clone(), trait_id.clone()));
            }
        }
        result
    }

    pub fn traits(&self) -> &HashMap<String, TraitInfo> {
        &self.traits
    }

    pub fn instances(&self) -> &[InstanceInfo] {
        &self.instances
    }

    /// When `find_instance` returns None, explain why by finding instances that
    /// structurally match but have failing `where` constraints.
    /// Called only on the error path — zero impact on the happy path.
    pub fn diagnose_missing_instance(&self, trait_name: &str, ty: &Type) -> Option<InstanceDiagnostic> {
        let trait_info = self.traits.get(trait_name);

        // HK trait path (arity > 0)
        if let Some(info) = trait_info {
            if info.type_var_arity > 0 {
                for inst in &self.instances {
                    if inst.trait_name != trait_name || inst.constraints.is_empty() {
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
                    if !inst_bound_args
                        .iter()
                        .zip(actual_bound_args.iter())
                        .all(|(pattern_arg, actual_arg)| {
                            types_match_with_bindings(pattern_arg, actual_arg, &mut bindings)
                        })
                    {
                        continue;
                    }

                    let ctor_binding =
                        Type::Named(actual_ctor.clone(), actual_bound_args[..inst_len].to_vec());

                    let unsatisfied: Vec<UnsatisfiedBound> = inst
                        .constraints
                        .iter()
                        .filter_map(|constraint| {
                            let Some(type_var_id) = inst.type_var_ids.get(&constraint.type_var) else {
                                return None;
                            };
                            let bound_ty = bindings.get(type_var_id).unwrap_or(&ctor_binding);
                            if self.find_instance(&constraint.trait_name, bound_ty).is_none() {
                                Some(UnsatisfiedBound {
                                    trait_name: constraint.trait_name.clone(),
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
            if inst.trait_name != trait_name || inst.constraints.is_empty() {
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
                    if self.find_instance(&constraint.trait_name, bound_ty).is_none() {
                        Some(UnsatisfiedBound {
                            trait_name: constraint.trait_name.clone(),
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
            let arg_strs: Vec<String> = args.iter().map(|a| format_type_with_names(a, id_to_name)).collect();
            format!("{name}[{}]", arg_strs.join(", "))
        }
        Type::Own(inner) => format!("own {}", format_type_with_names(inner, id_to_name)),
        Type::App(ctor, args) => {
            let ctor_str = format_type_with_names(ctor, id_to_name);
            let arg_strs: Vec<String> = args.iter().map(|a| format_type_with_names(a, id_to_name)).collect();
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
                    && args2
                        .iter()
                        .zip(args1)
                        .all(|(pattern_arg, actual_arg)| {
                            types_match_with_bindings(pattern_arg, actual_arg, bindings)
                        })
            } else {
                false
            }
        }
        _ => false,
    }
}

fn split_type_constructor(ty: &Type) -> Option<(String, Vec<Type>)> {
    match ty {
        Type::Named(name, args) => Some((name.clone(), args.clone())),
        Type::Own(inner) => split_type_constructor(inner),
        _ => None,
    }
}

fn split_instance_type_constructor(ty: &Type) -> Option<(String, Vec<Type>)> {
    match ty {
        Type::Named(name, args) => Some((name.clone(), args.clone())),
        Type::App(ctor, args) => {
            let (ctor_name, mut ctor_args) = split_instance_type_constructor(ctor)?;
            ctor_args.extend(args.iter().cloned());
            Some((ctor_name, ctor_args))
        }
        Type::Own(inner) => split_instance_type_constructor(inner),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{InstanceInfo, TraitInfo, TraitMethod, TraitRegistry};
    use crate::types::{Type, TypeVarGen};
    use krypton_parser::ast::TypeConstraint;
    use std::collections::HashMap;

    fn trait_info(name: &str) -> TraitInfo {
        trait_info_with_arity(name, 0)
    }

    fn trait_info_with_arity(name: &str, type_var_arity: usize) -> TraitInfo {
        let var_a = TypeVarGen::new().fresh();
        TraitInfo {
            name: name.to_string(),
            module_path: None,
            type_var: "a".to_string(),
            type_var_id: var_a,
            type_var_arity,
            superclasses: vec![],
            methods: Vec::<TraitMethod>::new(),
            span: (0, 0),
        }
    }

    fn instance(
        trait_name: &str,
        target_type: Type,
        target_type_name: &str,
        constraints: Vec<TypeConstraint>,
    ) -> InstanceInfo {
        let var_a = TypeVarGen::new().fresh();
        InstanceInfo {
            trait_name: trait_name.to_string(),
            target_type,
            target_type_name: target_type_name.to_string(),
            type_var_ids: HashMap::from([(String::from("a"), var_a)]),
            constraints,
            methods: vec![],
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
                vec![TypeConstraint {
                    type_var: "a".to_string(),
                    trait_name: "Show".to_string(),
                    span: (0, 0),
                }],
            ))
            .unwrap();

        let option_int = Type::Named("Option".to_string(), vec![Type::Int]);
        let option_blob = Type::Named(
            "Option".to_string(),
            vec![Type::Named("Blob".to_string(), vec![])],
        );

        assert!(registry.find_instance("Show", &option_int).is_some());
        assert!(registry.find_instance("Show", &option_blob).is_none());
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
                vec![TypeConstraint {
                    type_var: "a".to_string(),
                    trait_name: "Show".to_string(),
                    span: (0, 0),
                }],
            ))
            .unwrap();

        assert!(registry.find_instance("Show", &Type::Int).is_none());
    }

    #[test]
    fn unconstrained_hkt_instance_still_matches_by_constructor() {
        let mut registry = TraitRegistry::new();
        registry
            .register_trait(trait_info_with_arity("Functor", 1))
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: "Functor".to_string(),
                target_type: Type::Named("List".to_string(), vec![]),
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::new(),
                constraints: vec![],
                methods: vec![],
                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();

        let list_int = Type::Named("List".to_string(), vec![Type::Int]);

        assert!(registry.find_instance("Functor", &list_int).is_some());
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
                trait_name: "Functor".to_string(),
                target_type: Type::Named("List".to_string(), vec![]),
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::new(),
                constraints: vec![],
                methods: vec![],
                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: "Foldable".to_string(),
                target_type: Type::Named("List".to_string(), vec![]),
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::new(),
                constraints: vec![],
                methods: vec![],
                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: "Traversable".to_string(),
                target_type: Type::Named("List".to_string(), vec![]),
                target_type_name: "List".to_string(),
                type_var_ids: HashMap::from([(String::from("f"), TypeVarGen::new().fresh())]),
                constraints: vec![
                    TypeConstraint {
                        type_var: "f".to_string(),
                        trait_name: "Functor".to_string(),
                        span: (0, 0),
                    },
                    TypeConstraint {
                        type_var: "f".to_string(),
                        trait_name: "Foldable".to_string(),
                        span: (0, 0),
                    },
                ],
                methods: vec![],
                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();

        let list_int = Type::Named("List".to_string(), vec![Type::Int]);

        assert!(registry.find_instance("Traversable", &list_int).is_some());
    }

    #[test]
    fn constrained_hkt_instance_binds_partially_applied_constructor_arguments() {
        let var_e = TypeVarGen::new().fresh();
        let mut registry = TraitRegistry::new();
        registry
            .register_trait(trait_info("Show"))
            .unwrap();
        registry
            .register_trait(trait_info_with_arity("Functor", 1))
            .unwrap();
        registry
            .register_instance(instance("Show", Type::Int, "Int", vec![]))
            .unwrap();
        registry
            .register_instance(InstanceInfo {
                trait_name: "Functor".to_string(),
                target_type: Type::Named("Result".to_string(), vec![Type::Var(var_e)]),
                target_type_name: "Result".to_string(),
                type_var_ids: HashMap::from([(String::from("e"), var_e)]),
                constraints: vec![TypeConstraint {
                    type_var: "e".to_string(),
                    trait_name: "Show".to_string(),
                    span: (0, 0),
                }],
                methods: vec![],
                span: (0, 0),
                is_builtin: false,
            })
            .unwrap();

        let result_int_string =
            Type::Named("Result".to_string(), vec![Type::Int, Type::String]);
        let result_blob_string = Type::Named(
            "Result".to_string(),
            vec![Type::Named("Blob".to_string(), vec![]), Type::String],
        );

        assert!(registry.find_instance("Functor", &result_int_string).is_some());
        assert!(registry.find_instance("Functor", &result_blob_string).is_none());
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
                vec![TypeConstraint {
                    type_var: "a".to_string(),
                    trait_name: "Test".to_string(),
                    span: (0, 0),
                }],
            ))
            .unwrap();

        let vec_string = Type::Named("Vec".to_string(), vec![Type::String]);
        let diag = registry.diagnose_missing_instance("Test", &vec_string);
        assert!(diag.is_some());
        let diag = diag.unwrap();
        assert_eq!(diag.unsatisfied.len(), 1);
        assert_eq!(diag.unsatisfied[0].trait_name, "Test");
        assert_eq!(diag.unsatisfied[0].ty, "String");
        assert!(diag.to_note().contains("an impl for"));
        assert!(diag.to_note().contains("`Test` is not implemented for `String`"));
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
                trait_name: "Show".to_string(),
                target_type: Type::Named(
                    "Map".to_string(),
                    vec![Type::Var(var_k), Type::Var(var_v)],
                ),
                target_type_name: "Map".to_string(),
                type_var_ids: HashMap::from([
                    (String::from("k"), var_k),
                    (String::from("v"), var_v),
                ]),
                constraints: vec![
                    TypeConstraint {
                        type_var: "k".to_string(),
                        trait_name: "Show".to_string(),
                        span: (0, 0),
                    },
                    TypeConstraint {
                        type_var: "v".to_string(),
                        trait_name: "Show".to_string(),
                        span: (0, 0),
                    },
                ],
                methods: vec![],
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
            .diagnose_missing_instance("Show", &map_blob_opaque)
            .unwrap();
        assert_eq!(diag.unsatisfied.len(), 2);
        let note = diag.to_note();
        assert!(note.contains("`Show` is not implemented for `Blob`"));
        assert!(note.contains("`Show` is not implemented for `Opaque`"));
    }

    #[test]
    fn diagnose_no_candidate_returns_none() {
        let registry = TraitRegistry::new();
        let result = registry.diagnose_missing_instance("Show", &Type::Int);
        assert!(result.is_none());
    }

    #[test]
    fn diagnose_unconditional_instance_returns_none() {
        let mut registry = TraitRegistry::new();
        registry.register_trait(trait_info("Show")).unwrap();
        registry
            .register_instance(instance("Show", Type::Int, "Int", vec![]))
            .unwrap();
        // Int has Show unconditionally, so diagnosis returns None
        let result = registry.diagnose_missing_instance("Show", &Type::Int);
        assert!(result.is_none());
    }
}
