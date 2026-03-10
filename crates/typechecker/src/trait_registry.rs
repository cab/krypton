use std::collections::HashMap;

use krypton_parser::ast::Span;

use crate::types::{Type, TypeEnv, TypeScheme, TypeVarGen};
use crate::unify::TypeError;

pub struct TraitInfo {
    pub name: String,
    pub type_var: String,
    pub type_var_id: u32,
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
        // For HK traits (arity > 0), match by extracting the outermost type constructor
        let trait_info = self.traits.get(trait_name);
        if let Some(info) = trait_info {
            if info.type_var_arity > 0 {
                // Extract the type constructor name from the concrete type
                let ctor_name = match ty {
                    Type::Named(name, _) => Some(name.as_str()),
                    _ => None,
                };
                if let Some(ctor_name) = ctor_name {
                    return self.instances.iter().find(|inst| {
                        inst.trait_name == trait_name && inst.target_type_name == ctor_name
                    });
                }
                return None;
            }
        }
        self.instances.iter().find(|inst| {
            inst.trait_name == trait_name && types_match(&inst.target_type, ty)
        })
    }

    pub fn check_superclasses(&self, instance: &InstanceInfo) -> Result<(), TypeError> {
        let trait_info = match self.traits.get(&instance.trait_name) {
            Some(t) => t,
            None => return Ok(()),
        };
        for superclass in &trait_info.superclasses {
            if self.find_instance(superclass, &instance.target_type).is_none() {
                return Err(TypeError::NoInstance {
                    trait_name: superclass.clone(),
                    ty: instance.target_type_name.clone(),
                    required_by: Some(instance.trait_name.clone()),
                });
            }
        }
        Ok(())
    }

    pub fn find_instance_by_trait_and_span(&self, trait_name: &str, span: Span) -> Option<&InstanceInfo> {
        self.instances.iter().find(|inst| {
            inst.trait_name == trait_name && inst.span == span
        })
    }

    pub fn trait_method_names(&self) -> Vec<(String, String)> {
        let mut result = Vec::new();
        for (trait_name, info) in &self.traits {
            for method in &info.methods {
                result.push((method.name.clone(), trait_name.clone()));
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
}

/// Register all built-in operator traits and their instances for primitive types.
pub fn register_builtin_traits(
    registry: &mut TraitRegistry,
    env: &mut TypeEnv,
    gen: &mut TypeVarGen,
) {
    let builtin_span: Span = (0, 0);

    // Helper: register a binary trait (a, a) -> ret_type
    struct BinTraitDef {
        name: &'static str,
        method: &'static str,
        returns_self: bool, // true = returns a, false = returns Bool
    }

    let binary_traits = [
        BinTraitDef { name: "Add", method: "add", returns_self: true },
        BinTraitDef { name: "Sub", method: "sub", returns_self: true },
        BinTraitDef { name: "Mul", method: "mul", returns_self: true },
        BinTraitDef { name: "Div", method: "div", returns_self: true },
        BinTraitDef { name: "Eq",  method: "eq",  returns_self: false },
        BinTraitDef { name: "Ord", method: "lt",  returns_self: false },
    ];

    for def in &binary_traits {
        let tv_id = gen.fresh();
        let type_var = Type::Var(tv_id);
        let ret = if def.returns_self { type_var.clone() } else { Type::Bool };
        let superclasses = if def.name == "Ord" { vec!["Eq".to_string()] } else { vec![] };

        let _ = registry.register_trait(TraitInfo {
            name: def.name.to_string(),
            type_var: "a".to_string(),
            type_var_id: tv_id,
            type_var_arity: 0,
            superclasses,
            methods: vec![TraitMethod {
                name: def.method.to_string(),
                param_types: vec![type_var.clone(), type_var.clone()],
                return_type: ret.clone(),
            }],
            span: builtin_span,
        });

        // Bind method in env as polymorphic: forall a. fn(a, a) -> ret
        let fn_ty = Type::Fn(vec![type_var.clone(), type_var.clone()], Box::new(ret));
        env.bind(def.method.to_string(), TypeScheme { vars: vec![tv_id], ty: fn_ty });
    }

    // Neg: unary trait (a) -> a
    {
        let tv_id = gen.fresh();
        let type_var = Type::Var(tv_id);
        let _ = registry.register_trait(TraitInfo {
            name: "Neg".to_string(),
            type_var: "a".to_string(),
            type_var_id: tv_id,
            type_var_arity: 0,
            superclasses: vec![],
            methods: vec![TraitMethod {
                name: "neg".to_string(),
                param_types: vec![type_var.clone()],
                return_type: type_var.clone(),
            }],
            span: builtin_span,
        });
        let fn_ty = Type::Fn(vec![type_var.clone()], Box::new(type_var));
        env.bind("neg".to_string(), TypeScheme { vars: vec![tv_id], ty: fn_ty });
    }

    // Show: unary trait (a) -> String
    {
        let tv_id = gen.fresh();
        let type_var = Type::Var(tv_id);
        let _ = registry.register_trait(TraitInfo {
            name: "Show".to_string(),
            type_var: "a".to_string(),
            type_var_id: tv_id,
            type_var_arity: 0,
            superclasses: vec![],
            methods: vec![TraitMethod {
                name: "show".to_string(),
                param_types: vec![type_var.clone()],
                return_type: Type::String,
            }],
            span: builtin_span,
        });
        let fn_ty = Type::Fn(vec![type_var], Box::new(Type::String));
        env.bind("show".to_string(), TypeScheme { vars: vec![tv_id], ty: fn_ty });
    }

    // Register built-in instances
    struct BuiltinInstance {
        trait_name: &'static str,
        target_type: Type,
        target_name: &'static str,
        method: &'static str,
    }

    let instances = vec![
        // Int: Add, Sub, Mul, Div, Neg, Eq, Ord
        BuiltinInstance { trait_name: "Add", target_type: Type::Int, target_name: "Int", method: "add" },
        BuiltinInstance { trait_name: "Sub", target_type: Type::Int, target_name: "Int", method: "sub" },
        BuiltinInstance { trait_name: "Mul", target_type: Type::Int, target_name: "Int", method: "mul" },
        BuiltinInstance { trait_name: "Div", target_type: Type::Int, target_name: "Int", method: "div" },
        BuiltinInstance { trait_name: "Neg", target_type: Type::Int, target_name: "Int", method: "neg" },
        BuiltinInstance { trait_name: "Eq",  target_type: Type::Int, target_name: "Int", method: "eq" },
        BuiltinInstance { trait_name: "Ord", target_type: Type::Int, target_name: "Int", method: "lt" },
        // Float: Add, Sub, Mul, Div, Neg, Eq, Ord
        BuiltinInstance { trait_name: "Add", target_type: Type::Float, target_name: "Float", method: "add" },
        BuiltinInstance { trait_name: "Sub", target_type: Type::Float, target_name: "Float", method: "sub" },
        BuiltinInstance { trait_name: "Mul", target_type: Type::Float, target_name: "Float", method: "mul" },
        BuiltinInstance { trait_name: "Div", target_type: Type::Float, target_name: "Float", method: "div" },
        BuiltinInstance { trait_name: "Neg", target_type: Type::Float, target_name: "Float", method: "neg" },
        BuiltinInstance { trait_name: "Eq",  target_type: Type::Float, target_name: "Float", method: "eq" },
        BuiltinInstance { trait_name: "Ord", target_type: Type::Float, target_name: "Float", method: "lt" },
        // String: Add (concat), Eq
        BuiltinInstance { trait_name: "Add", target_type: Type::String, target_name: "String", method: "add" },
        BuiltinInstance { trait_name: "Eq",  target_type: Type::String, target_name: "String", method: "eq" },
        // Bool: Eq
        BuiltinInstance { trait_name: "Eq",  target_type: Type::Bool, target_name: "Bool", method: "eq" },
        // Show instances for primitive types
        BuiltinInstance { trait_name: "Show", target_type: Type::Int,    target_name: "Int",    method: "show" },
        BuiltinInstance { trait_name: "Show", target_type: Type::Float,  target_name: "Float",  method: "show" },
        BuiltinInstance { trait_name: "Show", target_type: Type::Bool,   target_name: "Bool",   method: "show" },
        BuiltinInstance { trait_name: "Show", target_type: Type::String, target_name: "String", method: "show" },
    ];

    for inst in instances {
        let _ = registry.register_instance(InstanceInfo {
            trait_name: inst.trait_name.to_string(),
            target_type: inst.target_type,
            target_type_name: inst.target_name.to_string(),
            methods: vec![inst.method.to_string()],
            span: builtin_span,
            is_builtin: true,
        });
    }
}

/// Check if two types match for instance lookup (concrete type matching).
/// Type variables in the instance type (first arg) act as wildcards.
fn types_match(a: &Type, b: &Type) -> bool {
    match (a, b) {
        // Type variable in instance type matches anything
        (Type::Var(_), _) => true,
        (Type::Int, Type::Int)
        | (Type::Float, Type::Float)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Unit, Type::Unit) => true,
        (Type::Named(n1, args1), Type::Named(n2, args2)) => {
            n1 == n2 && args1.len() == args2.len() && args1.iter().zip(args2).all(|(a, b)| types_match(a, b))
        }
        (Type::Own(a), Type::Own(b)) => types_match(a, b),
        // own T matches T for instance lookup
        (Type::Own(inner), other) | (other, Type::Own(inner)) => types_match(inner, other),
        // App reduces to Named for matching purposes
        (Type::App(ctor, args1), Type::Named(n, args2)) | (Type::Named(n, args2), Type::App(ctor, args1)) => {
            if let Type::Named(cn, ca) = ctor.as_ref() {
                ca.is_empty() && cn == n && args1.len() == args2.len() && args1.iter().zip(args2).all(|(a, b)| types_match(a, b))
            } else {
                false
            }
        }
        _ => false,
    }
}
