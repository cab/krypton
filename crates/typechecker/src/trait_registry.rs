use std::collections::HashMap;

use krypton_parser::ast::Span;

use crate::types::Type;
use crate::unify::TypeError;

pub struct TraitInfo {
    pub name: String,
    pub type_var: String,
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
                return Err(TypeError::TraitNotImplemented {
                    trait_name: superclass.clone(),
                    ty: instance.target_type_name.clone(),
                    required_by: instance.trait_name.clone(),
                });
            }
        }
        Ok(())
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
}

/// Check if two types match for instance lookup (concrete type matching).
fn types_match(a: &Type, b: &Type) -> bool {
    match (a, b) {
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
        _ => false,
    }
}
