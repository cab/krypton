use std::collections::HashMap;

use krypton_parser::ast::{TypeDeclKind, TypeExpr};

use crate::types::{Type, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::TypeError;

pub struct TypeInfo {
    pub name: String,
    pub type_params: Vec<String>,
    pub type_param_vars: Vec<TypeVarId>,
    pub kind: TypeKind,
    pub is_prelude: bool,
}

pub enum TypeKind {
    Record { fields: Vec<(String, Type)> },
    Sum { variants: Vec<VariantInfo> },
}

pub struct VariantInfo {
    pub name: String,
    pub fields: Vec<Type>,
}

pub struct TypeRegistry {
    types: HashMap<String, TypeInfo>,
    /// Names that have been forward-declared but not yet fully registered.
    forward_declared: std::collections::HashSet<String>,
}

impl Default for TypeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeRegistry {
    pub fn new() -> Self {
        TypeRegistry {
            types: HashMap::new(),
            forward_declared: std::collections::HashSet::new(),
        }
    }

    /// Register built-in types (Int, Float, Bool, String, Unit, Object) so that
    /// arity checks can find them in the registry instead of a separate function.
    pub fn register_builtins(&mut self) {
        for name in &["Int", "Float", "Bool", "String", "Unit"] {
            self.types.entry(name.to_string()).or_insert(TypeInfo {
                name: name.to_string(),
                type_params: vec![],
                type_param_vars: vec![],
                kind: TypeKind::Record { fields: vec![] },
                is_prelude: true,
            });
        }
    }

    pub fn register_type(&mut self, info: TypeInfo) -> Result<(), TypeError> {
        if let Some(existing) = self.types.get(&info.name) {
            if !existing.is_prelude {
                return Err(TypeError::DuplicateType {
                    name: info.name.clone(),
                });
            }
        }
        self.types.insert(info.name.clone(), info);
        Ok(())
    }

    /// Mark a registered type as a prelude type (can be shadowed by user definitions).
    pub fn set_prelude(&mut self, name: &str) {
        if let Some(info) = self.types.get_mut(name) {
            info.is_prelude = true;
        }
    }

    pub fn lookup_type(&self, name: &str) -> Option<&TypeInfo> {
        self.types.get(name)
    }

    /// Register a type name as known without full type info.
    /// Used for forward declarations so that self-referential and
    /// mutually recursive type declarations can resolve each other.
    pub fn register_name(&mut self, name: &str) {
        self.forward_declared.insert(name.to_string());
    }

    /// Check if a name is known (either fully registered or forward-declared).
    pub fn is_known(&self, name: &str) -> bool {
        self.types.contains_key(name) || self.forward_declared.contains(name)
    }

    /// Return the expected number of type parameters for a named type.
    pub fn expected_arity(&self, name: &str) -> Option<usize> {
        self.types.get(name).map(|info| info.type_params.len())
    }

    /// Check if a name is a constructor (record or sum variant).
    pub fn is_constructor(&self, name: &str) -> bool {
        for info in self.types.values() {
            // Record constructor has same name as the type
            if info.name == name {
                if let TypeKind::Record { .. } = &info.kind {
                    return true;
                }
            }
            // Sum variant constructors
            if let TypeKind::Sum { variants } = &info.kind {
                if variants.iter().any(|v| v.name == name) {
                    return true;
                }
            }
        }
        false
    }
}

/// Resolve an AST `TypeExpr` to an internal `Type`, using the type parameter
/// mapping for type variables and the registry for named types.
pub fn resolve_type_expr(
    texpr: &TypeExpr,
    type_param_map: &HashMap<String, TypeVarId>,
    registry: &TypeRegistry,
) -> Result<Type, TypeError> {
    match texpr {
        TypeExpr::Named { name, .. } => resolve_named(name, type_param_map, registry),
        TypeExpr::Var { name, .. } => {
            if let Some(&var_id) = type_param_map.get(name) {
                Ok(Type::Var(var_id))
            } else {
                resolve_named(name, type_param_map, registry)
            }
        }
        TypeExpr::App { name, args, .. } => {
            let mut resolved_args = Vec::new();
            for a in args {
                resolved_args.push(resolve_type_expr(a, type_param_map, registry)?);
            }
            // If the name is a type parameter (HKT variable), produce Type::App
            if let Some(&var_id) = type_param_map.get(name) {
                return Ok(Type::App(Box::new(Type::Var(var_id)), resolved_args));
            }
            // Validate the type name
            resolve_named(name, type_param_map, registry)?;
            // Kind check: verify arity matches
            let expected = registry.expected_arity(name);
            if let Some(expected) = expected {
                if expected != resolved_args.len() {
                    return Err(TypeError::KindMismatch {
                        type_name: name.clone(),
                        expected_arity: expected,
                        actual_arity: resolved_args.len(),
                    });
                }
            }
            Ok(Type::Named(name.clone(), resolved_args))
        }
        TypeExpr::Fn { params, ret, .. } => {
            let mut param_types = Vec::new();
            for p in params {
                param_types.push(resolve_type_expr(p, type_param_map, registry)?);
            }
            let ret_type = resolve_type_expr(ret, type_param_map, registry)?;
            Ok(Type::Fn(param_types, Box::new(ret_type)))
        }
        TypeExpr::Own { inner, .. } => Ok(Type::Own(Box::new(resolve_type_expr(
            inner,
            type_param_map,
            registry,
        )?))),
        TypeExpr::Tuple { elements, .. } => {
            let mut elem_types = Vec::new();
            for e in elements {
                elem_types.push(resolve_type_expr(e, type_param_map, registry)?);
            }
            Ok(Type::Tuple(elem_types))
        }
    }
}

fn resolve_named(
    name: &str,
    type_param_map: &HashMap<String, TypeVarId>,
    registry: &TypeRegistry,
) -> Result<Type, TypeError> {
    // Check if it's a type parameter first
    if let Some(&var_id) = type_param_map.get(name) {
        return Ok(Type::Var(var_id));
    }
    // Check for builtin types
    match name {
        "Int" => Ok(Type::Int),
        "Float" => Ok(Type::Float),
        "Bool" => Ok(Type::Bool),
        "String" => Ok(Type::String),
        "Unit" => Ok(Type::Unit),
        "Object" => Ok(Type::Named("Object".to_string(), Vec::new())),
        _ => {
            if registry.is_known(name) {
                Ok(Type::Named(name.to_string(), Vec::new()))
            } else {
                // Compute suggestion: if lowercase, try capitalizing first letter
                let suggestion = if name.starts_with(|c: char| c.is_ascii_lowercase()) {
                    let capitalized = {
                        let mut chars = name.chars();
                        match chars.next() {
                            Some(c) => format!("{}{}", c.to_uppercase(), chars.as_str()),
                            None => String::new(),
                        }
                    };
                    let is_builtin = matches!(
                        capitalized.as_str(),
                        "Int" | "Float" | "Bool" | "String" | "Unit"
                    );
                    if is_builtin || registry.is_known(&capitalized) {
                        Some(capitalized)
                    } else {
                        None
                    }
                } else {
                    None
                };
                Err(TypeError::UnknownType {
                    name: name.to_string(),
                    suggestion,
                })
            }
        }
    }
}

/// Process a type declaration and produce constructor TypeSchemes to bind in the env.
pub fn process_type_decl(
    decl: &krypton_parser::ast::TypeDecl,
    registry: &mut TypeRegistry,
    gen: &mut TypeVarGen,
) -> Result<Vec<(String, TypeScheme)>, TypeError> {
    // Create fresh type vars for type params
    let mut type_param_map: HashMap<String, TypeVarId> = HashMap::new();
    let mut quantified_vars: Vec<TypeVarId> = Vec::new();
    for param_name in &decl.type_params {
        let var_id = gen.fresh();
        type_param_map.insert(param_name.clone(), var_id);
        quantified_vars.push(var_id);
    }

    // Build the named type (e.g., Point or Option<a>)
    let type_args: Vec<Type> = quantified_vars.iter().map(|&v| Type::Var(v)).collect();
    let named_type = Type::Named(decl.name.clone(), type_args);

    let mut constructors: Vec<(String, TypeScheme)> = Vec::new();

    let kind = match &decl.kind {
        TypeDeclKind::Record { fields } => {
            let mut resolved_fields: Vec<(String, Type)> = Vec::new();
            for (name, texpr) in fields {
                let ty = resolve_type_expr(texpr, &type_param_map, registry)?;
                resolved_fields.push((name.clone(), ty));
            }

            // Record constructor: positional fn(field_types...) -> NamedType
            let field_types: Vec<Type> = resolved_fields.iter().map(|(_, t)| t.clone()).collect();
            let ctor_ty = Type::Fn(field_types, Box::new(named_type.clone()));
            constructors.push((
                decl.name.clone(),
                TypeScheme {
                    vars: quantified_vars.clone(),
                    ty: ctor_ty,
                },
            ));

            TypeKind::Record {
                fields: resolved_fields,
            }
        }
        TypeDeclKind::Sum { variants } => {
            let mut variant_infos = Vec::new();
            for variant in variants {
                let mut resolved_fields: Vec<Type> = Vec::new();
                for texpr in &variant.fields {
                    resolved_fields.push(resolve_type_expr(texpr, &type_param_map, registry)?);
                }

                // Variant constructor
                let ctor_ty = if resolved_fields.is_empty() {
                    // Nullary variant: just the named type (not a function)
                    named_type.clone()
                } else {
                    // Constructor function: fn(fields...) -> NamedType
                    Type::Fn(resolved_fields.clone(), Box::new(named_type.clone()))
                };

                constructors.push((
                    variant.name.clone(),
                    TypeScheme {
                        vars: quantified_vars.clone(),
                        ty: ctor_ty,
                    },
                ));

                variant_infos.push(VariantInfo {
                    name: variant.name.clone(),
                    fields: resolved_fields,
                });
            }

            TypeKind::Sum {
                variants: variant_infos,
            }
        }
    };

    // Register in the type registry
    registry.register_type(TypeInfo {
        name: decl.name.clone(),
        type_params: decl.type_params.clone(),
        type_param_vars: quantified_vars.clone(),
        kind,
        is_prelude: false,
    })?;

    Ok(constructors)
}
