use std::collections::HashMap;

use krypton_parser::ast::{TypeDeclKind, TypeExpr};

use crate::types::{Type, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::TypeError;

pub struct TypeInfo {
    pub name: String,
    pub type_params: Vec<String>,
    pub type_param_vars: Vec<TypeVarId>,
    pub kind: TypeKind,
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
        }
    }

    pub fn register_type(&mut self, info: TypeInfo) -> Result<(), TypeError> {
        if self.types.contains_key(&info.name) {
            return Err(TypeError::DuplicateType {
                name: info.name.clone(),
            });
        }
        self.types.insert(info.name.clone(), info);
        Ok(())
    }

    pub fn lookup_type(&self, name: &str) -> Option<&TypeInfo> {
        self.types.get(name)
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
) -> Type {
    match texpr {
        TypeExpr::Named { name, .. } => resolve_named(name, type_param_map, registry),
        TypeExpr::Var { name, .. } => {
            if let Some(&var_id) = type_param_map.get(name) {
                Type::Var(var_id)
            } else {
                resolve_named(name, type_param_map, registry)
            }
        }
        TypeExpr::App { name, args, .. } => {
            let resolved_args: Vec<Type> = args
                .iter()
                .map(|a| resolve_type_expr(a, type_param_map, registry))
                .collect();
            Type::Named(name.clone(), resolved_args)
        }
        TypeExpr::Fn { params, ret, .. } => {
            let param_types: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr(p, type_param_map, registry))
                .collect();
            let ret_type = resolve_type_expr(ret, type_param_map, registry);
            Type::Fn(param_types, Box::new(ret_type))
        }
        TypeExpr::Own { inner, .. } => {
            Type::Own(Box::new(resolve_type_expr(inner, type_param_map, registry)))
        }
        TypeExpr::Tuple { elements, .. } => {
            let elem_types: Vec<Type> = elements
                .iter()
                .map(|e| resolve_type_expr(e, type_param_map, registry))
                .collect();
            Type::Tuple(elem_types)
        }
    }
}

fn resolve_named(
    name: &str,
    type_param_map: &HashMap<String, TypeVarId>,
    _registry: &TypeRegistry,
) -> Type {
    // Check if it's a type parameter first
    if let Some(&var_id) = type_param_map.get(name) {
        return Type::Var(var_id);
    }
    // Check for builtin types
    match name {
        "Int" => Type::Int,
        "Float" => Type::Float,
        "Bool" => Type::Bool,
        "String" => Type::String,
        "Unit" => Type::Unit,
        _ => Type::Named(name.to_string(), Vec::new()),
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
            let resolved_fields: Vec<(String, Type)> = fields
                .iter()
                .map(|(name, texpr)| {
                    let ty = resolve_type_expr(texpr, &type_param_map, registry);
                    (name.clone(), ty)
                })
                .collect();

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
                let resolved_fields: Vec<Type> = variant
                    .fields
                    .iter()
                    .map(|texpr| resolve_type_expr(texpr, &type_param_map, registry))
                    .collect();

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
    })?;

    Ok(constructors)
}
