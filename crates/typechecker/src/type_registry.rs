use std::collections::HashMap;

use krypton_parser::ast::{TypeDeclKind, TypeExpr};

use crate::typed_ast::{ExportedTypeInfo, ExportedTypeKind};
use crate::types::{Type, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::TypeError;

pub struct TypeInfo {
    pub name: String,
    pub type_params: Vec<String>,
    pub type_param_vars: Vec<TypeVarId>,
    pub kind: TypeKind,
    pub lifts: Option<krypton_parser::ast::Lifts>,
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

/// Controls which types are considered in scope during type resolution.
#[derive(Clone, Copy)]
pub enum ResolutionContext {
    /// User-written type annotation — only explicitly imported/declared types accepted.
    UserAnnotation,
    /// Internal type declaration processing — any registered/forward-declared type accepted.
    InternalDecl,
}

pub struct TypeRegistry {
    types: HashMap<String, TypeInfo>,
    aliases: HashMap<String, String>,
    /// Names that have been forward-declared but not yet fully registered.
    forward_declared: std::collections::HashSet<String>,
    /// Type names that are visible to user-written type annotations.
    /// Types registered only for internal inference (e.g. implicit parent types
    /// from constructor imports) are NOT in this set.
    user_visible: std::collections::HashSet<String>,
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
            aliases: HashMap::new(),
            forward_declared: std::collections::HashSet::new(),
            user_visible: std::collections::HashSet::new(),
        }
    }

    /// Register built-in types (Int, Float, Bool, String, Unit, Vec) so that
    /// arity checks can find them in the registry instead of a separate function.
    pub fn register_builtins(&mut self, gen: &mut TypeVarGen) {
        for name in &["Int", "Float", "Bool", "String", "Unit"] {
            self.types.entry(name.to_string()).or_insert(TypeInfo {
                name: name.to_string(),
                type_params: vec![],
                type_param_vars: vec![],
                kind: TypeKind::Record { fields: vec![] },
                lifts: None,
                is_prelude: true,
            });
        }
        // Vec[a] — registered as a builtin so orphan checks and arity checks work.
        // The real implementation lives in stdlib/core/vec.kr.
        self.types.entry("Vec".to_string()).or_insert(TypeInfo {
            name: "Vec".to_string(),
            type_params: vec!["a".to_string()],
            type_param_vars: vec![gen.fresh()],
            kind: TypeKind::Record { fields: vec![] },
            lifts: None,
            is_prelude: true,
        });
        // All builtins are user-visible in annotations
        for name in &["Int", "Float", "Bool", "String", "Unit", "Vec"] {
            self.user_visible.insert(name.to_string());
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

    pub fn register_type_alias(&mut self, alias: &str, target: &str) -> Result<(), TypeError> {
        if self.types.contains_key(alias) || self.aliases.contains_key(alias) {
            return Err(TypeError::DuplicateType {
                name: alias.to_string(),
            });
        }
        if !self.types.contains_key(target) {
            return Err(TypeError::UnknownType {
                name: target.to_string(),
                suggestion: None,
                variant_of: None,
                is_value: false,
            });
        }
        self.aliases.insert(alias.to_string(), target.to_string());
        Ok(())
    }

    /// Mark a registered type as a prelude type (can be shadowed by user definitions).
    pub fn set_prelude(&mut self, name: &str) {
        if let Some(info) = self.types.get_mut(name) {
            info.is_prelude = true;
        }
        self.user_visible.insert(name.to_string());
    }

    /// Mark a type name as visible to user-written type annotations.
    /// Canonicalizes the name so callers don't need to double-mark aliases.
    pub fn mark_user_visible(&mut self, name: &str) {
        let canonical = self.canonical_name(name).to_string();
        self.user_visible.insert(canonical);
    }

    /// Check if a type name is visible to user-written type annotations.
    pub fn is_user_visible(&self, name: &str) -> bool {
        let canonical = self.canonical_name(name);
        self.user_visible.contains(canonical)
    }

    /// If `name` is a variant constructor of some sum type, return that type's name.
    pub fn find_variant_parent(&self, name: &str) -> Option<&str> {
        for info in self.types.values() {
            if let TypeKind::Sum { variants } = &info.kind {
                if variants.iter().any(|v| v.name == name) {
                    return Some(&info.name);
                }
            }
        }
        None
    }

    pub fn lookup_type(&self, name: &str) -> Option<&TypeInfo> {
        let canonical = self.canonical_name(name);
        self.types.get(canonical)
    }

    pub fn canonical_name<'a>(&'a self, name: &'a str) -> &'a str {
        self.aliases.get(name).map(|s| s.as_str()).unwrap_or(name)
    }

    /// Register a type name as known without full type info.
    /// Used for forward declarations so that self-referential and
    /// mutually recursive type declarations can resolve each other.
    pub fn register_name(&mut self, name: &str) {
        self.forward_declared.insert(name.to_string());
    }

    /// Check if a name is known (either fully registered or forward-declared).
    pub fn is_known(&self, name: &str) -> bool {
        self.types.contains_key(name)
            || self.aliases.contains_key(name)
            || self.forward_declared.contains(name)
    }

    /// Return the expected number of type parameters for a named type.
    pub fn expected_arity(&self, name: &str) -> Option<usize> {
        self.lookup_type(name).map(|info| info.type_params.len())
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
///
/// `context` controls which types are considered in scope:
///
/// - `UserAnnotation`: Only types explicitly imported or declared by the user
///   are accepted (checks `is_user_visible`). Used for user-written type
///   annotations like `fun wrap(x: Int) -> Option[Int]`. This enforces BL-1:
///   importing only constructors (`import core/option.{Some, None}`) does not
///   make the parent type (`Option`) available in annotations.
///
/// - `InternalDecl`: Any registered or forward-declared type is accepted
///   (checks `is_known`). Used internally when processing type declarations,
///   where self-referential types need to resolve before they're fully
///   registered. For example, `type List[a] = Cons(a, List[a]) | Nil` — while
///   processing the `Cons` variant, `List` is only forward-declared via
///   `register_name` and not yet in `user_visible`.
pub fn resolve_type_expr(
    texpr: &TypeExpr,
    type_param_map: &HashMap<String, TypeVarId>,
    type_param_arity: &HashMap<String, usize>,
    registry: &TypeRegistry,
    context: ResolutionContext,
    self_type: Option<&Type>,
) -> Result<Type, TypeError> {
    match texpr {
        TypeExpr::Named { name, .. } | TypeExpr::Qualified { name, .. } => resolve_named(
            name,
            type_param_map,
            type_param_arity,
            registry,
            context,
            self_type,
        ),
        TypeExpr::Var { name, .. } => {
            if let Some(&var_id) = type_param_map.get(name) {
                Ok(Type::Var(var_id))
            } else {
                resolve_named(
                    name,
                    type_param_map,
                    type_param_arity,
                    registry,
                    context,
                    self_type,
                )
            }
        }
        TypeExpr::App { name, args, .. } => {
            let mut resolved_args = Vec::new();
            for a in args {
                resolved_args.push(resolve_type_expr(
                    a,
                    type_param_map,
                    type_param_arity,
                    registry,
                    context,
                    self_type,
                )?);
            }
            // If the name is a type parameter (HKT variable), produce Type::App
            if let Some(&var_id) = type_param_map.get(name) {
                if let Some(expected_arity) = type_param_arity.get(name) {
                    if *expected_arity != resolved_args.len() {
                        return Err(TypeError::KindMismatch {
                            type_name: name.clone(),
                            expected_arity: *expected_arity,
                            actual_arity: resolved_args.len(),
                        });
                    }
                }
                return Ok(Type::App(Box::new(Type::Var(var_id)), resolved_args));
            }
            // Validate the type name
            resolve_named(
                name,
                type_param_map,
                type_param_arity,
                registry,
                context,
                self_type,
            )?;
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
            Ok(Type::Named(
                registry.canonical_name(name).to_string(),
                resolved_args,
            ))
        }
        TypeExpr::Fn { params, ret, .. } => {
            let mut param_types: Vec<(crate::types::ParamMode, Type)> = Vec::new();
            for p in params {
                let ty = resolve_type_expr(
                    &p.ty,
                    type_param_map,
                    type_param_arity,
                    registry,
                    context,
                    self_type,
                )?;
                param_types.push((p.mode, ty));
            }
            let ret_type = resolve_type_expr(
                ret,
                type_param_map,
                type_param_arity,
                registry,
                context,
                self_type,
            )?;
            Ok(Type::Fn(param_types, Box::new(ret_type)))
        }
        TypeExpr::Own { inner, .. } => Ok(Type::Own(Box::new(resolve_type_expr(
            inner,
            type_param_map,
            type_param_arity,
            registry,
            context,
            self_type,
        )?))),
        TypeExpr::Shape { inner, .. } => Ok(Type::Shape(Box::new(resolve_type_expr(
            inner,
            type_param_map,
            type_param_arity,
            registry,
            context,
            self_type,
        )?))),
        TypeExpr::Tuple { elements, .. } => {
            let mut elem_types = Vec::new();
            for e in elements {
                elem_types.push(resolve_type_expr(
                    e,
                    type_param_map,
                    type_param_arity,
                    registry,
                    context,
                    self_type,
                )?);
            }
            Ok(Type::Tuple(elem_types))
        }
        TypeExpr::Wildcard { span } => Err(TypeError::WildcardNotAllowed { span: *span }),
    }
}

fn resolve_named(
    name: &str,
    type_param_map: &HashMap<String, TypeVarId>,
    _type_param_arity: &HashMap<String, usize>,
    registry: &TypeRegistry,
    context: ResolutionContext,
    self_type: Option<&Type>,
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
        "Self" => match self_type {
            Some(ty) => Ok(ty.clone()),
            None => Err(TypeError::SelfOutsideImpl),
        },
        _ => {
            let is_available = match context {
                ResolutionContext::UserAnnotation => registry.is_user_visible(name),
                ResolutionContext::InternalDecl => registry.is_known(name),
            };
            if is_available {
                Ok(Type::Named(
                    registry.canonical_name(name).to_string(),
                    Vec::new(),
                ))
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
                    let suggestion_available = match context {
                        ResolutionContext::UserAnnotation => registry.is_user_visible(&capitalized),
                        ResolutionContext::InternalDecl => registry.is_known(&capitalized),
                    };
                    if is_builtin || suggestion_available {
                        Some(capitalized)
                    } else {
                        None
                    }
                } else {
                    None
                };
                let variant_of = registry.find_variant_parent(name).map(|s| s.to_string());
                Err(TypeError::UnknownType {
                    name: name.to_string(),
                    suggestion,
                    variant_of,
                    is_value: false,
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
    let type_param_arity: HashMap<String, usize> = HashMap::new();
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
                let ty = resolve_type_expr(
                    texpr,
                    &type_param_map,
                    &type_param_arity,
                    registry,
                    ResolutionContext::InternalDecl,
                    None,
                )?;
                resolved_fields.push((name.clone(), ty));
            }

            // Record constructor: positional fn(field_types...) -> NamedType
            let field_types: Vec<Type> = resolved_fields.iter().map(|(_, t)| t.clone()).collect();
            let ctor_ty = Type::fn_consuming(field_types, named_type.clone());
            constructors.push((
                decl.name.clone(),
                TypeScheme {
                    vars: quantified_vars.clone(),
                    constraints: Vec::new(),
                    ty: ctor_ty,
                    var_names: HashMap::new(),
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
                    resolved_fields.push(resolve_type_expr(
                        texpr,
                        &type_param_map,
                        &type_param_arity,
                        registry,
                        ResolutionContext::InternalDecl,
                        None,
                    )?);
                }

                // Variant constructor
                let ctor_ty = if resolved_fields.is_empty() {
                    // Nullary variant: just the named type (not a function)
                    named_type.clone()
                } else {
                    // Constructor function: fn(fields...) -> NamedType
                    Type::fn_consuming(resolved_fields.clone(), named_type.clone())
                };

                constructors.push((
                    variant.name.clone(),
                    TypeScheme {
                        vars: quantified_vars.clone(),
                        constraints: Vec::new(),
                        ty: ctor_ty,
                        var_names: HashMap::new(),
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
        lifts: None,
        is_prelude: false,
    })?;

    Ok(constructors)
}

/// Register a type from a pre-resolved `ExportedTypeInfo` (from a source module's
/// `exported_type_infos`). This avoids re-resolving variant field types from raw AST,
/// which would require transitive type dependencies in the consumer's registry.
///
/// Creates fresh TypeVarIds and substitutes the old ones in the pre-resolved field types.
pub fn register_type_from_export(
    info: &ExportedTypeInfo,
    registry: &mut TypeRegistry,
    gen: &mut TypeVarGen,
) -> Result<Vec<(String, TypeScheme)>, TypeError> {
    // Create fresh type vars for type params and build old→new mapping
    let mut fresh_vars: Vec<TypeVarId> = Vec::new();
    let mut old_to_new: HashMap<TypeVarId, TypeVarId> = HashMap::new();

    for (i, _) in info.type_params.iter().enumerate() {
        let fresh_id = gen.fresh();
        fresh_vars.push(fresh_id);
        if i < info.type_param_vars.len() {
            old_to_new.insert(info.type_param_vars[i], fresh_id);
        }
    }

    // Build the named type
    let type_args: Vec<Type> = fresh_vars.iter().map(|&v| Type::Var(v)).collect();
    let named_type = Type::Named(info.name.clone(), type_args);

    let mut constructors: Vec<(String, TypeScheme)> = Vec::new();

    let kind = match &info.kind {
        ExportedTypeKind::Opaque => TypeKind::Record { fields: vec![] },
        ExportedTypeKind::Record { fields } => {
            let resolved_fields: Vec<(String, Type)> = fields
                .iter()
                .map(|(name, ty)| (name.clone(), remap_vars(ty, &old_to_new)))
                .collect();

            let field_types: Vec<Type> = resolved_fields.iter().map(|(_, t)| t.clone()).collect();
            let ctor_ty = Type::fn_consuming(field_types, named_type.clone());
            constructors.push((
                info.name.clone(),
                TypeScheme {
                    vars: fresh_vars.clone(),
                    constraints: Vec::new(),
                    ty: ctor_ty,
                    var_names: HashMap::new(),
                },
            ));

            TypeKind::Record {
                fields: resolved_fields,
            }
        }
        ExportedTypeKind::Sum { variants } => {
            let mut variant_infos = Vec::new();
            for v in variants {
                let resolved_fields: Vec<Type> = v
                    .fields
                    .iter()
                    .map(|ty| remap_vars(ty, &old_to_new))
                    .collect();

                let ctor_ty = if resolved_fields.is_empty() {
                    named_type.clone()
                } else {
                    Type::fn_consuming(resolved_fields.clone(), named_type.clone())
                };

                constructors.push((
                    v.name.clone(),
                    TypeScheme {
                        vars: fresh_vars.clone(),
                        constraints: Vec::new(),
                        ty: ctor_ty,
                        var_names: HashMap::new(),
                    },
                ));

                variant_infos.push(VariantInfo {
                    name: v.name.clone(),
                    fields: resolved_fields,
                });
            }

            TypeKind::Sum {
                variants: variant_infos,
            }
        }
    };

    registry.register_type(TypeInfo {
        name: info.name.clone(),
        type_params: info.type_params.clone(),
        type_param_vars: fresh_vars,
        kind,
        lifts: info.lifts.clone(),
        is_prelude: false,
    })?;

    Ok(constructors)
}

/// Remap TypeVarIds in a Type according to the given mapping.
fn remap_vars(ty: &Type, mapping: &HashMap<TypeVarId, TypeVarId>) -> Type {
    match ty {
        Type::Var(id) => {
            if let Some(&new_id) = mapping.get(id) {
                Type::Var(new_id)
            } else {
                ty.clone()
            }
        }
        Type::Named(name, args) => Type::Named(
            name.clone(),
            args.iter().map(|a| remap_vars(a, mapping)).collect(),
        ),
        Type::Fn(params, ret) => Type::Fn(
            params
                .iter()
                .map(|(m, p)| (*m, remap_vars(p, mapping)))
                .collect(),
            Box::new(remap_vars(ret, mapping)),
        ),
        Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| remap_vars(e, mapping)).collect()),
        Type::Own(inner) => Type::Own(Box::new(remap_vars(inner, mapping))),
        Type::Shape(inner) => Type::Shape(Box::new(remap_vars(inner, mapping))),
        Type::MaybeOwn(q, inner) => Type::MaybeOwn(*q, Box::new(remap_vars(inner, mapping))),
        Type::App(base, args) => Type::App(
            Box::new(remap_vars(base, mapping)),
            args.iter().map(|a| remap_vars(a, mapping)).collect(),
        ),
        Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit | Type::FnHole => {
            ty.clone()
        }
    }
}
