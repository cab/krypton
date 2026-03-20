//! Module compilation pipeline and JVM type mapping.

mod builder;
mod calls;
mod class_gen;
mod compiler;
mod expr;
mod intrinsics;
mod lambda;
mod pattern;
mod registration;

use std::collections::HashMap;

use krypton_parser::ast::TypeExpr;
use krypton_typechecker::typed_ast::TypedModule;
use krypton_typechecker::type_registry::{self, ResolutionContext};
use krypton_typechecker::types::{Type, TypeVarGen, TypeVarId};
use ristretto_classfile::attributes::{Attribute, Instruction};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, FieldType, Method,
    MethodAccessFlags, Version,
};

pub use compiler::{CodegenError, JvmType};

use compiler::{Compiler, DictRequirement};

/// Java 21 class file version (major 65).
const JAVA_21: Version = Version::Java21 { minor: 0 };

#[derive(Clone)]
struct ImportedInstanceInfo {
    class_name: String,
    target_type: Type,
    requirements: Vec<DictRequirement>,
}

fn dict_requirements_for_instance(
    type_var_ids: &HashMap<String, TypeVarId>,
    constraints: &[krypton_parser::ast::TypeConstraint],
    subdict_traits: &[(String, usize)],
) -> Vec<DictRequirement> {
    let mut dict_requirements: Vec<DictRequirement> = subdict_traits
        .iter()
        .map(|(trait_name, param_idx)| DictRequirement::TypeParam {
            trait_name: trait_name.clone(),
            param_idx: *param_idx,
        })
        .collect();
    for constraint in constraints {
        if let Some(&type_var) = type_var_ids.get(&constraint.type_var) {
            if !dict_requirements.iter().any(|requirement| {
                matches!(
                    requirement,
                    DictRequirement::Constraint {
                        trait_name,
                        type_var: existing_type_var,
                    } if trait_name == &constraint.trait_name && *existing_type_var == type_var
                )
            }) {
                dict_requirements.push(DictRequirement::Constraint {
                    trait_name: constraint.trait_name.clone(),
                    type_var,
                });
            }
        }
    }
    dict_requirements
}


fn type_to_jvm_basic(ty: &Type) -> Result<JvmType, CodegenError> {
    match ty {
        Type::Int => Ok(JvmType::Long),
        Type::Float => Ok(JvmType::Double),
        Type::Bool => Ok(JvmType::Int),
        Type::Unit => Ok(JvmType::Int),
        other => Err(CodegenError::TypeError(format!(
            "cannot map type to JVM: {other:?}"
        ))),
    }
}

fn jvm_type_to_field_descriptor(ty: JvmType) -> String {
    match ty {
        JvmType::Long => "J".to_string(),
        JvmType::Double => "D".to_string(),
        JvmType::Int => "Z".to_string(),
        JvmType::StructRef(_) => unreachable!("StructRef must be resolved via class_descriptors"),
    }
}

fn jvm_type_to_base_field_type(ty: JvmType) -> FieldType {
    match ty {
        JvmType::Long => FieldType::Base(ristretto_classfile::BaseType::Long),
        JvmType::Double => FieldType::Base(ristretto_classfile::BaseType::Double),
        JvmType::Int => FieldType::Base(ristretto_classfile::BaseType::Boolean),
        JvmType::StructRef(_) => unreachable!("StructRef must be resolved via class_descriptors"),
    }
}

fn type_expr_to_jvm_basic(texpr: &TypeExpr, compiler: &Compiler) -> Result<JvmType, CodegenError> {
    match texpr {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } | TypeExpr::Qualified { name, .. } => match name.as_str() {
            "Int" => Ok(JvmType::Long),
            "Float" => Ok(JvmType::Double),
            "Bool" => Ok(JvmType::Int),
            "String" => Ok(JvmType::StructRef(compiler.builder.refs.string_class)),
            "Unit" => Ok(JvmType::Int),
            // Any other named type (struct, opaque, Object) maps to Object ref.
            // Variant fields are stored as Ljava/lang/Object; at JVM level
            // (see jvm_type_to_field_descriptor), so we use object_class here.
            _ => Ok(JvmType::StructRef(compiler.builder.refs.object_class)),
        },
        // App types (e.g. Ref[Int], Mailbox[Msg]) — same as above
        TypeExpr::App { .. } => Ok(JvmType::StructRef(compiler.builder.refs.object_class)),
        _ => Err(CodegenError::TypeError(format!(
            "unsupported type expr in struct field: {texpr:?}"
        ))),
    }
}

/// Map a record field TypeExpr to a JvmType using the typechecker's erasure rules.
fn type_expr_to_jvm(
    compiler: &Compiler,
    texpr: &TypeExpr,
    type_registry_ref: &type_registry::TypeRegistry,
) -> Result<JvmType, CodegenError> {
    type_expr_to_jvm_with_params(compiler, texpr, type_registry_ref, &HashMap::new())
}

fn type_expr_to_jvm_with_params(
    compiler: &Compiler,
    texpr: &TypeExpr,
    type_registry_ref: &type_registry::TypeRegistry,
    type_param_map: &HashMap<String, krypton_typechecker::types::TypeVarId>,
) -> Result<JvmType, CodegenError> {
    let resolved = type_registry::resolve_type_expr(
        texpr,
        type_param_map,
        &HashMap::new(),
        type_registry_ref,
        ResolutionContext::InternalDecl,
        None,
    )
    .map_err(|e| CodegenError::TypeError(format!("type error: {e}")))?;
    compiler.type_to_jvm(&resolved)
}

fn type_expr_uses_type_params(texpr: &TypeExpr, type_params: &[String]) -> bool {
    match texpr {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } | TypeExpr::Qualified { name, .. } => {
            type_params.contains(name)
        }
        TypeExpr::App { args, .. } => {
            args.iter().any(|a| type_expr_uses_type_params(a, type_params))
        }
        _ => false,
    }
}

/// Compile a library module (no main function required).
fn compile_library_module(
    typed_module: &TypedModule,
    class_name: &str,
    global_sum_types: &HashMap<String, String>,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    let empty_map = HashMap::new();
    compile_module_inner(typed_module, class_name, false, &empty_map, global_sum_types)
}

/// Qualify a type name from a module's perspective, using its type_provenance and module_path.
fn qualify_type_for(module: &TypedModule, bare_name: &str) -> String {
    let source = module.type_provenance.get(bare_name).map(String::as_str)
        .or(module.module_path.as_deref());
    match source {
        Some(mod_path) => format!("{mod_path}/{bare_name}"),
        None => bare_name.to_string(),
    }
}

/// Compile all modules returned by the typechecker. The first module is the main module;
/// the rest are library modules that each get their own class.
pub fn compile_modules(
    typed_modules: &[TypedModule],
    main_class_name: &str,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    let mut all_classes = Vec::new();

    // Build instance class name map from all library modules
    let mut instance_class_map: HashMap<(String, String), ImportedInstanceInfo> = HashMap::new();
    for module in typed_modules {
        if module.module_path.is_some() {
            for inst in &module.instance_defs {
                let builtin_types = ["Int", "Float", "Bool", "String"];
                if builtin_types.contains(&inst.target_type_name.as_str()) { continue; }
                let q_trait = qualify_type_for(module, &inst.trait_name);
                let class_name = format!("{}$${}", q_trait, inst.target_type_name);
                instance_class_map.insert(
                    (inst.trait_name.clone(), inst.target_type_name.clone()),
                    ImportedInstanceInfo {
                        class_name,
                        target_type: inst.target_type.clone(),
                        requirements: dict_requirements_for_instance(
                            &inst.type_var_ids,
                            &inst.constraints,
                            &inst.subdict_traits,
                        ),
                    },
                );
            }
        }
    }

    // Build global sum type map: bare_name → qualified_name (for cross-module references)
    // Detect collisions when two different library modules define the same bare name.
    let mut global_sum_types: HashMap<String, String> = HashMap::new();
    for module in typed_modules {
        for (sum_name, _, _) in &module.sum_decls {
            let qualified = qualify_type_for(module, sum_name);
            match global_sum_types.entry(sum_name.clone()) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    // Only error when two distinct qualified names collide
                    // (bare == qualified means it's the main module, which shadows imports)
                    let existing = e.get();
                    if existing != &qualified
                        && existing != sum_name
                        && qualified != *sum_name
                    {
                        return Err(CodegenError::TypeError(format!(
                            "sum type name collision: '{}' defined as both '{}' and '{}'",
                            sum_name, existing, qualified
                        )));
                    }
                }
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(qualified);
                }
            }
        }
    }

    // Compile all library modules
    for module in typed_modules {
        if let Some(path) = &module.module_path {
            let classes = compile_library_module(module, path, &global_sum_types)?;
            all_classes.extend(classes);
        }
    }

    // Compile main module with instance map
    for module in typed_modules {
        if module.module_path.is_none() {
            let classes = compile_module_inner(module, main_class_name, true, &instance_class_map, &global_sum_types)?;
            all_classes.extend(classes);
        }
    }

    Ok(all_classes)
}

fn compile_module_inner(
    typed_module: &TypedModule,
    class_name: &str,
    is_main: bool,
    imported_instances: &HashMap<(String, String), ImportedInstanceInfo>,
    global_sum_types: &HashMap<String, String>,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    if is_main && !typed_module.functions.iter().any(|f| f.name == "main") {
        return Err(CodegenError::NoMainFunction);
    }

    let mut compiler = Compiler::new(class_name)?;
    compiler.auto_close = typed_module.auto_close.clone();
    compiler.types
        .class_descriptors
        .insert(compiler.builder.refs.object_class, "Ljava/lang/Object;".to_string());

    // Build field type registry and type param maps for struct field resolution
    let mut field_type_registry = type_registry::TypeRegistry::new();
    field_type_registry.register_builtins(&mut TypeVarGen::new());
    let mut struct_type_param_maps: HashMap<String, HashMap<String, krypton_typechecker::types::TypeVarId>> = HashMap::new();
    for (struct_name, type_params, ast_fields) in &typed_module.struct_decls {
        // Build type param map so parameterized records (e.g., Predicate[a, b])
        // can resolve their field types
        let mut gen = TypeVarGen::new();
        let type_param_map: HashMap<String, krypton_typechecker::types::TypeVarId> = type_params
            .iter()
            .map(|name| (name.clone(), gen.fresh()))
            .collect();
        let resolved_fields = ast_fields
            .iter()
            .map(|(_, texpr)| {
                type_registry::resolve_type_expr(
                    texpr,
                    &type_param_map,
                    &HashMap::new(),
                    &field_type_registry,
                    ResolutionContext::InternalDecl,
                    None,
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| CodegenError::TypeError(format!("type error: {e}")))?;
        struct_type_param_maps.insert(struct_name.clone(), type_param_map);
        field_type_registry
            .register_type(type_registry::TypeInfo {
                name: struct_name.clone(),
                type_params: vec![],
                type_param_vars: vec![],
                kind: type_registry::TypeKind::Record {
                    fields: ast_fields
                        .iter()
                        .map(|(name, _)| name.clone())
                        .zip(resolved_fields.into_iter())
                        .collect(),
                },
                is_prelude: false,
            })
            .map_err(|e| CodegenError::TypeError(format!("type error: {e}")))?;
    }

    // Phase 1: Register types
    compiler.register_extern_types(typed_module)?;
    let mut result_classes: Vec<(String, Vec<u8>)> = Vec::new();
    result_classes.extend(compiler.register_structs(typed_module, &field_type_registry, &struct_type_param_maps)?);
    result_classes.extend(compiler.register_sum_types(typed_module)?);

    // Register cross-module sum type references (class index only, no bytecode)
    for (bare_name, qualified_name) in global_sum_types {
        if !compiler.types.sum_type_info.contains_key(bare_name) {
            let class_index = compiler.cp.add_class(qualified_name)?;
            let desc = format!("L{qualified_name};");
            compiler.types.class_descriptors.insert(class_index, desc);
            compiler.types.extern_sum_class_indices.insert(bare_name.clone(), class_index);
        }
    }

    // Phase 2: Register FunN interfaces, Vec, traits, and instances
    compiler.register_fun_interfaces(typed_module)?;
    // Vec's class descriptor must exist before instances referencing Vec[T] are registered.
    compiler.register_vec()?;
    result_classes.extend(compiler.register_traits(typed_module)?);
    result_classes.extend(compiler.register_builtin_instances(typed_module)?);
    compiler.register_imported_instances(imported_instances)?;
    result_classes.extend(compiler.register_instance_defs(typed_module, class_name)?);

    // Phase 3: Register tuples and functions
    compiler.register_tuples(typed_module)?;
    compiler.register_functions(typed_module, compiler.this_class)?;

    // Phase 4: Compile function bodies and build class
    let extra_methods = compiler.compile_function_bodies(typed_module)?;
    if is_main {
        compiler.emit_main_wrapper()?;
    }

    let class_bytes = compiler.build_class(extra_methods, is_main)?;
    result_classes.push((class_name.to_string(), class_bytes));

    Ok(result_classes)
}

/// Generate a minimal valid `.class` file containing a no-op
/// `public static void main(String[])` method.
pub fn generate_empty_main(class_name: &str) -> Result<Vec<u8>, ristretto_classfile::Error> {
    let mut cp = ConstantPool::default();

    // Class refs
    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    // "Code" attribute name must be in the constant pool
    let code_utf8 = cp.add_utf8("Code")?;

    // Method ref for super constructor call
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;

    // Method name/descriptor UTF-8 entries
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8("()V")?;
    let main_name = cp.add_utf8("main")?;
    let main_desc = cp.add_utf8("([Ljava/lang/String;)V")?;

    // Default constructor: calls super.<init>()
    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 1,
            max_locals: 1,
            code: vec![
                Instruction::Aload_0,
                Instruction::Invokespecial(object_init),
                Instruction::Return,
            ],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    // main method: just returns
    let main_method = Method {
        access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
        name_index: main_name,
        descriptor_index: main_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 0,
            max_locals: 1,
            code: vec![Instruction::Return],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        methods: vec![constructor, main_method],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}
