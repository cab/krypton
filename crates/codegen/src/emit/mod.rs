mod compiler;
mod class_gen;

use std::collections::HashMap;

use krypton_parser::ast::{Decl, Module, TypeDeclKind, TypeExpr};
use krypton_typechecker::infer::infer_module;
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{Attribute, Instruction, VerificationType};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, FieldType, Method,
    MethodAccessFlags, Version,
};

pub use compiler::{CodegenError, JvmType};

use compiler::{
    Compiler, FunctionInfo, StructInfo, VariantInfo, SumTypeInfo, TupleInfo, TraitDispatchInfo,
    InstanceSingletonInfo, VecInfo,
};
use class_gen::{
    generate_struct_class, generate_sealed_interface_class, generate_variant_class,
    generate_fun_interface, generate_trait_interface_class, generate_instance_class,
    generate_builtin_show_instance_class, generate_parameterized_instance_class,
};

/// Java 21 class file version (major 65).
const JAVA_21: Version = Version::Java21 { minor: 0 };

/// Extract the type name from a Type for instance lookup.
fn type_to_name(ty: &Type) -> String {
    match ty {
        Type::Named(name, _) => name.clone(),
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Own(inner) => type_to_name(inner),
        other => format!("{other:?}"),
    }
}

fn type_to_jvm_basic(ty: &Type) -> Result<JvmType, CodegenError> {
    match ty {
        Type::Int => Ok(JvmType::Long),
        Type::Float => Ok(JvmType::Double),
        Type::Bool => Ok(JvmType::Int),
        Type::String => Ok(JvmType::Ref),
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
        JvmType::Ref => "Ljava/lang/String;".to_string(),
        JvmType::StructRef(_) => unreachable!("StructRef descriptor handled by caller"),
    }
}

fn jvm_type_to_base_field_type(ty: JvmType) -> FieldType {
    match ty {
        JvmType::Long => FieldType::Base(ristretto_classfile::BaseType::Long),
        JvmType::Double => FieldType::Base(ristretto_classfile::BaseType::Double),
        JvmType::Int => FieldType::Base(ristretto_classfile::BaseType::Boolean),
        JvmType::Ref => FieldType::Object("java/lang/String".to_string()),
        JvmType::StructRef(_) => unreachable!("StructRef field type handled by caller"),
    }
}

/// Check if a function name is a compiler intrinsic.
fn is_intrinsic(name: &str) -> bool {
    matches!(name, "panic")
}

/// Map a TypeExpr to a JvmType (for struct field declarations in AST).
fn type_expr_to_jvm(texpr: &TypeExpr) -> Result<JvmType, CodegenError> {
    match texpr {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => match name.as_str() {
            "Int" => Ok(JvmType::Long),
            "Float" => Ok(JvmType::Double),
            "Bool" => Ok(JvmType::Int),
            "String" => Ok(JvmType::Ref),
            "Unit" => Ok(JvmType::Int),
            _ => Err(CodegenError::TypeError(format!(
                "cannot map type expr to JVM: {name}"
            ))),
        },
        _ => Err(CodegenError::TypeError(format!(
            "unsupported type expr in struct field: {texpr:?}"
        ))),
    }
}

fn type_expr_uses_type_params(texpr: &TypeExpr, type_params: &[String]) -> bool {
    match texpr {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => {
            type_params.contains(name)
        }
        TypeExpr::App { args, .. } => {
            args.iter().any(|a| type_expr_uses_type_params(a, type_params))
        }
        _ => false,
    }
}

/// Recursively collect all tuple arities from a Type.
fn collect_tuple_arities(ty: &Type, arities: &mut std::collections::HashSet<usize>) {
    match ty {
        Type::Tuple(elems) => {
            arities.insert(elems.len());
            for e in elems {
                collect_tuple_arities(e, arities);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_tuple_arities(p, arities);
            }
            collect_tuple_arities(ret, arities);
        }
        Type::Named(_, args) => {
            for a in args {
                collect_tuple_arities(a, arities);
            }
        }
        Type::Own(inner) => collect_tuple_arities(inner, arities),
        _ => {}
    }
}

/// Recursively collect all tuple arities from a TypedExpr tree.
fn collect_tuple_arities_expr(expr: &krypton_typechecker::typed_ast::TypedExpr, arities: &mut std::collections::HashSet<usize>) {
    use krypton_typechecker::typed_ast::TypedExprKind;
    collect_tuple_arities(&expr.ty, arities);
    match &expr.kind {
        TypedExprKind::Tuple(elems) => {
            arities.insert(elems.len());
            for e in elems {
                collect_tuple_arities_expr(e, arities);
            }
        }
        TypedExprKind::Let { value, body, .. } | TypedExprKind::LetPattern { value, body, .. } => {
            collect_tuple_arities_expr(value, arities);
            if let Some(b) = body {
                collect_tuple_arities_expr(b, arities);
            }
        }
        TypedExprKind::App { func, args } => {
            collect_tuple_arities_expr(func, arities);
            for a in args { collect_tuple_arities_expr(a, arities); }
        }
        TypedExprKind::If { cond, then_, else_ } => {
            collect_tuple_arities_expr(cond, arities);
            collect_tuple_arities_expr(then_, arities);
            collect_tuple_arities_expr(else_, arities);
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs { collect_tuple_arities_expr(e, arities); }
        }
        TypedExprKind::Match { scrutinee, arms } => {
            collect_tuple_arities_expr(scrutinee, arities);
            for arm in arms { collect_tuple_arities_expr(&arm.body, arities); }
        }
        TypedExprKind::Lambda { body, .. } => {
            collect_tuple_arities_expr(body, arities);
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            collect_tuple_arities_expr(lhs, arities);
            collect_tuple_arities_expr(rhs, arities);
        }
        TypedExprKind::UnaryOp { operand, .. } => {
            collect_tuple_arities_expr(operand, arities);
        }
        TypedExprKind::FieldAccess { expr, .. } => {
            collect_tuple_arities_expr(expr, arities);
        }
        TypedExprKind::StructUpdate { base, fields } => {
            collect_tuple_arities_expr(base, arities);
            for (_, e) in fields { collect_tuple_arities_expr(e, arities); }
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields { collect_tuple_arities_expr(e, arities); }
        }
        TypedExprKind::Recur(args) => {
            for a in args { collect_tuple_arities_expr(a, arities); }
        }
        TypedExprKind::QuestionMark { expr, .. } => {
            collect_tuple_arities_expr(expr, arities);
        }
        TypedExprKind::VecLit(elems) => {
            for e in elems { collect_tuple_arities_expr(e, arities); }
        }
        _ => {}
    }
}

/// Compile a module to JVM bytecode. Returns a list of (class_name, bytes) pairs.
#[tracing::instrument(skip(module), fields(class = %class_name))]
pub fn compile_module(
    module: &Module,
    class_name: &str,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    // Find the main function
    let _main_fn = module
        .decls
        .iter()
        .find_map(|decl| match decl {
            Decl::DefFn(f) if f.name == "main" => Some(f),
            _ => None,
        })
        .ok_or(CodegenError::NoMainFunction)?;

    let (mut compiler, this_class, object_class) = Compiler::new(class_name)?;

    // Register java/lang/Object in class_descriptors for erased type variables
    compiler.types
        .class_descriptors
        .insert(object_class, "Ljava/lang/Object;".to_string());

    // Run the typechecker to get typed module with function types and typed bodies
    let typed_module = infer_module(module).map_err(|e| {
        CodegenError::TypeError(format!("{e:?}"))
    })?;
    let type_info = &typed_module.fn_types;

    // Collect struct declarations from AST
    let struct_decls: Vec<_> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::DefType(td) => match &td.kind {
                TypeDeclKind::Record { fields } => Some((td.name.clone(), fields.clone())),
                _ => None,
            },
            _ => None,
        })
        .collect();

    // Process struct types: register in compiler, generate class files
    let mut result_classes: Vec<(String, Vec<u8>)> = Vec::new();
    for (struct_name, ast_fields) in &struct_decls {
        // Resolve field types to JvmTypes
        let jvm_fields: Vec<(String, JvmType)> = ast_fields
            .iter()
            .map(|(fname, texpr)| {
                // For struct-typed fields, we need to check if it refers to a known struct
                let jt = match texpr {
                    TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => {
                        if let Some(si) = compiler.types.struct_info.get(name.as_str()) {
                            JvmType::StructRef(si.class_index)
                        } else {
                            type_expr_to_jvm(texpr)?
                        }
                    }
                    _ => type_expr_to_jvm(texpr)?,
                };
                Ok((fname.clone(), jt))
            })
            .collect::<Result<_, CodegenError>>()?;

        // Register the struct class in main class's constant pool
        let class_index = compiler.cp.add_class(struct_name)?;
        let class_desc = format!("L{struct_name};");
        compiler.types
            .class_descriptors
            .insert(class_index, class_desc.clone());

        // Add constructor methodref in main class's cpool
        let mut ctor_desc = String::from("(");
        for (_, jt) in &jvm_fields {
            ctor_desc.push_str(&compiler.types.jvm_type_descriptor(*jt));
        }
        ctor_desc.push_str(")V");
        let constructor_ref =
            compiler
                .cp
                .add_method_ref(class_index, "<init>", &ctor_desc)?;

        // Add accessor methodrefs in main class's cpool
        let mut accessor_refs = HashMap::new();
        for (fname, jt) in &jvm_fields {
            let ret_desc = compiler.types.jvm_type_descriptor(*jt);
            let method_desc = format!("(){ret_desc}");
            let accessor_ref =
                compiler
                    .cp
                    .add_method_ref(class_index, fname, &method_desc)?;
            accessor_refs.insert(fname.clone(), accessor_ref);
        }

        compiler.types.struct_info.insert(
            struct_name.clone(),
            StructInfo {
                class_index,
                class_name: struct_name.clone(),
                fields: jvm_fields.clone(),
                constructor_ref,
                accessor_refs,
            },
        );

        // Generate the struct class file
        let struct_bytes =
            generate_struct_class(struct_name, &jvm_fields, &compiler.types.class_descriptors)?;
        result_classes.push((struct_name.clone(), struct_bytes));
    }

    // Collect sum type declarations from AST
    let mut sum_decls: Vec<_> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::DefType(td) => match &td.kind {
                TypeDeclKind::Sum { variants } => {
                    Some((td.name.clone(), td.type_params.clone(), variants.clone()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect();

    // Inject prelude sum types not shadowed by user declarations
    {
        let user_type_names: std::collections::HashSet<String> =
            sum_decls.iter().map(|(name, _, _)| name.clone()).collect();
        for &module_path in krypton_typechecker::stdlib_loader::StdlibLoader::PRELUDE_MODULES {
            if let Some(source) = krypton_typechecker::stdlib_loader::StdlibLoader::get_source(module_path) {
                let (stdlib_module, _) = krypton_parser::parser::parse(source);
                for decl in stdlib_module.decls {
                    if let Decl::DefType(td) = decl {
                        if let TypeDeclKind::Sum { variants } = td.kind {
                            if !user_type_names.contains(&td.name) {
                                sum_decls.push((td.name, td.type_params, variants));
                            }
                        }
                    }
                }
            }
        }
    }

    // Process sum types: generate sealed interface + variant classes
    for (sum_name, type_params, variants) in &sum_decls {
        // Register interface class in main cpool
        let interface_class_index = compiler.cp.add_class(sum_name)?;
        let interface_desc = format!("L{sum_name};");
        compiler.types
            .class_descriptors
            .insert(interface_class_index, interface_desc);

        let mut variant_infos = HashMap::new();
        let variant_names: Vec<String> = variants.iter().map(|v| format!("{}${}", sum_name, v.name)).collect();

        for variant in variants {
            // Resolve fields: type params are erased to Object
            let fields: Vec<(String, JvmType, bool)> = variant
                .fields
                .iter()
                .enumerate()
                .map(|(i, texpr)| {
                    let field_name = format!("field{i}");
                    let is_erased = type_expr_uses_type_params(texpr, type_params);
                    let jt = if is_erased {
                        JvmType::Ref // erased to Object
                    } else {
                        type_expr_to_jvm(texpr)?
                    };
                    Ok((field_name, jt, is_erased))
                })
                .collect::<Result<_, CodegenError>>()?;

            // Register variant class in main cpool
            let qualified_name = format!("{}${}", sum_name, variant.name);
            let variant_class_index = compiler.cp.add_class(&qualified_name)?;
            let variant_desc = format!("L{qualified_name};");
            compiler.types
                .class_descriptors
                .insert(variant_class_index, variant_desc);

            // Build constructor descriptor — erased fields use Ljava/lang/Object;
            let mut ctor_desc = String::from("(");
            for (_, jt, is_erased) in &fields {
                if *is_erased {
                    ctor_desc.push_str("Ljava/lang/Object;");
                } else {
                    ctor_desc.push_str(&jvm_type_to_field_descriptor(*jt));
                }
            }
            ctor_desc.push_str(")V");

            let constructor_ref = compiler.cp.add_method_ref(
                variant_class_index,
                "<init>",
                &ctor_desc,
            )?;

            // Add field refs to main cpool for pattern matching getfield
            let mut main_field_refs = Vec::new();
            for (fname, jt, is_erased) in &fields {
                let fdesc = if *is_erased {
                    "Ljava/lang/Object;".to_string()
                } else {
                    jvm_type_to_field_descriptor(*jt)
                };
                let fr = compiler.cp.add_field_ref(variant_class_index, fname, &fdesc)?;
                main_field_refs.push(fr);
            }

            compiler.types
                .variant_to_sum
                .insert(variant.name.clone(), sum_name.clone());

            variant_infos.insert(
                variant.name.clone(),
                VariantInfo {
                    class_index: variant_class_index,
                    class_name: qualified_name.clone(),
                    fields: fields.clone(),
                    constructor_ref,
                    field_refs: main_field_refs,
                },
            );

            // Generate variant class file
            let variant_bytes =
                generate_variant_class(&qualified_name, sum_name, &variant.name, &fields)?;
            result_classes.push((qualified_name.clone(), variant_bytes));
        }

        compiler.types.sum_type_info.insert(
            sum_name.clone(),
            SumTypeInfo {
                interface_class_index,
                variants: variant_infos,
            },
        );

        // Generate sealed interface class file
        let variant_name_refs: Vec<&str> = variant_names.iter().map(|s| s.as_str()).collect();
        let interface_bytes = generate_sealed_interface_class(sum_name, &variant_name_refs)?;
        result_classes.push((sum_name.clone(), interface_bytes));
    }

    // Pre-scan for function-typed params so we can register FunN interfaces first
    for (name, scheme) in type_info.iter() {
        if let Type::Fn(param_tys, _) = &scheme.ty {
            if compiler.types.struct_info.contains_key(name)
                || compiler.types.variant_to_sum.contains_key(name)
            {
                continue;
            }
            for pt in param_tys {
                if let Type::Fn(inner_params, _) = pt {
                    let arity = inner_params.len() as u8;
                    compiler.lambda.ensure_fun_interface(arity, &mut compiler.cp, &mut compiler.types.class_descriptors)?;
                }
            }
        }
    }

    // Process trait definitions: generate interface classes
    compiler.traits.trait_method_map = typed_module.trait_method_map.clone();
    compiler.traits.fn_constraints = typed_module.fn_constraints.clone();

    for trait_def in &typed_module.trait_defs {
        let interface_bytes = generate_trait_interface_class(&trait_def.name, &trait_def.methods)?;
        result_classes.push((trait_def.name.clone(), interface_bytes));

        // Register interface class in main cpool
        let iface_class = compiler.cp.add_class(&trait_def.name)?;
        compiler.types.class_descriptors.insert(iface_class, format!("L{};", trait_def.name));

        // Register interface method refs in main cpool
        let mut method_refs = HashMap::new();
        for (method_name, param_count) in &trait_def.methods {
            let mut desc = String::from("(");
            for _ in 0..*param_count {
                desc.push_str("Ljava/lang/Object;");
            }
            desc.push_str(")Ljava/lang/Object;");
            let mref = compiler.cp.add_interface_method_ref(iface_class, method_name, &desc)?;
            method_refs.insert(method_name.clone(), mref);
        }

        compiler.traits.trait_dispatch.insert(trait_def.name.clone(), TraitDispatchInfo {
            interface_class: iface_class,
            method_refs,
        });
    }

    // Generate built-in Show instance classes for primitive types
    {
        let show_primitives = [
            ("Show$Int", "Int", "(J)Ljava/lang/String;", "java/lang/Long", "toString"),
            ("Show$Float", "Float", "(D)Ljava/lang/String;", "java/lang/Double", "toString"),
            ("Show$Bool", "Bool", "(Z)Ljava/lang/String;", "java/lang/Boolean", "toString"),
            ("Show$String", "String", "(Ljava/lang/String;)Ljava/lang/String;", "", ""),
        ];

        for (show_class_name, type_name, _static_desc, _box_class, _method_name) in &show_primitives {
            if compiler.traits.trait_dispatch.contains_key("Show") {
                let show_bytes = generate_builtin_show_instance_class(show_class_name, type_name)?;
                result_classes.push((show_class_name.to_string(), show_bytes));

                let inst_class_idx = compiler.cp.add_class(show_class_name)?;
                let inst_desc = format!("L{show_class_name};");
                compiler.types.class_descriptors.insert(inst_class_idx, inst_desc.clone());
                let instance_field_ref = compiler.cp.add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;
                compiler.traits.instance_singletons.insert(
                    ("Show".to_string(), type_name.to_string()),
                    InstanceSingletonInfo { instance_field_ref },
                );
            }
        }
    }

    // Process instance definitions: generate singleton/parameterized classes
    for instance_def in &typed_module.instance_defs {
        let instance_class_name = format!("{}${}", instance_def.trait_name, instance_def.target_type_name);

        // Collect method info for the instance class
        let mut method_info = Vec::new();
        let mut param_jvm_types_map: HashMap<String, Vec<JvmType>> = HashMap::new();
        let mut return_jvm_types_map: HashMap<String, JvmType> = HashMap::new();
        let mut param_class_names_map: HashMap<String, Vec<Option<String>>> = HashMap::new();

        for (method_name, qualified_name) in &instance_def.qualified_method_names {
            // Look up the qualified method's type from fn_types
            if let Some((_, scheme)) = typed_module.fn_types.iter().find(|(n, _)| n == qualified_name) {
                if let Type::Fn(param_tys, ret_ty) = &scheme.ty {
                    let param_jvm: Vec<JvmType> = param_tys.iter()
                        .map(|t| compiler.type_to_jvm(t))
                        .collect::<Result<_, _>>()?;
                    let ret_jvm = compiler.type_to_jvm(ret_ty)?;
                    // Build the static method descriptor, prepending dict params if constrained
                    let constraint_traits = typed_module.fn_constraints.get(qualified_name).cloned().unwrap_or_default();
                    let mut all_param_jvm = Vec::new();
                    for _ in &constraint_traits {
                        all_param_jvm.push(JvmType::StructRef(compiler.refs.object_class));
                    }
                    all_param_jvm.extend(param_jvm.iter().copied());
                    let static_desc = compiler.types.build_descriptor(&all_param_jvm, ret_jvm);
                    // Collect class names for checkcast in bridge methods
                    let class_names: Vec<Option<String>> = param_tys.iter().map(|t| {
                        match t {
                            Type::Named(name, _) => Some(name.clone()),
                            _ => None,
                        }
                    }).collect();
                    param_class_names_map.insert(method_name.clone(), class_names);
                    param_jvm_types_map.insert(method_name.clone(), param_jvm);
                    return_jvm_types_map.insert(method_name.clone(), ret_jvm);
                    method_info.push((method_name.clone(), qualified_name.clone(), param_tys.len(), static_desc));
                }
            }
        }

        if instance_def.subdict_traits.is_empty() {
            // Simple singleton instance
            let instance_bytes = generate_instance_class(
                &instance_class_name,
                &instance_def.trait_name,
                class_name,
                &method_info,
                &param_jvm_types_map,
                &return_jvm_types_map,
                &param_class_names_map,
            )?;
            result_classes.push((instance_class_name.clone(), instance_bytes));

            // Register INSTANCE field ref in main cpool
            let inst_class_idx = compiler.cp.add_class(&instance_class_name)?;
            let inst_desc = format!("L{instance_class_name};");
            compiler.types.class_descriptors.insert(inst_class_idx, inst_desc.clone());
            let instance_field_ref = compiler.cp.add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;

            compiler.traits.instance_singletons.insert(
                (instance_def.trait_name.clone(), instance_def.target_type_name.clone()),
                InstanceSingletonInfo { instance_field_ref },
            );
        } else {
            // Parameterized instance — needs subdictionaries
            let instance_bytes = generate_parameterized_instance_class(
                &instance_class_name,
                &instance_def.trait_name,
                class_name,
                &method_info,
                &param_jvm_types_map,
                &return_jvm_types_map,
                &param_class_names_map,
                instance_def.subdict_traits.len(),
            )?;
            result_classes.push((instance_class_name.clone(), instance_bytes));

            // Register class in main cpool (no INSTANCE field — constructed on demand)
            let inst_class_idx = compiler.cp.add_class(&instance_class_name)?;
            let inst_desc = format!("L{instance_class_name};");
            compiler.types.class_descriptors.insert(inst_class_idx, inst_desc.clone());

            compiler.traits.parameterized_instances.insert(
                (instance_def.trait_name.clone(), instance_def.target_type_name.clone()),
                instance_def.subdict_traits.clone(),
            );
        }
    }

    // Scan for tuple arities used in the typed module and register TupleN classes
    {
        let mut tuple_arities = std::collections::HashSet::new();
        for (_, scheme) in type_info.iter() {
            collect_tuple_arities(&scheme.ty, &mut tuple_arities);
        }
        for typed_fn in &typed_module.functions {
            collect_tuple_arities_expr(&typed_fn.body, &mut tuple_arities);
        }
        for arity in tuple_arities {
            let class_name = format!("krypton/runtime/Tuple{arity}");
            let class_index = compiler.cp.add_class(&class_name)?;
            let class_desc = format!("Lkrypton/runtime/Tuple{arity};");
            compiler.types.class_descriptors.insert(class_index, class_desc);

            // Constructor: (Object, Object, ...)V
            let mut ctor_desc = String::from("(");
            for _ in 0..arity {
                ctor_desc.push_str("Ljava/lang/Object;");
            }
            ctor_desc.push_str(")V");
            let constructor_ref = compiler.cp.add_method_ref(class_index, "<init>", &ctor_desc)?;

            // Accessor method refs for _0(), _1(), etc. (all return Ljava/lang/Object;)
            let mut field_refs = Vec::new();
            for i in 0..arity {
                let accessor_name = format!("_{i}");
                let accessor_desc = "()Ljava/lang/Object;".to_string();
                let mr = compiler.cp.add_method_ref(class_index, &accessor_name, &accessor_desc)?;
                field_refs.push(mr);
            }

            compiler.types.tuple_info.insert(arity, TupleInfo {
                class_index,
                constructor_ref,
                field_refs,
            });
        }
    }

    // Register KryptonArray (Vec backing class)
    {
        let ka_class = compiler.cp.add_class("krypton/runtime/KryptonArray")?;
        let ka_init = compiler.cp.add_method_ref(ka_class, "<init>", "(I)V")?;
        let ka_set = compiler.cp.add_method_ref(ka_class, "set", "(ILjava/lang/Object;)V")?;
        let ka_freeze = compiler.cp.add_method_ref(ka_class, "freeze", "()V")?;
        compiler.types.class_descriptors.insert(ka_class, "Lkrypton/runtime/KryptonArray;".to_string());
        compiler.vec_info = Some(VecInfo { class_index: ka_class, init_ref: ka_init, set_ref: ka_set, freeze_ref: ka_freeze });
    }

    // Register all functions (including main) in the function registry.
    // Skip constructor entries (they're handled as struct/variant constructors).
    for (name, scheme) in type_info.iter() {
        if let Type::Fn(param_tys, ret_ty) = &scheme.ty {
            // Skip if this is a struct constructor or variant constructor
            if compiler.types.struct_info.contains_key(name)
                || compiler.types.variant_to_sum.contains_key(name)
            {
                continue;
            }
            // For constrained functions, prepend dict params (one Object per trait constraint)
            let constraint_traits = compiler.traits.fn_constraints.get(name).cloned().unwrap_or_default();
            let mut all_param_types: Vec<JvmType> = Vec::new();
            for _ in &constraint_traits {
                all_param_types.push(JvmType::StructRef(compiler.refs.object_class));
            }
            let user_param_types: Vec<JvmType> = param_tys
                .iter()
                .map(|t| compiler.type_to_jvm(t))
                .collect::<Result<_, _>>()?;
            all_param_types.extend(user_param_types);
            let return_type = compiler.type_to_jvm(ret_ty)?;
            let jvm_name = if name == "main" {
                "krypton_main"
            } else {
                name.as_str()
            };
            let descriptor = compiler.types.build_descriptor(&all_param_types, return_type);
            let method_ref =
                compiler.cp.add_method_ref(this_class, jvm_name, &descriptor)?;
            compiler.types.functions.insert(
                name.clone(),
                FunctionInfo {
                    method_ref,
                    param_types: all_param_types,
                    return_type,
                    is_void: false,
                },
            );
            // Store TC types for detecting Fn-typed params in compile_function
            compiler.types.fn_tc_types.insert(
                name.clone(),
                (param_tys.clone(), (**ret_ty).clone()),
            );
        }
    }

    // Register extern functions so they can be called via invokestatic
    for ext in typed_module.extern_fns.iter().chain(typed_module.imported_extern_fns.iter()) {
        let jvm_class_name = ext.java_class.replace('.', "/");
        let extern_class = compiler.cp.add_class(&jvm_class_name)?;

        let mut param_jvm_types = Vec::new();
        let mut param_desc = String::from("(");
        for pt in &ext.param_types {
            match pt {
                Type::Int => {
                    param_jvm_types.push(JvmType::Long);
                    param_desc.push('J');
                }
                Type::Float => {
                    param_jvm_types.push(JvmType::Double);
                    param_desc.push('D');
                }
                Type::Bool => {
                    param_jvm_types.push(JvmType::Int);
                    param_desc.push('Z');
                }
                Type::String => {
                    param_jvm_types.push(JvmType::Ref);
                    param_desc.push_str("Ljava/lang/String;");
                }
                Type::Named(_, _) => {
                    param_jvm_types.push(JvmType::StructRef(compiler.refs.object_class));
                    param_desc.push_str("Ljava/lang/Object;");
                }
                other => {
                    return Err(CodegenError::TypeError(format!(
                        "unsupported extern param type: {other:?}"
                    )));
                }
            }
        }
        param_desc.push(')');

        let is_void = matches!(ext.return_type, Type::Unit);
        let (return_type, ret_desc) = if is_void {
            (JvmType::Int, "V".to_string())
        } else {
            match &ext.return_type {
                Type::Int => (JvmType::Long, "J".to_string()),
                Type::Float => (JvmType::Double, "D".to_string()),
                Type::Bool => (JvmType::Int, "Z".to_string()),
                Type::String => (JvmType::Ref, "Ljava/lang/String;".to_string()),
                Type::Named(_, _) => {
                    (JvmType::StructRef(compiler.refs.object_class), "Ljava/lang/Object;".to_string())
                }
                other => {
                    return Err(CodegenError::TypeError(format!(
                        "unsupported extern return type: {other:?}"
                    )));
                }
            }
        };

        let descriptor = format!("{param_desc}{ret_desc}");
        let method_ref = compiler.cp.add_method_ref(extern_class, &ext.name, &descriptor)?;

        compiler.types.functions.insert(
            ext.name.clone(),
            FunctionInfo {
                method_ref,
                param_types: param_jvm_types,
                return_type,
                is_void,
            },
        );
    }

    // Compile all functions (including main) as static methods using typed bodies
    let mut extra_methods = Vec::new();
    for typed_fn in &typed_module.functions {
        let mut method = compiler.compile_function(typed_fn)?;
        // Rename main → krypton_main in the method
        if typed_fn.name == "main" {
            let name_idx = compiler.cp.add_utf8("krypton_main")?;
            method.name_index = name_idx;
        }
        extra_methods.push(method);
    }

    // Build JVM main(String[])V — calls krypton_main and discards the result
    let main_info = compiler.types.functions.get("main").ok_or(CodegenError::NoMainFunction)?;
    let krypton_main_ref = main_info.method_ref;
    let main_return_type = main_info.return_type;

    compiler.reset_method_state();
    compiler.next_local = 1; // slot 0 = String[] args
    let string_arr_class = compiler.cp.add_class("[Ljava/lang/String;")?;
    compiler.frame.local_types = vec![VerificationType::Object {
        cpool_index: string_arr_class,
    }];

    // Call krypton_main
    compiler.emit(Instruction::Invokestatic(krypton_main_ref));
    compiler.push_jvm_type(main_return_type);

    // Discard the return value
    match main_return_type {
        JvmType::Long | JvmType::Double => {
            compiler.emit(Instruction::Pop2);
            compiler.frame.pop_type_n(2);
        }
        JvmType::Int | JvmType::Ref | JvmType::StructRef(_) => {
            compiler.emit(Instruction::Pop);
            compiler.frame.pop_type();
        }
    }

    compiler.emit(Instruction::Return);

    // Generate FunN interface class files
    let fun_arities: Vec<u8> = compiler.lambda.fun_classes.keys().copied().collect();
    for arity in fun_arities {
        let fun_bytes = generate_fun_interface(arity)?;
        result_classes.push((format!("Fun{arity}"), fun_bytes));
    }

    let main_bytes = compiler.build_class(this_class, object_class, extra_methods)?;
    result_classes.push((class_name.to_string(), main_bytes));

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
