//! Module compilation pipeline and JVM type mapping.

mod builder;
mod calls;
mod compiler;
mod data_class_gen;
mod intrinsics;
mod lambda;
mod registration;
mod trait_class_gen;

use std::collections::HashMap;

use krypton_ir::{TraitName, Type, TypeVarId};
use krypton_typechecker::typed_ast::TypedModule;
use ristretto_classfile::attributes::{Attribute, Instruction};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, FieldType, Method, MethodAccessFlags, Version,
};

pub use compiler::{CodegenError, CodegenErrorKind, JvmType};

use compiler::{Compiler, DictRequirement};
use krypton_typechecker::link_context::ModuleLinkView;
use krypton_typechecker::module_interface::ModulePath;

use krypton_typechecker::typed_ast::QualifiedName;

/// Extension trait for JVM-specific qualified name formatting.
trait JvmQualifiedName {
    /// Returns the slash-separated JVM class path form, e.g. "core/semigroup/Semigroup".
    fn jvm_qualified(&self) -> String;
}

impl JvmQualifiedName for QualifiedName {
    fn jvm_qualified(&self) -> String {
        format!("{}/{}", self.module_path, self.local_name)
    }
}

/// Java 21 class file version (major 65).
const JAVA_21: Version = Version::Java21 { minor: 0 };

#[derive(Clone)]
struct ImportedInstanceInfo {
    class_name: String,
    target_type: Type,
    requirements: Vec<DictRequirement>,
}

fn type_to_jvm_basic(ty: &Type) -> Result<JvmType, CodegenError> {
    match ty {
        Type::Int => Ok(JvmType::Long),
        Type::Float => Ok(JvmType::Double),
        Type::Bool => Ok(JvmType::Int),
        Type::Unit => Ok(JvmType::Int),
        other => Err(CodegenError::TypeError(
            format!("cannot map type to JVM: {other:?}"),
            None,
        )),
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

/// Qualify a type name using the module's path (IR version).
/// Qualify a type name using the module's path.
fn qualify_ir(module_path: &str, bare_name: &str) -> String {
    format!("{module_path}/{bare_name}")
}

/// Check if a Type references any of the given type variable IDs (for JVM erasure).
fn type_references_var(ty: &Type, vars: &[TypeVarId]) -> bool {
    match ty {
        Type::Var(id) => vars.contains(id),
        Type::Named(_, args) => args.iter().any(|a| type_references_var(a, vars)),
        Type::App(ctor, args) => {
            type_references_var(ctor, vars) || args.iter().any(|a| type_references_var(a, vars))
        }
        Type::Fn(params, ret) => {
            params.iter().any(|p| type_references_var(p, vars)) || type_references_var(ret, vars)
        }
        Type::Tuple(elems) => elems.iter().any(|e| type_references_var(e, vars)),
        Type::Own(inner) => type_references_var(inner, vars),
        Type::Dict { target, .. } => type_references_var(target, vars),
        _ => false,
    }
}

/// Check if a Type contains any type variables.
fn type_has_vars(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Named(_, args) => args.iter().any(type_has_vars),
        Type::App(ctor, args) => type_has_vars(ctor) || args.iter().any(type_has_vars),
        Type::Fn(params, ret) => params.iter().any(type_has_vars) || type_has_vars(ret),
        Type::Tuple(elems) => elems.iter().any(type_has_vars),
        Type::Own(inner) => type_has_vars(inner),
        Type::Dict { target, .. } => type_has_vars(target),
        _ => false,
    }
}

/// Compile all modules returned by the typechecker. The first module is the main module;
/// the rest are library modules that each get their own class.
pub fn compile_modules(
    typed_modules: &[TypedModule],
    main_class_name: &str,
    link_ctx: &krypton_typechecker::link_context::LinkContext,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    let mut all_classes = Vec::new();

    // Lower each TypedModule to an IR Module.
    let mut ir_modules: Vec<krypton_ir::Module> = Vec::new();
    let mut typed_with_ir: Vec<(&TypedModule, usize)> = Vec::new(); // (typed_module, ir_index)
                                                                    // The first module is the root/main module; subsequent ones are library modules.
    let root_module_path = typed_modules
        .first()
        .map(|tm| tm.module_path.as_str())
        .unwrap_or("");
    for tm in typed_modules {
        let is_root = tm.module_path == root_module_path;
        // JVM class name: main_class_name for the entry module, module_path for libraries.
        let jvm_class_name = if is_root {
            main_class_name
        } else {
            &tm.module_path
        };
        let view = link_ctx
            .view_for(&krypton_typechecker::module_interface::ModulePath::new(&tm.module_path))
            .unwrap_or_else(|| {
                panic!("ICE: no LinkContext view for module '{}'", tm.module_path)
            });
        let ir = krypton_ir::lower::lower_module(tm, jvm_class_name, &view).map_err(|e| {
            CodegenError::TypeError(
                format!("IR lowering error in module {jvm_class_name}: {e}"),
                None,
            )
        })?;
        let idx = ir_modules.len();
        ir_modules.push(ir);
        typed_with_ir.push((tm, idx));
    }

    // Compile each module independently — each module builds its own instance map
    // from its local instances + imported_instances metadata.
    for &(typed_module, ir_idx) in &typed_with_ir {
        let ir_module = &ir_modules[ir_idx];
        let is_entry = ir_module.module_path.as_str() == root_module_path;
        let class_name = if is_entry {
            main_class_name
        } else {
            ir_module.module_path.as_str()
        };
        let view = link_ctx
            .view_for(&ModulePath::new(ir_module.module_path.as_str()))
            .unwrap_or_else(|| {
                panic!("ICE: no LinkContext view for module '{}'", ir_module.module_path)
            });
        let classes = compile_module_inner(ir_module, class_name, is_entry, &view).map_err(|e| {
            if let Some(s) = &typed_module.module_source {
                return e.with_source(typed_module.module_path.clone(), s.clone());
            }
            e
        })?;
        all_classes.extend(classes);
    }

    Ok(all_classes)
}

fn compile_module_inner(
    ir_module: &krypton_ir::Module,
    class_name: &str,
    is_main: bool,
    link_view: &ModuleLinkView<'_>,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    if is_main && !ir_module.functions.iter().any(|f| f.name == "main") {
        return Err(CodegenError::NoMainFunction());
    }

    let mut compiler = Compiler::new(class_name, link_view)?;
    compiler.types.class_descriptors.insert(
        compiler.builder.refs.object_class,
        "Ljava/lang/Object;".to_string(),
    );

    // Phase 1: Register types — local first, then imported metadata from link view.
    let module_path = ir_module.module_path.as_str();
    compiler.register_extern_types_ir(ir_module)?;
    compiler.register_imported_extern_types(module_path)?;
    compiler.register_imported_structs_from_metadata(module_path)?;
    compiler.register_imported_sum_types_from_metadata(module_path)?;

    let mut result_classes: Vec<(String, Vec<u8>)> = Vec::new();
    result_classes.extend(compiler.register_structs_ir(ir_module)?);
    result_classes.extend(compiler.register_sum_types_ir(ir_module)?);

    // Phase 2: Register FunN interfaces, Vec, traits, and instances
    compiler.register_fun_interfaces_ir(ir_module)?;
    compiler.register_vec()?;
    result_classes.extend(compiler.register_traits_ir(ir_module)?);
    result_classes.extend(compiler.register_builtin_instances_ir(ir_module)?);

    // Build instance map from local + imported instances
    let instance_class_map = build_instance_class_map(ir_module, link_view);
    compiler.register_imported_instances(&instance_class_map)?;
    result_classes.extend(compiler.register_instance_defs_ir(ir_module, class_name)?);

    // Phase 3: Register tuples and functions
    compiler.register_tuples_ir(ir_module)?;
    compiler.register_functions_ir(ir_module, compiler.this_class)?;

    // Phase 4: Compile function bodies from IR
    let extra_methods = compiler.compile_function_bodies_ir(ir_module)?;
    if is_main {
        compiler.emit_main_wrapper()?;
    }

    let class_bytes = compiler.build_class(extra_methods, is_main)?;
    result_classes.push((class_name.to_string(), class_bytes));

    Ok(result_classes)
}

/// Build instance class map from a module's local + imported instances.
fn build_instance_class_map(
    ir_module: &krypton_ir::Module,
    link_view: &ModuleLinkView<'_>,
) -> HashMap<(TraitName, Type), ImportedInstanceInfo> {
    let mut map: HashMap<(TraitName, Type), ImportedInstanceInfo> = HashMap::new();
    let intrinsic_registry = intrinsics::IntrinsicRegistry::new();

    // Local non-imported instances
    for inst in &ir_module.instances {
        if inst.is_imported {
            continue;
        }
        if intrinsic_registry
            .get(&inst.trait_name.local_name, &inst.target_type_name)
            .is_some()
        {
            continue;
        }
        let class_name = format!(
            "{}/{}$${}",
            ir_module.module_path.as_str(), inst.trait_name.local_name, inst.target_type_name
        );
        let requirements: Vec<DictRequirement> = inst
            .sub_dict_requirements
            .iter()
            .map(|(trait_name, type_var)| DictRequirement {
                trait_name: trait_name.clone(),
                type_var: *type_var,
            })
            .collect();
        map.insert(
            (inst.trait_name.clone(), inst.target_type.clone()),
            ImportedInstanceInfo {
                class_name,
                target_type: inst.target_type.clone(),
                requirements,
            },
        );
    }

    // Imported instances from link view
    for (path, inst) in link_view.all_instances() {
        if path.as_str() == ir_module.module_path.as_str() { continue; }
        if inst.is_intrinsic {
            continue;
        }
        if intrinsic_registry
            .get(&inst.trait_name.local_name, &inst.target_type_name)
            .is_some()
        {
            continue;
        }
        let class_name = format!(
            "{}/{}$${}",
            path.as_str(), inst.trait_name.local_name, inst.target_type_name
        );
        let target_type: krypton_ir::Type = inst.target_type.clone().into();
        let requirements: Vec<DictRequirement> = inst
            .constraints
            .iter()
            .filter_map(|c| {
                inst.type_var_ids.get(&c.type_var).map(|&id| DictRequirement {
                    trait_name: c.trait_name.clone(),
                    type_var: id,
                })
            })
            .collect();
        map.insert(
            (inst.trait_name.clone(), target_type.clone()),
            ImportedInstanceInfo {
                class_name,
                target_type,
                requirements,
            },
        );
    }

    map
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
