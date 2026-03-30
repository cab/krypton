//! Module registration phases (types, traits, instances, functions).
//! All registration reads from `ir::Module`.

use std::collections::HashMap;

use krypton_ir::{TraitName, Type};
use ristretto_classfile::attributes::{Instruction, VerificationType};
use ristretto_classfile::Method;

use super::compiler::{
    CodegenError, Compiler, DictRequirement, FunctionInfo, InstanceSingletonInfo, JvmType,
    ParameterizedInstanceInfo, StructInfo, SumTypeInfo, TraitDispatchInfo, VariantField,
    VariantInfo, VecInfo,
};
use super::data_class_gen::{
    generate_sealed_interface_class, generate_struct_class, generate_variant_class,
};
use super::intrinsics;
use super::trait_class_gen::{
    generate_builtin_show_instance_class, generate_builtin_trait_instance_class,
    generate_instance_class, generate_parameterized_instance_class, generate_trait_interface_class,
};
use super::{
    jvm_type_to_field_descriptor, qualify_ir, type_has_vars, type_references_var,
    ImportedInstanceInfo, JvmQualifiedName,
};

fn name_to_builtin_type(name: &str) -> Type {
    match name {
        "Int" => Type::Int,
        "Float" => Type::Float,
        "Bool" => Type::Bool,
        "String" => Type::String,
        "Unit" => Type::Unit,
        other => unreachable!("unexpected builtin type name: {other}"),
    }
}

/// Map a `Type::Named` to its JVM type and descriptor fragment.
fn jvm_type_for_named(
    name: &str,
    args: &[Type],
    struct_info: &HashMap<String, StructInfo>,
    object_class: u16,
) -> (JvmType, String) {
    if args.is_empty() {
        if let Some(info) = struct_info.get(name) {
            (
                JvmType::StructRef(info.class_index),
                format!("L{};", info.class_name),
            )
        } else {
            (
                JvmType::StructRef(object_class),
                "Ljava/lang/Object;".to_string(),
            )
        }
    } else {
        (
            JvmType::StructRef(object_class),
            "Ljava/lang/Object;".to_string(),
        )
    }
}

fn jvm_descriptor(compiler: &Compiler, ty: JvmType) -> String {
    match ty {
        JvmType::StructRef(_) => compiler.types.jvm_type_descriptor(ty),
        other => jvm_type_to_field_descriptor(other),
    }
}

fn extern_param_info(compiler: &Compiler, ty: &Type) -> Result<(JvmType, String), CodegenError> {
    match ty {
        Type::Named(name, args) => {
            let (jvm, desc) = jvm_type_for_named(
                name,
                args,
                &compiler.types.struct_info,
                compiler.builder.refs.object_class,
            );
            Ok((jvm, desc))
        }
        Type::Own(inner) => extern_param_info(compiler, inner),
        other => {
            let jvm = compiler.type_to_jvm(other)?;
            Ok((jvm, jvm_descriptor(compiler, jvm)))
        }
    }
}

fn extern_return_info(
    compiler: &Compiler,
    ty: &Type,
    nullable: bool,
) -> Result<(JvmType, String, bool), CodegenError> {
    if nullable {
        let jvm = compiler.nullable_host_return_jvm(ty)?;
        return Ok((jvm, jvm_descriptor(compiler, jvm), false));
    }
    if matches!(ty, Type::Unit) {
        return Ok((JvmType::Int, "V".to_string(), true));
    }
    match ty {
        Type::Named(name, args) => {
            let (jvm, desc) = jvm_type_for_named(
                name,
                args,
                &compiler.types.struct_info,
                compiler.builder.refs.object_class,
            );
            Ok((jvm, desc, false))
        }
        Type::Own(inner) => extern_return_info(compiler, inner, false),
        other => {
            let jvm = compiler.type_to_jvm(other)?;
            Ok((jvm, jvm_descriptor(compiler, jvm), false))
        }
    }
}

impl<'link> Compiler<'link> {
    // -----------------------------------------------------------------------
    // Phase 1: Types
    // -----------------------------------------------------------------------

    pub(super) fn register_extern_types_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<(), CodegenError> {
        for ext in &ir_module.extern_types {
            let jvm_class = match &ext.target {
                krypton_ir::ExternTarget::Java { class } => class.replace('.', "/"),
                krypton_ir::ExternTarget::Js { .. } => continue,
            };
            let class_index = self.cp.add_class(&jvm_class)?;
            self.types
                .class_descriptors
                .insert(class_index, format!("L{jvm_class};"));
            self.types.struct_info.insert(
                ext.name.clone(),
                StructInfo {
                    class_index,
                    class_name: jvm_class,
                    fields: vec![],
                    constructor_ref: 0,
                    accessor_refs: HashMap::new(),
                },
            );
        }
        Ok(())
    }

    /// Resolve fields, register class/ctor/accessors in the constant pool, and insert StructInfo.
    fn register_struct_metadata(
        &mut self,
        struct_def: &krypton_ir::StructDef,
        qualified: &str,
    ) -> Result<(), CodegenError> {
        let jvm_fields: Vec<(String, JvmType)> = struct_def
            .fields
            .iter()
            .map(|(fname, ty)| {
                let jt = if type_references_var(ty, &struct_def.type_params) {
                    JvmType::StructRef(self.builder.refs.object_class)
                } else {
                    self.type_to_jvm(ty)?
                };
                Ok((fname.clone(), jt))
            })
            .collect::<Result<_, CodegenError>>()?;

        let class_index = self.cp.add_class(qualified)?;
        let class_desc = format!("L{qualified};");
        self.types.class_descriptors.insert(class_index, class_desc);

        let mut ctor_desc = String::from("(");
        for (_, jt) in &jvm_fields {
            ctor_desc.push_str(&self.types.jvm_type_descriptor(*jt));
        }
        ctor_desc.push_str(")V");
        let constructor_ref = self.cp.add_method_ref(class_index, "<init>", &ctor_desc)?;

        let mut accessor_refs = HashMap::new();
        for (fname, jt) in &jvm_fields {
            let ret_desc = self.types.jvm_type_descriptor(*jt);
            let method_desc = format!("(){ret_desc}");
            let accessor_ref = self.cp.add_method_ref(class_index, fname, &method_desc)?;
            accessor_refs.insert(fname.clone(), accessor_ref);
        }

        self.types.struct_info.insert(
            struct_def.name.clone(),
            StructInfo {
                class_index,
                class_name: qualified.to_string(),
                fields: jvm_fields,
                constructor_ref,
                accessor_refs,
            },
        );
        Ok(())
    }

    pub(super) fn register_structs_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        for struct_def in &ir_module.structs {
            let qualified = qualify_ir(ir_module.module_path.as_str(), &struct_def.name);
            self.register_struct_metadata(struct_def, &qualified)?;
            let info = &self.types.struct_info[&struct_def.name];
            let struct_bytes = generate_struct_class(
                &info.class_name,
                &info.fields,
                &self.types.class_descriptors,
            )?;
            result_classes.push((qualified, struct_bytes));
        }
        Ok(result_classes)
    }

    /// Register a single variant's metadata in the constant pool.
    fn register_variant_metadata(
        &mut self,
        variant: &krypton_ir::VariantDef,
        sum_def: &krypton_ir::SumTypeDef,
        qualified_sum: &str,
    ) -> Result<(String, String, VariantInfo), CodegenError> {
        let fields: Vec<VariantField> = variant
            .fields
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let name = format!("field{i}");
                let is_erased = type_references_var(ty, &sum_def.type_params);
                let jvm_type = if is_erased {
                    JvmType::StructRef(self.builder.refs.object_class)
                } else {
                    self.type_to_jvm(ty)?
                };
                Ok(VariantField {
                    name,
                    jvm_type,
                    is_erased,
                })
            })
            .collect::<Result<_, CodegenError>>()?;

        let qualified_variant = format!("{}${}", qualified_sum, variant.name);
        let variant_class_index = self.cp.add_class(&qualified_variant)?;
        let variant_desc = format!("L{qualified_variant};");
        self.types
            .class_descriptors
            .insert(variant_class_index, variant_desc);

        let mut ctor_desc = String::from("(");
        for f in &fields {
            if f.is_erased {
                ctor_desc.push_str("Ljava/lang/Object;");
            } else {
                ctor_desc.push_str(&self.types.jvm_type_descriptor(f.jvm_type));
            }
        }
        ctor_desc.push_str(")V");

        let constructor_ref = self
            .cp
            .add_method_ref(variant_class_index, "<init>", &ctor_desc)?;

        let mut field_refs = Vec::new();
        for f in &fields {
            let fdesc = if f.is_erased {
                "Ljava/lang/Object;".to_string()
            } else {
                self.types.jvm_type_descriptor(f.jvm_type)
            };
            let fr = self
                .cp
                .add_field_ref(variant_class_index, &f.name, &fdesc)?;
            field_refs.push(fr);
        }

        self.types
            .variant_to_sum
            .insert(variant.name.clone(), sum_def.name.clone());

        let vi = VariantInfo {
            class_index: variant_class_index,
            fields,
            constructor_ref,
            field_refs,
        };
        Ok((variant.name.clone(), qualified_variant, vi))
    }

    /// Register a sum type's sealed interface and all variant classes in the constant pool.
    /// Returns Vec<(variant_bare_name, qualified_variant_name)> for bytecode generation.
    fn register_sum_type_metadata(
        &mut self,
        sum_def: &krypton_ir::SumTypeDef,
        qualified_sum: &str,
    ) -> Result<Vec<(String, String)>, CodegenError> {
        let interface_class_index = self.cp.add_class(qualified_sum)?;
        let interface_desc = format!("L{qualified_sum};");
        self.types
            .class_descriptors
            .insert(interface_class_index, interface_desc);

        // Pre-register so recursive type references (e.g., List[a] = Cons(a, List[a]))
        // can resolve the type during variant field processing.
        self.types.sum_type_info.insert(
            sum_def.name.clone(),
            SumTypeInfo {
                interface_class_index,
                variants: HashMap::new(),
            },
        );

        let mut variant_infos = HashMap::new();
        let mut variant_pairs = Vec::new();

        for variant in &sum_def.variants {
            let (name, qualified, info) =
                self.register_variant_metadata(variant, sum_def, qualified_sum)?;
            variant_pairs.push((name.clone(), qualified));
            variant_infos.insert(name, info);
        }

        // Update with full variant info.
        self.types.sum_type_info.insert(
            sum_def.name.clone(),
            SumTypeInfo {
                interface_class_index,
                variants: variant_infos,
            },
        );

        Ok(variant_pairs)
    }

    pub(super) fn register_sum_types_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        for sum_def in &ir_module.sum_types {
            let qualified_sum = qualify_ir(ir_module.module_path.as_str(), &sum_def.name);
            let variant_pairs = self.register_sum_type_metadata(sum_def, &qualified_sum)?;

            let sum_info = &self.types.sum_type_info[&sum_def.name];
            for (variant_name, qualified_variant) in &variant_pairs {
                let vi = &sum_info.variants[variant_name];
                let variant_bytes = generate_variant_class(
                    qualified_variant,
                    &qualified_sum,
                    variant_name,
                    &vi.fields,
                    &self.types.class_descriptors,
                )?;
                result_classes.push((qualified_variant.clone(), variant_bytes));
            }

            let variant_name_refs: Vec<&str> =
                variant_pairs.iter().map(|(_, q)| q.as_str()).collect();
            let interface_bytes =
                generate_sealed_interface_class(&qualified_sum, &variant_name_refs)?;
            result_classes.push((qualified_sum, interface_bytes));
        }
        Ok(result_classes)
    }

    /// Register extern types from cross-module link view.
    pub(super) fn register_imported_extern_types(
        &mut self,
        module_path: &str,
    ) -> Result<(), CodegenError> {
        for (path, ext) in self.link_view.all_extern_types() {
            if path.as_str() == module_path { continue; }
            let jvm_class = match &ext.target {
                krypton_parser::ast::ExternTarget::Java => ext.host_module.replace('.', "/"),
                krypton_parser::ast::ExternTarget::Js => continue,
            };
            if self.types.struct_info.contains_key(&ext.krypton_name) {
                continue;
            }
            let class_index = self.cp.add_class(&jvm_class)?;
            self.types
                .class_descriptors
                .insert(class_index, format!("L{jvm_class};"));
            self.types.struct_info.insert(
                ext.krypton_name.clone(),
                StructInfo {
                    class_index,
                    class_name: jvm_class,
                    fields: vec![],
                    constructor_ref: 0,
                    accessor_refs: HashMap::new(),
                },
            );
        }
        Ok(())
    }

    /// Register struct types from cross-module link view.
    pub(super) fn register_imported_structs_from_metadata(
        &mut self,
        module_path: &str,
    ) -> Result<(), CodegenError> {
        use krypton_typechecker::module_interface::TypeSummaryKind;
        // Two-pass: pre-register class indices, then process fields.
        let mut to_process: Vec<(krypton_ir::StructDef, String)> = Vec::new();
        for (path, ts) in self.link_view.all_exported_types() {
            if path.as_str() == module_path { continue; }
            let TypeSummaryKind::Record { fields } = &ts.kind else { continue; };
            if self.types.struct_info.contains_key(&ts.name) {
                continue;
            }
            let qualified = format!("{}/{}", path.as_str(), ts.name);
            let class_index = self.cp.add_class(&qualified)?;
            let class_desc = format!("L{qualified};");
            self.types.class_descriptors.insert(class_index, class_desc);
            self.types.struct_info.insert(
                ts.name.clone(),
                StructInfo {
                    class_index,
                    class_name: qualified.clone(),
                    fields: vec![],
                    constructor_ref: 0,
                    accessor_refs: HashMap::new(),
                },
            );
            let ir_fields: Vec<(String, krypton_ir::Type)> = fields.iter()
                .map(|(name, ty)| (name.clone(), krypton_ir::Type::from(ty.clone())))
                .collect();
            to_process.push((
                krypton_ir::StructDef {
                    name: ts.name.clone(),
                    type_params: ts.type_param_vars.clone(),
                    fields: ir_fields,
                },
                qualified,
            ));
        }
        for (struct_def, qualified) in &to_process {
            self.register_struct_metadata(struct_def, qualified)?;
        }
        Ok(())
    }

    /// Register sum types from cross-module link view.
    pub(super) fn register_imported_sum_types_from_metadata(
        &mut self,
        module_path: &str,
    ) -> Result<(), CodegenError> {
        use krypton_typechecker::module_interface::TypeSummaryKind;
        // Two-pass registration: first pre-register all sum type interfaces so that
        // cross-references between types (e.g., Json's JArr(List[Json]) referencing
        // List) can be resolved during variant field processing.
        let mut to_process: Vec<(krypton_ir::SumTypeDef, String)> = Vec::new();
        for (path, ts) in self.link_view.all_exported_types() {
            if path.as_str() == module_path { continue; }
            let TypeSummaryKind::Sum { variants } = &ts.kind else { continue; };
            if self.types.sum_type_info.contains_key(&ts.name) {
                continue;
            }
            let qualified_sum = format!("{}/{}", path.as_str(), ts.name);
            let interface_class_index = self.cp.add_class(&qualified_sum)?;
            let interface_desc = format!("L{qualified_sum};");
            self.types
                .class_descriptors
                .insert(interface_class_index, interface_desc);
            self.types.sum_type_info.insert(
                ts.name.clone(),
                SumTypeInfo {
                    interface_class_index,
                    variants: HashMap::new(),
                },
            );
            let ir_variants: Vec<krypton_ir::VariantDef> = variants.iter().enumerate()
                .map(|(tag, v)| krypton_ir::VariantDef {
                    name: v.name.clone(),
                    tag: tag as u32,
                    fields: v.fields.iter().map(|ty| krypton_ir::Type::from(ty.clone())).collect(),
                })
                .collect();
            to_process.push((
                krypton_ir::SumTypeDef {
                    name: ts.name.clone(),
                    type_params: ts.type_param_vars.clone(),
                    variants: ir_variants,
                },
                qualified_sum,
            ));
        }
        // Second pass: register variant metadata (calls type_to_jvm for field types).
        for (sum_def, qualified_sum) in &to_process {
            self.register_sum_type_metadata(sum_def, qualified_sum)?;
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Phase 2: Traits & Instances
    // -----------------------------------------------------------------------

    pub(super) fn register_fun_interfaces_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<(), CodegenError> {
        fn collect_fn_arities(ty: &Type, arities: &mut std::collections::BTreeSet<u8>) {
            match ty {
                Type::Fn(params, ret) => {
                    arities.insert(params.len() as u8);
                    for p in params {
                        collect_fn_arities(p, arities);
                    }
                    collect_fn_arities(ret, arities);
                }
                Type::Named(_, args) => {
                    for a in args {
                        collect_fn_arities(a, arities);
                    }
                }
                Type::Tuple(elems) => {
                    for e in elems {
                        collect_fn_arities(e, arities);
                    }
                }
                Type::Own(inner) => collect_fn_arities(inner, arities),
                _ => {}
            }
        }

        let mut arities = std::collections::BTreeSet::new();

        // Local functions (including instance methods)
        for fn_def in &ir_module.functions {
            if self.types.struct_info.contains_key(&fn_def.name)
                || self.types.variant_to_sum.contains_key(&fn_def.name)
            {
                continue;
            }
            for (_var_id, param_ty) in &fn_def.params {
                collect_fn_arities(param_ty, &mut arities);
            }
            collect_fn_arities(&fn_def.return_type, &mut arities);
        }

        // Imported function signatures
        for imp in &ir_module.imported_fns {
            for ty in &imp.param_types {
                collect_fn_arities(ty, &mut arities);
            }
            collect_fn_arities(&imp.return_type, &mut arities);
        }

        for arity in arities {
            self.lambda.ensure_fun_interface(
                arity,
                &mut self.cp,
                &mut self.types.class_descriptors,
            )?;
        }
        Ok(())
    }

    pub(super) fn register_traits_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();

        // Populate dict requirements from IR
        for (name, requirements) in &ir_module.fn_dict_requirements {
            self.traits
                .impl_dict_requirements
                .entry(name.clone())
                .or_insert_with(|| {
                    requirements
                        .iter()
                        .map(|(trait_name, type_var)| DictRequirement {
                            trait_name: trait_name.clone(),
                            type_var: *type_var,
                        })
                        .collect()
                });
        }

        for trait_def in &ir_module.traits {
            let qualified_trait = trait_def.trait_name.jvm_qualified();

            if !trait_def.is_imported {
                let methods_for_gen: Vec<(String, usize)> = trait_def
                    .methods
                    .iter()
                    .map(|m| (m.name.clone(), m.param_count))
                    .collect();
                let interface_bytes =
                    generate_trait_interface_class(&qualified_trait, &methods_for_gen)?;
                result_classes.push((qualified_trait.clone(), interface_bytes));
            }

            let iface_class = self.cp.add_class(&qualified_trait)?;
            self.types
                .class_descriptors
                .insert(iface_class, format!("L{qualified_trait};"));

            let mut method_refs = HashMap::new();
            for method in &trait_def.methods {
                let mut desc = String::from("(");
                for _ in 0..method.param_count {
                    desc.push_str("Ljava/lang/Object;");
                }
                desc.push_str(")Ljava/lang/Object;");
                let mref = self
                    .cp
                    .add_interface_method_ref(iface_class, &method.name, &desc)?;
                method_refs.insert(method.name.clone(), mref);
            }

            let trait_key = trait_def.trait_name.clone();
            self.traits.trait_dispatch.insert(
                trait_key,
                TraitDispatchInfo {
                    interface_class: iface_class,
                    method_refs,
                },
            );
        }
        Ok(result_classes)
    }

    pub(super) fn register_builtin_instances_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        let local_traits: std::collections::HashSet<&str> = ir_module
            .traits
            .iter()
            .filter(|td| !td.is_imported)
            .map(|td| td.name.as_str())
            .collect();
        let registry = intrinsics::IntrinsicRegistry::new();
        for entry in registry.iter() {
            // Find the TraitName key matching this intrinsic's bare trait name
            let trait_key = self
                .traits
                .trait_dispatch
                .keys()
                .find(|tn| tn.local_name == entry.trait_name)
                .cloned();
            if let Some(trait_key) = trait_key {
                // Builtin instance classes live in the trait's defining module.
                let class_name = format!(
                    "{}/{}$${}",
                    trait_key.module_path, entry.trait_name, entry.type_name
                );

                // The trait interface class uses the qualified trait name
                let q_trait = trait_key.jvm_qualified();
                if local_traits.contains(entry.trait_name) {
                    let bytes = if entry.is_show() {
                        generate_builtin_show_instance_class(&class_name, &q_trait, entry)?
                    } else {
                        generate_builtin_trait_instance_class(&class_name, &q_trait, entry)?
                    };
                    result_classes.push((class_name.clone(), bytes));
                }

                let inst_class_idx = self.cp.add_class(&class_name)?;
                let inst_desc = format!("L{class_name};");
                self.types
                    .class_descriptors
                    .insert(inst_class_idx, inst_desc.clone());
                let instance_field_ref =
                    self.cp
                        .add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;
                let builtin_type = name_to_builtin_type(entry.type_name);
                self.traits.instance_singletons.insert(
                    (trait_key, builtin_type),
                    InstanceSingletonInfo { instance_field_ref },
                );
            }
        }
        Ok(result_classes)
    }

    pub(super) fn register_imported_instances(
        &mut self,
        imported_instances: &HashMap<(TraitName, krypton_ir::Type), ImportedInstanceInfo>,
    ) -> Result<(), CodegenError> {
        for ((trait_name, _target_type), imported_instance) in imported_instances {
            let inst_class_idx = self.cp.add_class(&imported_instance.class_name)?;
            let inst_desc = format!("L{};", imported_instance.class_name);
            self.types
                .class_descriptors
                .insert(inst_class_idx, inst_desc.clone());
            if imported_instance.requirements.is_empty() {
                let instance_field_ref =
                    self.cp
                        .add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;
                self.traits.instance_singletons.insert(
                    (trait_name.clone(), imported_instance.target_type.clone()),
                    InstanceSingletonInfo { instance_field_ref },
                );
            } else {
                self.traits
                    .parameterized_instances
                    .entry(trait_name.clone())
                    .or_default()
                    .push(ParameterizedInstanceInfo {
                        class_name: imported_instance.class_name.clone(),
                        target_type: imported_instance.target_type.clone(),
                        requirements: imported_instance.requirements.clone(),
                    });
            }
        }
        Ok(())
    }

    pub(super) fn register_instance_defs_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
        class_name: &str,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();

        // Build FnId → FnDef lookup
        let fn_defs_by_id: HashMap<krypton_ir::FnId, &krypton_ir::FnDef> =
            ir_module.functions.iter().map(|f| (f.id, f)).collect();

        for inst in &ir_module.instances {
            if inst.is_intrinsic || inst.is_imported {
                continue;
            }
            let instance_class_name = format!(
                "{}/{}$${}",
                ir_module.module_path.as_str(), inst.trait_name.local_name, inst.target_type_name
            );
            // The trait interface class uses the qualified trait name
            let q_trait = inst.trait_name.jvm_qualified();
            let dict_requirements: Vec<DictRequirement> = inst
                .sub_dict_requirements
                .iter()
                .map(|(trait_name, type_var)| DictRequirement {
                    trait_name: trait_name.clone(),
                    type_var: *type_var,
                })
                .collect();

            let mut method_info = Vec::new();
            let mut param_jvm_types_map: HashMap<String, Vec<JvmType>> = HashMap::new();
            let mut return_jvm_types_map: HashMap<String, JvmType> = HashMap::new();
            let mut param_class_names_map: HashMap<String, Vec<Option<String>>> = HashMap::new();

            for (method_name, fn_id) in &inst.method_fn_ids {
                let mangled = format!(
                    "{}$${}$${}",
                    inst.trait_name.local_name, inst.target_type_name, method_name
                );

                // Look up the FnDef to get param/return types
                let Some(fn_def) = fn_defs_by_id.get(fn_id) else {
                    continue; // Intrinsic method — no FnDef exists
                };

                // Extract user param types (skip dict params at the front)
                let dict_count = dict_requirements.len();
                let user_params: Vec<&Type> = fn_def
                    .params
                    .iter()
                    .skip(dict_count)
                    .map(|(_vid, ty)| ty)
                    .collect();

                let param_jvm: Vec<JvmType> = user_params
                    .iter()
                    .map(|t| self.type_to_jvm(t))
                    .collect::<Result<_, _>>()?;
                let ret_jvm = self.type_to_jvm(&fn_def.return_type)?;

                self.traits
                    .impl_dict_requirements
                    .insert(mangled.clone(), dict_requirements.clone());

                let mut all_param_jvm = Vec::new();
                for _ in 0..dict_requirements.len() {
                    all_param_jvm.push(JvmType::StructRef(self.builder.refs.object_class));
                }
                all_param_jvm.extend(param_jvm.iter().copied());
                let static_desc = self.types.build_descriptor(&all_param_jvm, ret_jvm);

                let class_names: Vec<Option<String>> = param_jvm
                    .iter()
                    .map(|jt| match jt {
                        JvmType::StructRef(idx) => {
                            self.types.class_descriptors.get(idx).map(|desc| {
                                desc.strip_prefix('L')
                                    .and_then(|s| s.strip_suffix(';'))
                                    .unwrap_or(desc)
                                    .to_string()
                            })
                        }
                        _ => None,
                    })
                    .collect();

                param_class_names_map.insert(method_name.clone(), class_names);
                param_jvm_types_map.insert(method_name.clone(), param_jvm);
                return_jvm_types_map.insert(method_name.clone(), ret_jvm);
                method_info.push((
                    method_name.clone(),
                    mangled.clone(),
                    user_params.len(),
                    static_desc,
                ));
            }

            let is_parameterized = type_has_vars(&inst.target_type);

            if !is_parameterized {
                let instance_bytes = generate_instance_class(
                    &instance_class_name,
                    &q_trait,
                    class_name,
                    &method_info,
                    &param_jvm_types_map,
                    &return_jvm_types_map,
                    &param_class_names_map,
                )?;
                result_classes.push((instance_class_name.clone(), instance_bytes));

                let inst_class_idx = self.cp.add_class(&instance_class_name)?;
                let inst_desc = format!("L{instance_class_name};");
                self.types
                    .class_descriptors
                    .insert(inst_class_idx, inst_desc.clone());
                let instance_field_ref =
                    self.cp
                        .add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;

                self.traits.instance_singletons.insert(
                    (inst.trait_name.clone(), inst.target_type.clone()),
                    InstanceSingletonInfo { instance_field_ref },
                );
            } else {
                let instance_bytes = generate_parameterized_instance_class(
                    &instance_class_name,
                    &q_trait,
                    class_name,
                    &method_info,
                    &param_jvm_types_map,
                    &return_jvm_types_map,
                    &param_class_names_map,
                    dict_requirements.len(),
                )?;
                result_classes.push((instance_class_name.clone(), instance_bytes));

                let new_info = ParameterizedInstanceInfo {
                    class_name: instance_class_name.clone(),
                    target_type: inst.target_type.clone(),
                    requirements: dict_requirements,
                };
                let entries = self
                    .traits
                    .parameterized_instances
                    .entry(inst.trait_name.clone())
                    .or_default();
                let canonical = krypton_ir::type_to_canonical_name(&inst.target_type);
                if let Some(pos) = entries
                    .iter()
                    .position(|e| krypton_ir::type_to_canonical_name(&e.target_type) == canonical)
                {
                    entries[pos] = new_info;
                } else {
                    entries.push(new_info);
                }
            }
        }
        Ok(result_classes)
    }

    // -----------------------------------------------------------------------
    // Phase 3: Tuples & Functions
    // -----------------------------------------------------------------------

    pub(super) fn register_tuples_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<(), CodegenError> {
        for &arity in &ir_module.tuple_arities {
            let class_name = format!("krypton/runtime/Tuple{arity}");
            let class_index = self.cp.add_class(&class_name)?;
            let class_desc = format!("Lkrypton/runtime/Tuple{arity};");
            self.types.class_descriptors.insert(class_index, class_desc);

            let mut ctor_desc = String::from("(");
            for _ in 0..arity {
                ctor_desc.push_str("Ljava/lang/Object;");
            }
            ctor_desc.push_str(")V");
            let constructor_ref = self.cp.add_method_ref(class_index, "<init>", &ctor_desc)?;

            let mut field_refs = Vec::new();
            for i in 0..arity {
                let accessor_name = format!("_{i}");
                let accessor_desc = "()Ljava/lang/Object;".to_string();
                let mr = self
                    .cp
                    .add_method_ref(class_index, &accessor_name, &accessor_desc)?;
                field_refs.push(mr);
            }

            self.types.tuple_info.insert(
                arity,
                super::compiler::TupleInfo {
                    class_index,
                    constructor_ref,
                    field_refs,
                },
            );
        }
        Ok(())
    }

    pub(super) fn register_vec(&mut self) -> Result<(), CodegenError> {
        let ka_class = self.cp.add_class("krypton/runtime/KryptonArray")?;
        let ka_init = self.cp.add_method_ref(ka_class, "<init>", "(I)V")?;
        let ka_set = self
            .cp
            .add_method_ref(ka_class, "set", "(ILjava/lang/Object;)V")?;
        let ka_freeze = self.cp.add_method_ref(ka_class, "freeze", "()V")?;
        self.types
            .class_descriptors
            .insert(ka_class, "Lkrypton/runtime/KryptonArray;".to_string());
        self.vec_info = Some(VecInfo {
            class_index: ka_class,
            init_ref: ka_init,
            set_ref: ka_set,
            freeze_ref: ka_freeze,
        });
        Ok(())
    }

    pub(super) fn register_functions_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
        this_class: u16,
    ) -> Result<(), CodegenError> {
        // Local functions (including instance methods which are in ir_module.functions)
        for fn_def in &ir_module.functions {
            let name = &fn_def.name;
            if self.types.struct_info.contains_key(name)
                || self.types.variant_to_sum.contains_key(name)
            {
                continue;
            }
            let impl_dict_count = self
                .traits
                .impl_dict_requirements
                .get(name)
                .map(|r| r.len())
                .unwrap_or(0);

            // FnDef params already include dict params prepended by the lowerer.
            // We need to build the JVM descriptor from all params.
            let all_param_types: Vec<JvmType> = fn_def
                .params
                .iter()
                .map(|(_vid, ty)| self.type_to_jvm(ty))
                .collect::<Result<_, _>>()?;
            let return_type = self.type_to_jvm(&fn_def.return_type)?;

            let jvm_name = if name == "main" {
                "krypton_main"
            } else {
                name.as_str()
            };
            let descriptor = self.types.build_descriptor(&all_param_types, return_type);
            let method_ref = self.cp.add_method_ref(this_class, jvm_name, &descriptor)?;

            // tc_param_types = user params (skip dict params)
            let tc_param_types: Vec<Type> = fn_def
                .params
                .iter()
                .skip(impl_dict_count)
                .map(|(_vid, ty)| ty.clone())
                .collect();

            self.types
                .functions
                .entry(name.clone())
                .or_default()
                .push(FunctionInfo {
                    method_ref,
                    param_types: all_param_types,
                    return_type,
                    is_void: false,
                });
            self.types
                .fn_tc_types
                .insert(name.clone(), (tc_param_types, fn_def.return_type.clone()));
        }

        for ext in ir_module
            .extern_fns
            .iter()
            .filter(|ext| ext.nullable && matches!(ext.target, krypton_ir::ExternTarget::Java { .. }))
        {
            let wrapper_param_types: Vec<JvmType> = ext
                .param_types
                .iter()
                .map(|ty| extern_param_info(self, ty).map(|(jvm, _)| jvm))
                .collect::<Result<_, _>>()?;
            let wrapper_return_type = self.type_to_jvm(&ext.return_type)?;
            let wrapper_desc = self
                .types
                .build_descriptor(&wrapper_param_types, wrapper_return_type);
            let wrapper_ref = self.cp.add_method_ref(this_class, &ext.name, &wrapper_desc)?;
            self.types.functions.entry(ext.name.clone()).or_insert_with(|| {
                vec![FunctionInfo {
                    method_ref: wrapper_ref,
                    param_types: wrapper_param_types,
                    return_type: wrapper_return_type,
                    is_void: false,
                }]
            });
        }

        // Extern functions: local externs first
        let local_nullable_java_externs: std::collections::HashSet<&str> = ir_module
            .extern_fns
            .iter()
            .filter(|ext| ext.nullable && matches!(ext.target, krypton_ir::ExternTarget::Java { .. }))
            .map(|ext| ext.name.as_str())
            .collect();
        for ext in &ir_module.extern_fns {
            let (_, extern_class) = match &ext.target {
                krypton_ir::ExternTarget::Java { class } => {
                    let jvm = class.replace('.', "/");
                    let ci = self.cp.add_class(&jvm)?;
                    (jvm, ci)
                }
                krypton_ir::ExternTarget::Js { .. } => continue,
            };

            let mut param_jvm_types = Vec::new();
            let mut param_desc = String::from("(");
            for pt in &ext.param_types {
                let (jvm, desc) = extern_param_info(self, pt)?;
                param_jvm_types.push(jvm);
                param_desc.push_str(&desc);
            }
            param_desc.push(')');

            let (return_type, ret_desc, is_void) =
                extern_return_info(self, &ext.return_type, ext.nullable)?;

            let descriptor = format!("{param_desc}{ret_desc}");
            let method_ref = self
                .cp
                .add_method_ref(extern_class, &ext.name, &descriptor)?;

            let info = FunctionInfo {
                method_ref,
                param_types: param_jvm_types,
                return_type,
                is_void,
            };

            if ext.nullable {
                if local_nullable_java_externs.contains(ext.name.as_str()) {
                    self.raw_extern_functions.insert(ext.name.clone(), info);
                }
                continue;
            }

            self.types
                .functions
                .entry(ext.name.clone())
                .or_insert_with(|| vec![info]);
        }

        // Imported extern functions from link view
        for (path, ef) in self.link_view.all_extern_fns() {
            if path.as_str() == ir_module.module_path.as_str() { continue; }
            let extern_class = match &ef.target {
                krypton_parser::ast::ExternTarget::Java => {
                    let jvm = ef.host_module_path.replace('.', "/");
                    self.cp.add_class(&jvm)?
                }
                krypton_parser::ast::ExternTarget::Js => continue,
            };

            let ir_param_types: Vec<krypton_ir::Type> = ef.param_types.iter()
                .map(|ty| krypton_ir::Type::from(ty.clone()))
                .collect();
            let ir_return_type: krypton_ir::Type = ef.return_type.clone().into();

            let mut param_jvm_types = Vec::new();
            let mut param_desc = String::from("(");
            for pt in &ir_param_types {
                let (jvm, desc) = extern_param_info(self, pt)?;
                param_jvm_types.push(jvm);
                param_desc.push_str(&desc);
            }
            param_desc.push(')');

            let (return_type, ret_desc, is_void) =
                extern_return_info(self, &ir_return_type, ef.nullable)?;

            let descriptor = format!("{param_desc}{ret_desc}");
            let method_ref = self
                .cp
                .add_method_ref(extern_class, &ef.name, &descriptor)?;

            let info = FunctionInfo {
                method_ref,
                param_types: param_jvm_types,
                return_type,
                is_void,
            };

            if ef.nullable {
                continue;
            }

            self.types
                .functions
                .entry(ef.name.clone())
                .or_insert_with(|| vec![info]);
        }

        // Imported functions
        for imp in &ir_module.imported_fns {
            // Skip imported constructors — local sum types/structs shadow them
            if self.types.struct_info.contains_key(&imp.name)
                || self.types.variant_to_sum.contains_key(&imp.name)
            {
                continue;
            }
            let target_class = self.cp.add_class(&imp.source_module)?;

            let impl_dict_count = self
                .traits
                .impl_dict_requirements
                .get(&imp.name)
                .map(|r| r.len())
                .unwrap_or(0);
            let mut all_param_types: Vec<JvmType> = Vec::new();
            for _ in 0..impl_dict_count {
                all_param_types.push(JvmType::StructRef(self.builder.refs.object_class));
            }
            let user_param_types: Vec<JvmType> = imp
                .param_types
                .iter()
                .map(|t| self.type_to_jvm(t))
                .collect::<Result<_, _>>()?;
            all_param_types.extend(user_param_types);
            let return_type = self.type_to_jvm(&imp.return_type)?;

            let jvm_name = if imp.original_name == "main" {
                "krypton_main"
            } else {
                imp.original_name.as_str()
            };
            let descriptor = self.types.build_descriptor(&all_param_types, return_type);
            let method_ref = self
                .cp
                .add_method_ref(target_class, jvm_name, &descriptor)?;

            self.types
                .functions
                .entry(imp.name.clone())
                .or_default()
                .push(FunctionInfo {
                    method_ref,
                    param_types: all_param_types,
                    return_type,
                    is_void: false,
                });
            self.types.fn_tc_types.insert(
                imp.name.clone(),
                (imp.param_types.clone(), imp.return_type.clone()),
            );
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Phase 4 (IR): Compile function bodies from ir::Module
    // -----------------------------------------------------------------------

    pub(super) fn compile_function_bodies_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<Vec<Method>, CodegenError> {
        self.fn_names = ir_module.fn_names();

        // Build variant_tags, sum_type_params, and variant_field_types from link view
        for (path, ts) in self.link_view.all_exported_types() {
            if path.as_str() == ir_module.module_path.as_str() { continue; }
            let krypton_typechecker::module_interface::TypeSummaryKind::Sum { variants } = &ts.kind else { continue; };
            let mut tag_map = std::collections::HashMap::new();
            for (tag, variant) in variants.iter().enumerate() {
                tag_map.insert(tag as u32, variant.name.clone());
                let ir_fields: Vec<krypton_ir::Type> = variant.fields.iter()
                    .map(|ty| krypton_ir::Type::from(ty.clone()))
                    .collect();
                self.variant_field_types
                    .insert(variant.name.clone(), ir_fields);
            }
            self.variant_tags.insert(ts.name.clone(), tag_map);
            self.sum_type_params
                .insert(ts.name.clone(), ts.type_param_vars.clone());
        }

        // Ensure current module's sum type tags take priority over imports
        for sum_def in &ir_module.sum_types {
            let mut tag_map = std::collections::HashMap::new();
            for variant in &sum_def.variants {
                tag_map.insert(variant.tag, variant.name.clone());
                self.variant_field_types
                    .insert(variant.name.clone(), variant.fields.clone());
            }
            self.variant_tags.insert(sum_def.name.clone(), tag_map);
            self.sum_type_params
                .insert(sum_def.name.clone(), sum_def.type_params.clone());
        }

        let mut extra_methods = Vec::new();
        for fn_def in &ir_module.functions {
            let method = self.compile_ir_function(fn_def, ir_module)?;
            extra_methods.push(method);
        }
        for ext in ir_module
            .extern_fns
            .iter()
            .filter(|ext| ext.nullable && matches!(ext.target, krypton_ir::ExternTarget::Java { .. }))
        {
            extra_methods.push(self.compile_nullable_extern_wrapper(ext)?);
        }
        Ok(extra_methods)
    }

    fn compile_nullable_extern_wrapper(
        &mut self,
        ext: &krypton_ir::ExternFnDef,
    ) -> Result<Method, CodegenError> {
        self.reset_method_state();

        let wrapper_info = self
            .types
            .get_function(&ext.name)
            .cloned()
            .ok_or_else(|| CodegenError::UndefinedVariable(ext.name.clone(), None))?;
        let raw_info = self
            .raw_extern_functions
            .get(&ext.name)
            .cloned()
            .ok_or_else(|| {
                CodegenError::UndefinedVariable(
                    format!("missing raw extern method info for {}", ext.name),
                    None,
                )
            })?;

        let mut param_slots = Vec::new();
        for &jvm_ty in &wrapper_info.param_types {
            let slot = self.builder.next_local;
            let slot_size: u16 = match jvm_ty {
                JvmType::Long | JvmType::Double => 2,
                _ => 1,
            };
            self.builder.next_local += slot_size;
            self.builder
                .frame
                .local_types
                .extend(self.builder.jvm_type_to_vtypes(jvm_ty));
            param_slots.push((slot, jvm_ty));
        }
        self.builder.fn_params = param_slots.clone();
        self.builder.fn_return_type = Some(wrapper_info.return_type);

        for (slot, jvm_ty) in &param_slots {
            self.builder.emit_load(*slot, *jvm_ty);
        }
        for jvm_ty in raw_info.param_types.iter().rev() {
            self.builder.pop_jvm_type(*jvm_ty);
        }
        self.builder.emit(Instruction::Invokestatic(raw_info.method_ref));
        self.builder.push_jvm_type(raw_info.return_type);

        let raw_slot = self.builder.alloc_anonymous_local(raw_info.return_type);
        self.builder.emit(Instruction::Astore(raw_slot as u8));
        self.builder.frame.pop_type();

        self.builder.emit(Instruction::Aload(raw_slot as u8));
        self.builder.push_jvm_type(raw_info.return_type);
        let some_path = self.builder.emit_placeholder(Instruction::Ifnonnull(0));
        self.builder.frame.pop_type();
        let stack_at_some = self.builder.frame.stack_types.clone();

        let (none_class, _, _, _) = self.option_variant_construct_info(&ext.return_type, "None")?;
        let none_field_ref = self.variant_singleton_field_ref(none_class)?;
        self.builder.emit(Instruction::Getstatic(none_field_ref));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: none_class,
        });
        self.builder.emit(Instruction::Areturn);

        let some_target = self.builder.current_offset();
        self.builder.frame.stack_types = stack_at_some;
        self.builder.frame.record_frame(some_target);
        self.builder
            .patch(some_path, Instruction::Ifnonnull(some_target));

        let (some_class, some_ctor, option_iface, some_fields) =
            self.option_variant_construct_info(&ext.return_type, "Some")?;
        self.builder.emit_new_dup(some_class);
        self.builder.emit(Instruction::Aload(raw_slot as u8));
        self.builder.push_jvm_type(raw_info.return_type);

        let inner_type = self.nullable_inner_type(&ext.return_type)?;
        let actual_jvm = match inner_type {
            Type::Int => {
                self.builder.unbox_if_needed(JvmType::Long);
                JvmType::Long
            }
            Type::Float => {
                self.builder.unbox_if_needed(JvmType::Double);
                JvmType::Double
            }
            Type::Bool => {
                self.builder.unbox_if_needed(JvmType::Int);
                JvmType::Int
            }
            _ => raw_info.return_type,
        };

        let expected = if some_fields[0].is_erased {
            JvmType::StructRef(self.builder.refs.object_class)
        } else {
            some_fields[0].jvm_type
        };
        self.emit_type_coercion(actual_jvm, expected);
        self.emit_variant_invokespecial(some_ctor, &some_fields, option_iface);
        self.builder.emit(Instruction::Areturn);

        let descriptor = self
            .types
            .build_descriptor(&wrapper_info.param_types, wrapper_info.return_type);
        let name_idx = self.cp.add_utf8(&ext.name)?;
        let desc_idx = self.cp.add_utf8(&descriptor)?;

        Ok(Method {
            access_flags: ristretto_classfile::MethodAccessFlags::PUBLIC
                | ristretto_classfile::MethodAccessFlags::STATIC,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![self.builder.finish_method()],
        })
    }

    pub(super) fn emit_main_wrapper(&mut self) -> Result<(), CodegenError> {
        let main_info = self
            .types
            .get_function("main")
            .ok_or(CodegenError::NoMainFunction())?;
        let krypton_main_ref = main_info.method_ref;
        let main_return_type = main_info.return_type;

        self.reset_method_state();
        self.builder.next_local = 1; // slot 0 = String[] args
        self.builder.frame.local_types = vec![VerificationType::Object {
            cpool_index: self.builder.refs.string_arr_class,
        }];

        // Boot the actor runtime before calling user code
        let runtime_class_boot = self.cp.add_class("krypton/runtime/KryptonRuntime")?;
        let boot_ref = self.cp.add_method_ref(runtime_class_boot, "boot", "()V")?;
        self.builder.emit(Instruction::Invokestatic(boot_ref));

        // Call krypton_main
        self.builder
            .emit(Instruction::Invokestatic(krypton_main_ref));
        self.builder.push_jvm_type(main_return_type);

        // Discard the return value
        match main_return_type {
            JvmType::Long | JvmType::Double => {
                self.builder.emit(Instruction::Pop2);
                self.builder.frame.pop_type_n(2);
            }
            JvmType::Int | JvmType::StructRef(_) => {
                self.builder.emit(Instruction::Pop);
                self.builder.frame.pop_type();
            }
        }

        // Call KryptonRuntime.awaitAll()
        let runtime_class = self.cp.add_class("krypton/runtime/KryptonRuntime")?;
        let await_ref = self
            .cp
            .add_method_ref(runtime_class, "awaitAllActors", "()V")?;
        self.builder.emit(Instruction::Invokestatic(await_ref));

        self.builder.emit(Instruction::Return);
        Ok(())
    }
}
