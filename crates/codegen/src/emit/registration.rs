//! Module registration phases (types, traits, instances, functions).

use std::collections::HashMap;

use krypton_typechecker::typed_ast::TypedModule;
use krypton_typechecker::type_registry;
use krypton_typechecker::types::{self, Type, TypeVarId};
use ristretto_classfile::attributes::{Instruction, VerificationType};
use ristretto_classfile::Method;

use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind};

use super::{
    type_expr_to_jvm, type_expr_to_jvm_basic, type_expr_to_jvm_with_params,
    type_expr_uses_type_params, qualify_type_for,
    ImportedInstanceInfo, dict_requirements_for_instance,
};
use super::data_class_gen::{
    generate_struct_class, generate_sealed_interface_class, generate_variant_class,
};
use super::trait_class_gen::{
    generate_trait_interface_class, generate_instance_class,
    generate_builtin_show_instance_class, generate_builtin_trait_instance_class,
    generate_parameterized_instance_class,
};
use super::compiler::{
    Compiler, CodegenError, JvmType, FunctionInfo, StructInfo, VariantInfo, SumTypeInfo,
    TraitDispatchInfo, DictRequirement, InstanceSingletonInfo, ParameterizedInstanceInfo, VecInfo,
};
use super::intrinsics;

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
/// Types with type args use Object (JVM erasure).
fn jvm_type_for_named(
    name: &str,
    args: &[Type],
    struct_info: &HashMap<String, StructInfo>,
    object_class: u16,
) -> (JvmType, String) {
    if args.is_empty() {
        if let Some(info) = struct_info.get(name) {
            (JvmType::StructRef(info.class_index), format!("L{};", info.class_name))
        } else {
            (JvmType::StructRef(object_class), "Ljava/lang/Object;".to_string())
        }
    } else {
        (JvmType::StructRef(object_class), "Ljava/lang/Object;".to_string())
    }
}

impl Compiler {
    pub(super) fn register_extern_types(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<(), CodegenError> {
        for (krypton_name, java_class) in typed_module
            .extern_java_types
            .iter()
            .chain(typed_module.imported_extern_java_types.iter())
        {
            let jvm_class = java_class.replace('.', "/");
            let class_index = self.cp.add_class(&jvm_class)?;
            self.types
                .class_descriptors
                .insert(class_index, format!("L{};", jvm_class));
            self.types.struct_info.insert(
                krypton_name.clone(),
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

    pub(super) fn register_structs(
        &mut self,
        typed_module: &TypedModule,
        field_type_registry: &type_registry::TypeRegistry,
        struct_type_param_maps: &HashMap<String, HashMap<String, TypeVarId>>,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        let empty_map = HashMap::new();
        for (struct_name, _type_params, ast_fields) in &typed_module.struct_decls {
            let qualified = qualify_type_for(typed_module, struct_name);

            let type_param_map = struct_type_param_maps.get(struct_name).unwrap_or(&empty_map);
            let jvm_fields: Vec<(String, JvmType)> = ast_fields
                .iter()
                .map(|(fname, texpr)| {
                    let jt = type_expr_to_jvm_with_params(self, texpr, field_type_registry, &type_param_map)?;
                    Ok((fname.clone(), jt))
                })
                .collect::<Result<_, CodegenError>>()?;

            let class_index = self.cp.add_class(&qualified)?;
            let class_desc = format!("L{qualified};");
            self.types
                .class_descriptors
                .insert(class_index, class_desc.clone());

            let mut ctor_desc = String::from("(");
            for (_, jt) in &jvm_fields {
                ctor_desc.push_str(&self.types.jvm_type_descriptor(*jt));
            }
            ctor_desc.push_str(")V");
            let constructor_ref =
                self.cp.add_method_ref(class_index, "<init>", &ctor_desc)?;

            let mut accessor_refs = HashMap::new();
            for (fname, jt) in &jvm_fields {
                let ret_desc = self.types.jvm_type_descriptor(*jt);
                let method_desc = format!("(){ret_desc}");
                let accessor_ref =
                    self.cp.add_method_ref(class_index, fname, &method_desc)?;
                accessor_refs.insert(fname.clone(), accessor_ref);
            }

            self.types.struct_info.insert(
                struct_name.clone(),
                StructInfo {
                    class_index,
                    class_name: qualified.clone(),
                    fields: jvm_fields.clone(),
                    constructor_ref,
                    accessor_refs,
                },
            );

            let struct_bytes =
                generate_struct_class(&qualified, &jvm_fields, &self.types.class_descriptors)?;
            result_classes.push((qualified.clone(), struct_bytes));
        }
        Ok(result_classes)
    }

    pub(super) fn register_sum_types(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        for (sum_name, type_params, variants) in &typed_module.sum_decls {
            let qualified_sum = qualify_type_for(typed_module, sum_name);

            let interface_class_index = self.cp.add_class(&qualified_sum)?;
            let interface_desc = format!("L{qualified_sum};");
            self.types
                .class_descriptors
                .insert(interface_class_index, interface_desc);

            let mut variant_infos = HashMap::new();
            let variant_names: Vec<String> = variants.iter().map(|v| format!("{}${}", qualified_sum, v.name)).collect();

            for variant in variants {
                let fields: Vec<(String, JvmType, bool)> = variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, texpr)| {
                        let field_name = format!("field{i}");
                        let is_erased = type_expr_uses_type_params(texpr, type_params);
                        let jt = if is_erased {
                            JvmType::StructRef(self.builder.refs.object_class)
                        } else {
                            type_expr_to_jvm_basic(texpr, self)?
                        };
                        Ok((field_name, jt, is_erased))
                    })
                    .collect::<Result<_, CodegenError>>()?;

                let qualified_variant = format!("{}${}", qualified_sum, variant.name);
                let variant_class_index = self.cp.add_class(&qualified_variant)?;
                let variant_desc = format!("L{qualified_variant};");
                self.types
                    .class_descriptors
                    .insert(variant_class_index, variant_desc);

                let mut ctor_desc = String::from("(");
                for (_, jt, is_erased) in &fields {
                    if *is_erased {
                        ctor_desc.push_str("Ljava/lang/Object;");
                    } else {
                        ctor_desc.push_str(&self.types.jvm_type_descriptor(*jt));
                    }
                }
                ctor_desc.push_str(")V");

                let constructor_ref = self.cp.add_method_ref(
                    variant_class_index,
                    "<init>",
                    &ctor_desc,
                )?;

                let mut main_field_refs = Vec::new();
                for (fname, jt, is_erased) in &fields {
                    let fdesc = if *is_erased {
                        "Ljava/lang/Object;".to_string()
                    } else {
                        self.types.jvm_type_descriptor(*jt)
                    };
                    let fr = self.cp.add_field_ref(variant_class_index, fname, &fdesc)?;
                    main_field_refs.push(fr);
                }

                self.types
                    .variant_to_sum
                    .insert(variant.name.clone(), sum_name.clone());

                let singleton_field_ref = if fields.is_empty() {
                    let variant_desc = format!("L{qualified_variant};");
                    Some(self.cp.add_field_ref(variant_class_index, "INSTANCE", &variant_desc)?)
                } else {
                    None
                };

                variant_infos.insert(
                    variant.name.clone(),
                    VariantInfo {
                        class_index: variant_class_index,
                        class_name: qualified_variant.clone(),
                        fields: fields.clone(),
                        constructor_ref,
                        field_refs: main_field_refs,
                        singleton_field_ref,
                    },
                );

                let variant_bytes =
                    generate_variant_class(&qualified_variant, &qualified_sum, &variant.name, &fields, &self.types.class_descriptors)?;
                result_classes.push((qualified_variant.clone(), variant_bytes));
            }

            self.types.sum_type_info.insert(
                sum_name.clone(),
                SumTypeInfo {
                    interface_class_index,
                    variants: variant_infos,
                },
            );

            let variant_name_refs: Vec<&str> = variant_names.iter().map(|s| s.as_str()).collect();
            let interface_bytes = generate_sealed_interface_class(&qualified_sum, &variant_name_refs)?;
            result_classes.push((qualified_sum.clone(), interface_bytes));
        }
        Ok(result_classes)
    }

    pub(super) fn register_fun_interfaces(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<(), CodegenError> {
        for entry in typed_module.fn_types.iter() {
            if let Type::Fn(param_tys, _) = &entry.scheme.ty {
                if self.types.struct_info.contains_key(&entry.name)
                    || self.types.variant_to_sum.contains_key(&entry.name)
                {
                    continue;
                }
                for pt in param_tys {
                    if let Type::Fn(inner_params, _) = pt {
                        let arity = inner_params.len() as u8;
                        self.lambda.ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
                    }
                }
            }
        }
        for instance_def in &typed_module.instance_defs {
            for method in &instance_def.methods {
                if let Type::Fn(param_tys, _) = &method.scheme.ty {
                    for pt in param_tys {
                        if let Type::Fn(inner_params, _) = pt {
                            let arity = inner_params.len() as u8;
                            self.lambda.ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn register_traits(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();

        for (name, requirements) in &typed_module.fn_constraint_requirements {
            self.traits.impl_dict_requirements.insert(
                name.clone(),
                requirements
                    .iter()
                    .map(|(trait_name, type_var)| DictRequirement {
                        trait_name: trait_name.clone(),
                        type_var: *type_var,
                    })
                    .collect(),
            );
        }
        for (name, requirements) in &typed_module.imported_fn_constraint_requirements {
            self.traits.impl_dict_requirements.entry(name.clone()).or_insert_with(|| {
                requirements
                    .iter()
                    .map(|(trait_name, type_var)| DictRequirement {
                        trait_name: trait_name.clone(),
                        type_var: *type_var,
                    })
                    .collect()
            });
        }

        for trait_def in &typed_module.trait_defs {
            let qualified_trait = qualify_type_for(typed_module, &trait_def.name);

            if !trait_def.is_imported {
                let interface_bytes = generate_trait_interface_class(&qualified_trait, &trait_def.methods)?;
                result_classes.push((qualified_trait.clone(), interface_bytes));
            }

            let iface_class = self.cp.add_class(&qualified_trait)?;
            self.types.class_descriptors.insert(iface_class, format!("L{qualified_trait};"));

            let mut method_refs = HashMap::new();
            for (method_name, param_count) in &trait_def.methods {
                let mut desc = String::from("(");
                for _ in 0..*param_count {
                    desc.push_str("Ljava/lang/Object;");
                }
                desc.push_str(")Ljava/lang/Object;");
                let mref = self.cp.add_interface_method_ref(iface_class, method_name, &desc)?;
                method_refs.insert(method_name.clone(), mref);
            }

            self.traits.trait_dispatch.insert(trait_def.name.clone(), TraitDispatchInfo {
                interface_class: iface_class,
                method_refs,
                type_var_id: trait_def.type_var_id,
                method_tc_types: trait_def.method_tc_types.clone(),
            });
        }
        Ok(result_classes)
    }

    pub(super) fn register_builtin_instances(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        let registry = intrinsics::IntrinsicRegistry::new();
        for entry in registry.iter() {
            if self.traits.trait_dispatch.contains_key(entry.trait_name) {
                let q_trait = qualify_type_for(typed_module, entry.trait_name);
                let class_name = format!("{q_trait}$${}", entry.type_name);

                let bytes = if entry.is_show() {
                    generate_builtin_show_instance_class(&class_name, &q_trait, entry)?
                } else {
                    generate_builtin_trait_instance_class(&class_name, &q_trait, entry)?
                };
                result_classes.push((class_name.clone(), bytes));

                let inst_class_idx = self.cp.add_class(&class_name)?;
                let inst_desc = format!("L{class_name};");
                self.types.class_descriptors.insert(inst_class_idx, inst_desc.clone());
                let instance_field_ref = self.cp.add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;
                let builtin_type = name_to_builtin_type(entry.type_name);
                self.traits.instance_singletons.insert(
                    (entry.trait_name.to_string(), builtin_type),
                    InstanceSingletonInfo { instance_field_ref },
                );
            }
        }
        Ok(result_classes)
    }

    pub(super) fn register_imported_instances(
        &mut self,
        imported_instances: &HashMap<(String, String), ImportedInstanceInfo>,
    ) -> Result<(), CodegenError> {
        for ((trait_name, type_name), imported_instance) in imported_instances {
            let inst_class_idx = self.cp.add_class(&imported_instance.class_name)?;
            let inst_desc = format!("L{};", imported_instance.class_name);
            self.types
                .class_descriptors
                .insert(inst_class_idx, inst_desc.clone());
            if imported_instance.requirements.is_empty() {
                let instance_field_ref =
                    self.cp.add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;
                self.traits.instance_singletons.insert(
                    (trait_name.clone(), imported_instance.target_type.clone()),
                    InstanceSingletonInfo { instance_field_ref },
                );
            } else {
                self.traits.parameterized_instances
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

    pub(super) fn register_instance_defs(
        &mut self,
        typed_module: &TypedModule,
        class_name: &str,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        for instance_def in &typed_module.instance_defs {
            if instance_def.is_intrinsic {
                continue;
            }
            let q_trait = qualify_type_for(typed_module, &instance_def.trait_name);
            let instance_class_name = format!("{}$${}", q_trait, instance_def.target_type_name);
            let dict_requirements = dict_requirements_for_instance(
                &instance_def.type_var_ids,
                &instance_def.constraints,
                &instance_def.subdict_traits,
            );

            let mut method_info = Vec::new();
            let mut param_jvm_types_map: HashMap<String, Vec<JvmType>> = HashMap::new();
            let mut return_jvm_types_map: HashMap<String, JvmType> = HashMap::new();
            let mut param_class_names_map: HashMap<String, Vec<Option<String>>> = HashMap::new();

            for method in &instance_def.methods {
                let qualified_name = krypton_typechecker::typed_ast::mangled_method_name(
                    &instance_def.trait_name,
                    &instance_def.target_type_name,
                    &method.name,
                );
                if let Type::Fn(param_tys, ret_ty) = &method.scheme.ty {
                    let param_jvm: Vec<JvmType> = param_tys.iter()
                        .map(|t| self.type_to_jvm(t))
                        .collect::<Result<_, _>>()?;
                    let ret_jvm = self.type_to_jvm(ret_ty)?;
                    self.traits
                        .impl_dict_requirements
                        .insert(qualified_name.clone(), dict_requirements.clone());
                    let mut all_param_jvm = Vec::new();
                    for _ in 0..dict_requirements.len() {
                        all_param_jvm.push(JvmType::StructRef(self.builder.refs.object_class));
                    }
                    all_param_jvm.extend(param_jvm.iter().copied());
                    let static_desc = self.types.build_descriptor(&all_param_jvm, ret_jvm);
                    let class_names: Vec<Option<String>> = param_jvm.iter().map(|jt| {
                        match jt {
                            JvmType::StructRef(idx) => {
                                self.types.class_descriptors.get(idx).map(|desc| {
                                    desc.strip_prefix('L')
                                        .and_then(|s| s.strip_suffix(';'))
                                        .unwrap_or(desc)
                                        .to_string()
                                })
                            }
                            _ => None,
                        }
                    }).collect();
                    param_class_names_map.insert(method.name.clone(), class_names);
                    param_jvm_types_map.insert(method.name.clone(), param_jvm);
                    return_jvm_types_map.insert(method.name.clone(), ret_jvm);
                    method_info.push((method.name.clone(), qualified_name.clone(), param_tys.len(), static_desc));
                }
            }

            if instance_def.type_var_ids.is_empty() {
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
                self.types.class_descriptors.insert(inst_class_idx, inst_desc.clone());
                let instance_field_ref = self.cp.add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;

                self.traits.instance_singletons.insert(
                    (instance_def.trait_name.clone(), instance_def.target_type.clone()),
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
                    target_type: instance_def.target_type.clone(),
                    requirements: dict_requirements,
                };
                let entries = self.traits.parameterized_instances
                    .entry(instance_def.trait_name.clone())
                    .or_default();
                // Local impls shadow imported impls with the same target type name
                // (e.g. user-defined Option shadows prelude Option).
                let canonical = types::type_to_canonical_name(&instance_def.target_type);
                if let Some(pos) = entries.iter().position(|e| {
                    types::type_to_canonical_name(&e.target_type) == canonical
                }) {
                    entries[pos] = new_info;
                } else {
                    entries.push(new_info);
                }
            }
        }
        Ok(result_classes)
    }

    pub(super) fn register_tuples(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<(), CodegenError> {
        let mut tuple_arities = std::collections::HashSet::new();
        for entry in typed_module.fn_types.iter() {
            collect_tuple_arities(&entry.scheme.ty, &mut tuple_arities);
        }
        for typed_fn in &typed_module.functions {
            collect_tuple_arities_expr(&typed_fn.body, &mut tuple_arities);
        }
        for instance_def in &typed_module.instance_defs {
            for method in &instance_def.methods {
                collect_tuple_arities(&method.scheme.ty, &mut tuple_arities);
                collect_tuple_arities_expr(&method.body, &mut tuple_arities);
            }
        }
        for arity in tuple_arities {
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
                let mr = self.cp.add_method_ref(class_index, &accessor_name, &accessor_desc)?;
                field_refs.push(mr);
            }

            self.types.tuple_info.insert(arity, super::compiler::TupleInfo {
                class_index,
                constructor_ref,
                field_refs,
            });
        }
        Ok(())
    }

    pub(super) fn register_vec(&mut self) -> Result<(), CodegenError> {
        let ka_class = self.cp.add_class("krypton/runtime/KryptonArray")?;
        let ka_init = self.cp.add_method_ref(ka_class, "<init>", "(I)V")?;
        let ka_set = self.cp.add_method_ref(ka_class, "set", "(ILjava/lang/Object;)V")?;
        let ka_freeze = self.cp.add_method_ref(ka_class, "freeze", "()V")?;
        self.types.class_descriptors.insert(ka_class, "Lkrypton/runtime/KryptonArray;".to_string());
        self.vec_info = Some(VecInfo { class_index: ka_class, init_ref: ka_init, set_ref: ka_set, freeze_ref: ka_freeze });
        Ok(())
    }

    pub(super) fn register_functions(
        &mut self,
        typed_module: &TypedModule,
        this_class: u16,
    ) -> Result<(), CodegenError> {
        let type_info = &typed_module.fn_types;

        for entry in type_info.iter() {
            if let Type::Fn(param_tys, ret_ty) = &entry.scheme.ty {
                let name = &entry.name;
                if self.types.struct_info.contains_key(name)
                    || self.types.variant_to_sum.contains_key(name)
                {
                    continue;
                }
                let impl_dict_count = self
                    .traits
                    .impl_dict_requirements
                    .get(name)
                    .map(|requirements| requirements.len())
                    .unwrap_or(0);
                let mut all_param_types: Vec<JvmType> = Vec::new();
                for _ in 0..impl_dict_count {
                    all_param_types.push(JvmType::StructRef(self.builder.refs.object_class));
                }
                let user_param_types: Vec<JvmType> = param_tys
                    .iter()
                    .map(|t| self.type_to_jvm(t))
                    .collect::<Result<_, _>>()?;
                all_param_types.extend(user_param_types);
                let return_type = self.type_to_jvm(ret_ty.as_ref())?;
                let jvm_name = if name == "main" {
                    "krypton_main"
                } else {
                    name.as_str()
                };
                let descriptor = self.types.build_descriptor(&all_param_types, return_type);
                let (target_class, target_name) = if let Some((source_module, orig_name)) = &entry.provenance {
                    (self.cp.add_class(source_module)?, orig_name.as_str())
                } else {
                    (this_class, jvm_name)
                };
                let method_ref =
                    self.cp.add_method_ref(target_class, target_name, &descriptor)?;
                self.types.functions.entry(name.clone()).or_default().push(
                    FunctionInfo {
                        method_ref,
                        param_types: all_param_types,
                        return_type,
                        is_void: false,
                        tc_param_types: param_tys.clone(),
                    },
                );
                self.types.fn_tc_types.insert(
                    name.clone(),
                    (param_tys.clone(), ret_ty.as_ref().clone()),
                );
            }
        }

        // Register instance method functions from instance_defs
        for instance_def in &typed_module.instance_defs {
            for method in &instance_def.methods {
                let qualified_name = krypton_typechecker::typed_ast::mangled_method_name(
                    &instance_def.trait_name,
                    &instance_def.target_type_name,
                    &method.name,
                );
                if let Type::Fn(param_tys, ret_ty) = &method.scheme.ty {
                    let impl_dict_count = self
                        .traits
                        .impl_dict_requirements
                        .get(&qualified_name)
                        .map(|requirements| requirements.len())
                        .unwrap_or(0);
                    let mut all_param_types: Vec<JvmType> = Vec::new();
                    for _ in 0..impl_dict_count {
                        all_param_types.push(JvmType::StructRef(self.builder.refs.object_class));
                    }
                    let user_param_types: Vec<JvmType> = param_tys
                        .iter()
                        .map(|t| self.type_to_jvm(t))
                        .collect::<Result<_, _>>()?;
                    all_param_types.extend(user_param_types);
                    let return_type = self.type_to_jvm(ret_ty.as_ref())?;
                    let descriptor = self.types.build_descriptor(&all_param_types, return_type);
                    let method_ref =
                        self.cp.add_method_ref(this_class, &qualified_name, &descriptor)?;
                    self.types.functions.insert(qualified_name.clone(), vec![
                        FunctionInfo {
                            method_ref,
                            param_types: all_param_types,
                            return_type,
                            is_void: false,
                            tc_param_types: param_tys.clone(),
                        },
                    ]);
                    self.types.fn_tc_types.insert(
                        qualified_name,
                        (param_tys.clone(), ret_ty.as_ref().clone()),
                    );
                }
            }
        }

        // Register extern functions
        for ext in typed_module.extern_fns.iter().chain(typed_module.imported_extern_fns.iter()) {
            let jvm_class_name = ext.java_class.replace('.', "/");
            let extern_class = self.cp.add_class(&jvm_class_name)?;

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
                        param_jvm_types.push(JvmType::StructRef(self.builder.refs.string_class));
                        param_desc.push_str("Ljava/lang/String;");
                    }
                    Type::Named(name, args) => {
                        let (jvm, desc) = jvm_type_for_named(name, args, &self.types.struct_info, self.builder.refs.object_class);
                        param_jvm_types.push(jvm);
                        param_desc.push_str(&desc);
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
                    Type::String => (JvmType::StructRef(self.builder.refs.string_class), "Ljava/lang/String;".to_string()),
                    Type::Named(name, args) => {
                        let (jvm, desc) = jvm_type_for_named(name, args, &self.types.struct_info, self.builder.refs.object_class);
                        (jvm, desc)
                    }
                    other => {
                        return Err(CodegenError::TypeError(format!(
                            "unsupported extern return type: {other:?}"
                        )));
                    }
                }
            };

            let descriptor = format!("{param_desc}{ret_desc}");
            let method_ref = self.cp.add_method_ref(extern_class, &ext.name, &descriptor)?;

            self.types.functions.insert(ext.name.clone(), vec![
                FunctionInfo {
                    method_ref,
                    param_types: param_jvm_types,
                    return_type,
                    is_void,
                    tc_param_types: ext.param_types.clone(),
                },
            ]);
        }

        Ok(())
    }

    pub(super) fn compile_function_bodies(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<Vec<Method>, CodegenError> {
        let mut extra_methods = Vec::new();
        for typed_fn in &typed_module.functions {
            let mut method = self.compile_function(typed_fn)?;
            if typed_fn.name == "main" {
                let name_idx = self.cp.add_utf8("krypton_main")?;
                method.name_index = name_idx;
            }
            extra_methods.push(method);
        }

        for instance_def in &typed_module.instance_defs {
            if instance_def.is_intrinsic {
                continue;
            }
            for method in &instance_def.methods {
                let qualified_name = krypton_typechecker::typed_ast::mangled_method_name(
                    &instance_def.trait_name,
                    &instance_def.target_type_name,
                    &method.name,
                );
                let typed_fn = krypton_typechecker::typed_ast::TypedFnDecl {
                    name: qualified_name,
                    visibility: krypton_parser::ast::Visibility::Pub,
                    params: method.params.clone(),
                    body: method.body.clone(),
                    close_self_type: None,
                };
                let compiled_method = self.compile_function(&typed_fn)?;
                extra_methods.push(compiled_method);
            }
        }

        Ok(extra_methods)
    }

    pub(super) fn emit_main_wrapper(&mut self) -> Result<(), CodegenError> {
        let main_info = self.types.get_function("main").ok_or(CodegenError::NoMainFunction)?;
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
        self.builder.emit(Instruction::Invokestatic(krypton_main_ref));
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
        let await_ref = self.cp.add_method_ref(runtime_class, "awaitAllActors", "()V")?;
        self.builder.emit(Instruction::Invokestatic(await_ref));

        self.builder.emit(Instruction::Return);
        Ok(())
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

/// Iteratively collect all tuple arities from a TypedExpr tree.
fn collect_tuple_arities_expr(expr: &TypedExpr, arities: &mut std::collections::HashSet<usize>) {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        collect_tuple_arities(&expr.ty, arities);
        match &expr.kind {
            TypedExprKind::Tuple(elems) => {
                arities.insert(elems.len());
                for e in elems { work.push(e); }
            }
            TypedExprKind::Let { value, body, .. } | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(b) = body { work.push(b); }
            }
            TypedExprKind::App { func, args } => {
                work.push(func);
                for a in args { work.push(a); }
            }
            TypedExprKind::TypeApp { expr, .. } => work.push(expr),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs { work.push(e); }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms { work.push(&arm.body); }
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::FieldAccess { expr, .. } | TypedExprKind::QuestionMark { expr, .. } => {
                work.push(expr);
            }
            TypedExprKind::StructUpdate { base, fields } => {
                work.push(base);
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::Recur(args) | TypedExprKind::VecLit(args) => {
                for a in args { work.push(a); }
            }
            _ => {}
        }
    }
}
