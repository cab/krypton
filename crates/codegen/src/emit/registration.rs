//! Module registration phases (types, traits, instances, functions).
//! All registration reads from `ir::Module`; function body compilation still uses `TypedModule`.

use std::collections::HashMap;

use krypton_typechecker::typed_ast::TypedModule;
use krypton_ir::Type;
use ristretto_classfile::attributes::{Instruction, VerificationType};
use ristretto_classfile::Method;

use super::{
    qualify_ir, qualify_with_provenance, type_references_var, type_has_vars,
    ImportedInstanceInfo,
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
    Compiler, CodegenError, JvmType, FunctionInfo, StructInfo, VariantField, VariantInfo, SumTypeInfo,
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
        let jvm_fields: Vec<(String, JvmType)> = struct_def.fields
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
            let qualified = qualify_ir(&ir_module.module_path, &struct_def.name);
            self.register_struct_metadata(struct_def, &qualified)?;
            let info = &self.types.struct_info[&struct_def.name];
            let struct_bytes =
                generate_struct_class(&info.class_name, &info.fields, &self.types.class_descriptors)?;
            result_classes.push((qualified, struct_bytes));
        }
        Ok(result_classes)
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
        self.types.class_descriptors.insert(interface_class_index, interface_desc);

        let mut variant_infos = HashMap::new();
        let mut variant_pairs = Vec::new();

        for variant in &sum_def.variants {
            let fields: Vec<VariantField> = variant.fields
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
                    Ok(VariantField { name, jvm_type, is_erased })
                })
                .collect::<Result<_, CodegenError>>()?;

            let qualified_variant = format!("{}${}", qualified_sum, variant.name);
            let variant_class_index = self.cp.add_class(&qualified_variant)?;
            let variant_desc = format!("L{qualified_variant};");
            self.types.class_descriptors.insert(variant_class_index, variant_desc);

            let mut ctor_desc = String::from("(");
            for f in &fields {
                if f.is_erased {
                    ctor_desc.push_str("Ljava/lang/Object;");
                } else {
                    ctor_desc.push_str(&self.types.jvm_type_descriptor(f.jvm_type));
                }
            }
            ctor_desc.push_str(")V");

            let constructor_ref = self.cp.add_method_ref(
                variant_class_index, "<init>", &ctor_desc,
            )?;

            let mut main_field_refs = Vec::new();
            for f in &fields {
                let fdesc = if f.is_erased {
                    "Ljava/lang/Object;".to_string()
                } else {
                    self.types.jvm_type_descriptor(f.jvm_type)
                };
                let fr = self.cp.add_field_ref(variant_class_index, &f.name, &fdesc)?;
                main_field_refs.push(fr);
            }

            self.types.variant_to_sum.insert(variant.name.clone(), sum_def.name.clone());

            let singleton_field_ref = if fields.is_empty() {
                let vdesc = format!("L{qualified_variant};");
                Some(self.cp.add_field_ref(variant_class_index, "INSTANCE", &vdesc)?)
            } else {
                None
            };

            variant_pairs.push((variant.name.clone(), qualified_variant.clone()));

            variant_infos.insert(
                variant.name.clone(),
                VariantInfo {
                    class_index: variant_class_index,
                    class_name: qualified_variant,
                    fields,
                    constructor_ref,
                    field_refs: main_field_refs,
                    singleton_field_ref,
                },
            );
        }

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
            let qualified_sum = qualify_ir(&ir_module.module_path, &sum_def.name);
            let variant_pairs = self.register_sum_type_metadata(sum_def, &qualified_sum)?;

            let sum_info = &self.types.sum_type_info[&sum_def.name];
            for (variant_name, qualified_variant) in &variant_pairs {
                let vi = &sum_info.variants[variant_name];
                let variant_bytes = generate_variant_class(
                    qualified_variant, &qualified_sum, variant_name,
                    &vi.fields, &self.types.class_descriptors,
                )?;
                result_classes.push((qualified_variant.clone(), variant_bytes));
            }

            let variant_name_refs: Vec<&str> = variant_pairs.iter()
                .map(|(_, q)| q.as_str()).collect();
            let interface_bytes = generate_sealed_interface_class(&qualified_sum, &variant_name_refs)?;
            result_classes.push((qualified_sum, interface_bytes));
        }
        Ok(result_classes)
    }

    /// Register struct types from another module (class indices only, no bytecode).
    pub(super) fn register_imported_structs_ir(
        &mut self,
        other_module: &krypton_ir::Module,
    ) -> Result<(), CodegenError> {
        for struct_def in &other_module.structs {
            if self.types.struct_info.contains_key(&struct_def.name) { continue; }
            let qualified = qualify_ir(&other_module.module_path, &struct_def.name);
            self.register_struct_metadata(struct_def, &qualified)?;
        }
        Ok(())
    }

    /// Register sum types from another module (class indices + variant mappings, no bytecode).
    pub(super) fn register_imported_sum_types_ir(
        &mut self,
        other_module: &krypton_ir::Module,
    ) -> Result<(), CodegenError> {
        for sum_def in &other_module.sum_types {
            let qualified_sum = qualify_ir(&other_module.module_path, &sum_def.name);
            if self.types.sum_type_info.contains_key(&sum_def.name) {
                // Sum type already registered (e.g. local shadow). Merge imported
                // variants into the existing info so function bodies referencing
                // imported variants (e.g. stdlib `head` returning Some) can resolve.
                for variant in &sum_def.variants {
                    if self.types.variant_to_sum.contains_key(&variant.name) {
                        continue; // Already registered (local variant)
                    }
                    // Register variant class metadata
                    let qualified_variant = format!("{}${}", qualified_sum, variant.name);
                    let variant_class_index = self.cp.add_class(&qualified_variant)?;
                    let variant_desc = format!("L{qualified_variant};");
                    self.types.class_descriptors.insert(variant_class_index, variant_desc);

                    let fields: Vec<VariantField> = variant.fields.iter().enumerate().map(|(i, ty)| {
                        let is_erased = type_references_var(ty, &sum_def.type_params);
                        let jvm_type = if is_erased {
                            JvmType::StructRef(self.builder.refs.object_class)
                        } else {
                            self.type_to_jvm(ty)?
                        };
                        Ok(VariantField {
                            name: format!("field{i}"),
                            jvm_type,
                            is_erased,
                        })
                    }).collect::<Result<_, CodegenError>>()?;

                    let mut ctor_desc = String::from("(");
                    for f in &fields {
                        if f.is_erased {
                            ctor_desc.push_str("Ljava/lang/Object;");
                        } else {
                            ctor_desc.push_str(&self.types.jvm_type_descriptor(f.jvm_type));
                        }
                    }
                    ctor_desc.push_str(")V");
                    let constructor_ref = self.cp.add_method_ref(variant_class_index, "<init>", &ctor_desc)?;

                    let mut field_refs = Vec::new();
                    for f in &fields {
                        let fdesc = if f.is_erased {
                            "Ljava/lang/Object;".to_string()
                        } else {
                            self.types.jvm_type_descriptor(f.jvm_type)
                        };
                        let fr = self.cp.add_field_ref(variant_class_index, &f.name, &fdesc)?;
                        field_refs.push(fr);
                    }

                    let singleton_field_ref = if fields.is_empty() {
                        let vdesc = format!("L{qualified_variant};");
                        Some(self.cp.add_field_ref(variant_class_index, "INSTANCE", &vdesc)?)
                    } else {
                        None
                    };

                    self.types.variant_to_sum.insert(variant.name.clone(), sum_def.name.clone());
                    if let Some(info) = self.types.sum_type_info.get_mut(&sum_def.name) {
                        info.variants.insert(variant.name.clone(), VariantInfo {
                            class_index: variant_class_index,
                            class_name: qualified_variant,
                            constructor_ref,
                            field_refs,
                            fields,
                            singleton_field_ref,
                        });
                    }
                }
                continue;
            }
            self.register_sum_type_metadata(sum_def, &qualified_sum)?;
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
                    for p in params { collect_fn_arities(p, arities); }
                    collect_fn_arities(ret, arities);
                }
                Type::Named(_, args) => { for a in args { collect_fn_arities(a, arities); } }
                Type::Tuple(elems) => { for e in elems { collect_fn_arities(e, arities); } }
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
            self.lambda.ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
        }
        Ok(())
    }

    pub(super) fn register_traits_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
        type_provenance: &HashMap<String, String>,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();

        // Populate dict requirements from IR
        for (name, requirements) in &ir_module.fn_dict_requirements {
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

        for trait_def in &ir_module.traits {
            let qualified_trait = qualify_with_provenance(&ir_module.module_path, &trait_def.name, type_provenance);

            if !trait_def.is_imported {
                let methods_for_gen: Vec<(String, usize)> = trait_def.methods.iter()
                    .map(|m| (m.name.clone(), m.param_count))
                    .collect();
                let interface_bytes = generate_trait_interface_class(&qualified_trait, &methods_for_gen)?;
                result_classes.push((qualified_trait.clone(), interface_bytes));
            }

            let iface_class = self.cp.add_class(&qualified_trait)?;
            self.types.class_descriptors.insert(iface_class, format!("L{qualified_trait};"));

            let mut method_refs = HashMap::new();
            for method in &trait_def.methods {
                let mut desc = String::from("(");
                for _ in 0..method.param_count {
                    desc.push_str("Ljava/lang/Object;");
                }
                desc.push_str(")Ljava/lang/Object;");
                let mref = self.cp.add_interface_method_ref(iface_class, &method.name, &desc)?;
                method_refs.insert(method.name.clone(), mref);
            }

            let method_tc_types: HashMap<String, (Vec<Type>, Type)> = trait_def.methods.iter()
                .map(|m| (m.name.clone(), (m.param_types.clone(), m.return_type.clone())))
                .collect();

            self.traits.trait_dispatch.insert(trait_def.name.clone(), TraitDispatchInfo {
                interface_class: iface_class,
                method_refs,
                type_var_id: trait_def.type_var,
                method_tc_types,
            });
        }
        Ok(result_classes)
    }

    pub(super) fn register_builtin_instances_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
        type_provenance: &HashMap<String, String>,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();
        let local_traits: std::collections::HashSet<&str> = ir_module.traits.iter()
            .filter(|td| !td.is_imported)
            .map(|td| td.name.as_str())
            .collect();
        let registry = intrinsics::IntrinsicRegistry::new();
        for entry in registry.iter() {
            if self.traits.trait_dispatch.contains_key(entry.trait_name) {
                let q_trait = qualify_with_provenance(&ir_module.module_path, entry.trait_name, type_provenance);
                let class_name = format!("{q_trait}$${}", entry.type_name);

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
        for ((trait_name, _type_name), imported_instance) in imported_instances {
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

    pub(super) fn register_instance_defs_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
        class_name: &str,
        type_provenance: &HashMap<String, String>,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();

        // Build FnId → FnDef lookup
        let fn_defs_by_id: HashMap<krypton_ir::FnId, &krypton_ir::FnDef> = ir_module.functions.iter()
            .map(|f| (f.id, f))
            .collect();

        for inst in &ir_module.instances {
            if inst.is_intrinsic || inst.is_imported {
                continue;
            }
            let q_trait = qualify_with_provenance(&ir_module.module_path, &inst.trait_name, type_provenance);
            let instance_class_name = format!("{}$${}", q_trait, inst.target_type_name);
            let dict_requirements: Vec<DictRequirement> = inst.sub_dict_requirements.iter()
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
                let mangled = format!("{}$${}$${}", inst.trait_name, inst.target_type_name, method_name);

                // Look up the FnDef to get param/return types
                let Some(fn_def) = fn_defs_by_id.get(fn_id) else {
                    continue; // Intrinsic method — no FnDef exists
                };

                // Extract user param types (skip dict params at the front)
                let dict_count = dict_requirements.len();
                let user_params: Vec<&Type> = fn_def.params.iter()
                    .skip(dict_count)
                    .map(|(_vid, ty)| ty)
                    .collect();

                let param_jvm: Vec<JvmType> = user_params.iter()
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

                param_class_names_map.insert(method_name.clone(), class_names);
                param_jvm_types_map.insert(method_name.clone(), param_jvm);
                return_jvm_types_map.insert(method_name.clone(), ret_jvm);
                method_info.push((method_name.clone(), mangled.clone(), user_params.len(), static_desc));
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
                self.types.class_descriptors.insert(inst_class_idx, inst_desc.clone());
                let instance_field_ref = self.cp.add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;

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
                let entries = self.traits.parameterized_instances
                    .entry(inst.trait_name.clone())
                    .or_default();
                let canonical = krypton_ir::type_to_canonical_name(&inst.target_type);
                if let Some(pos) = entries.iter().position(|e| {
                    krypton_ir::type_to_canonical_name(&e.target_type) == canonical
                }) {
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
            let all_param_types: Vec<JvmType> = fn_def.params
                .iter()
                .map(|(_vid, ty)| self.type_to_jvm(ty))
                .collect::<Result<_, _>>()?;
            let return_type = self.type_to_jvm(&fn_def.return_type)?;

            let jvm_name = if name == "main" { "krypton_main" } else { name.as_str() };
            let descriptor = self.types.build_descriptor(&all_param_types, return_type);
            let method_ref =
                self.cp.add_method_ref(this_class, jvm_name, &descriptor)?;

            // tc_param_types = user params (skip dict params)
            let tc_param_types: Vec<Type> = fn_def.params
                .iter()
                .skip(impl_dict_count)
                .map(|(_vid, ty)| ty.clone())
                .collect();

            self.types.functions.entry(name.clone()).or_default().push(
                FunctionInfo {
                    method_ref,
                    param_types: all_param_types,
                    return_type,
                    is_void: false,
                    tc_param_types: tc_param_types.clone(),
                },
            );
            self.types.fn_tc_types.insert(
                name.clone(),
                (tc_param_types, fn_def.return_type.clone()),
            );
        }

        // Extern functions
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
                        ), None));
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
                        ), None));
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
            let user_param_types: Vec<JvmType> = imp.param_types
                .iter()
                .map(|t| self.type_to_jvm(t))
                .collect::<Result<_, _>>()?;
            all_param_types.extend(user_param_types);
            let return_type = self.type_to_jvm(&imp.return_type)?;

            let jvm_name = if imp.original_name == "main" { "krypton_main" } else { imp.original_name.as_str() };
            let descriptor = self.types.build_descriptor(&all_param_types, return_type);
            let method_ref = self.cp.add_method_ref(target_class, jvm_name, &descriptor)?;

            self.types.functions.entry(imp.name.clone()).or_default().push(
                FunctionInfo {
                    method_ref,
                    param_types: all_param_types,
                    return_type,
                    is_void: false,
                    tc_param_types: imp.param_types.clone(),
                },
            );
            self.types.fn_tc_types.insert(
                imp.name.clone(),
                (imp.param_types.clone(), imp.return_type.clone()),
            );
        }

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Phase 4: Function bodies (still uses TypedModule)
    // -----------------------------------------------------------------------

    pub(super) fn compile_function_bodies(
        &mut self,
        typed_module: &TypedModule,
    ) -> Result<Vec<Method>, CodegenError> {
        let mut extra_methods = Vec::new();
        let instance_method_names: std::collections::HashSet<String> = typed_module.instance_defs.iter()
            .flat_map(|inst| inst.methods.iter().map(|m| {
                krypton_typechecker::typed_ast::mangled_method_name(&inst.trait_name, &inst.target_type_name, &m.name)
            }))
            .collect();
        for typed_fn in &typed_module.functions {
            if instance_method_names.contains(&typed_fn.name) {
                continue; // compiled from instance_defs below
            }
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

    // -----------------------------------------------------------------------
    // Phase 4 (IR): Compile function bodies from ir::Module
    // -----------------------------------------------------------------------

    pub(super) fn compile_function_bodies_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
        all_ir_modules: &[krypton_ir::Module],
    ) -> Result<Vec<Method>, CodegenError> {
        self.fn_names = ir_module.fn_names.clone();

        // Build variant_tags, sum_type_params, and variant_field_types from all IR modules
        for module in all_ir_modules {
            for sum_def in &module.sum_types {
                let mut tag_map = std::collections::HashMap::new();
                for variant in &sum_def.variants {
                    tag_map.insert(variant.tag, variant.name.clone());
                    self.variant_field_types.insert(variant.name.clone(), variant.fields.clone());
                }
                self.variant_tags.insert(sum_def.name.clone(), tag_map);
                self.sum_type_params.insert(sum_def.name.clone(), sum_def.type_params.clone());
            }
        }

        // Ensure current module's sum type tags take priority over imports
        for sum_def in &ir_module.sum_types {
            let mut tag_map = std::collections::HashMap::new();
            for variant in &sum_def.variants {
                tag_map.insert(variant.tag, variant.name.clone());
                self.variant_field_types.insert(variant.name.clone(), variant.fields.clone());
            }
            self.variant_tags.insert(sum_def.name.clone(), tag_map);
            self.sum_type_params.insert(sum_def.name.clone(), sum_def.type_params.clone());
        }

        let mut extra_methods = Vec::new();
        for fn_def in &ir_module.functions {
            if fn_def.name == "main" {
                eprintln!("=== IR main ===\n{}", fn_def);
            }
            let method = self.compile_ir_function(fn_def, ir_module)?;
            extra_methods.push(method);
        }
        Ok(extra_methods)
    }

    pub(super) fn emit_main_wrapper(&mut self) -> Result<(), CodegenError> {
        let main_info = self.types.get_function("main").ok_or(CodegenError::NoMainFunction())?;
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
