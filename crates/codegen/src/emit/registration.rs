//! Module registration phases (types, traits, instances, functions).
//! All registration reads from `ir::Module`.

use std::collections::HashMap;

use krypton_ir::{TraitName, Type};
use ristretto_classfile::attributes::{Instruction, VerificationType};
use ristretto_classfile::Method;

use super::compiler::{
    CodegenError, Compiler, DictRequirement, FunctionInfo, InstanceSingletonInfo, JvmType,
    ParameterizedInstanceInfo, StructInfo, SumTypeInfo, TraitDispatchInfo, VariantField,
    VariantInfo, VecBuilderInfo,
};
use super::data_class_gen::{
    generate_sealed_interface_class, generate_struct_class, generate_variant_class,
};
use super::intrinsics;
use super::trait_class_gen::{
    generate_builtin_show_instance_class, generate_builtin_trait_instance_class,
    generate_extern_trait_bridge_class, generate_instance_class,
    generate_parameterized_instance_class, generate_trait_interface_class, TraitClassNames,
    TraitMethodSignatures,
};
use super::{
    jvm_type_to_field_descriptor, qualify_ir, type_has_vars, type_references_var,
    ImportedInstanceInfo, JvmQualifiedName,
};
use krypton_ir::substitute_type_vars;

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

fn jvm_descriptor(compiler: &Compiler, ty: JvmType) -> String {
    match ty {
        JvmType::StructRef(_) => compiler.types.jvm_type_descriptor(ty),
        other => jvm_type_to_field_descriptor(other),
    }
}

/// Resolve a type to its JVM representation for raw extern descriptors.
///
/// This must match what the Java host method actually declares. For most types,
/// `type_to_jvm` gives the right answer. The only override is `Type::Named`:
/// extern types (Vec, Map, Ref, etc.) in `struct_info` resolve to their Java
/// backing class, but Krypton-only named types (sum types, etc.) that Java
/// doesn't know about must map to Object.
fn extern_type_to_jvm(compiler: &Compiler, ty: &Type) -> Result<JvmType, CodegenError> {
    match ty {
        Type::Named(name, _) => {
            if name == "Dict" {
                return Ok(JvmType::StructRef(compiler.builder.refs.object_class));
            }
            if let Some(info) = compiler.types.struct_info.get(name) {
                Ok(JvmType::StructRef(info.class_index))
            } else {
                // Sum types, etc. — Java sees these as Object
                Ok(JvmType::StructRef(compiler.builder.refs.object_class))
            }
        }
        Type::Own(inner) => extern_type_to_jvm(compiler, inner),
        other => compiler.type_to_jvm(other),
    }
}

fn extern_param_info(compiler: &Compiler, ty: &Type) -> Result<(JvmType, String), CodegenError> {
    let jvm = extern_type_to_jvm(compiler, ty)?;
    Ok((jvm, jvm_descriptor(compiler, jvm)))
}

fn extern_return_info(
    compiler: &Compiler,
    ty: &Type,
    nullable: bool,
    throws: bool,
) -> Result<(JvmType, String, bool), CodegenError> {
    if nullable {
        let jvm = compiler.nullable_host_return_jvm(ty)?;
        return Ok((jvm, jvm_descriptor(compiler, jvm), false));
    }
    if throws {
        let inner = compiler.throws_inner_type(ty)?;
        if matches!(inner, Type::Unit) {
            // @throws with Unit inner type: raw Java method returns void
            return Ok((JvmType::Int, "V".to_string(), true));
        }
        let jvm = compiler.type_to_jvm(inner)?;
        return Ok((jvm, jvm_descriptor(compiler, jvm), false));
    }
    if matches!(ty, Type::Unit) {
        return Ok((JvmType::Int, "V".to_string(), true));
    }
    let jvm = extern_type_to_jvm(compiler, ty)?;
    Ok((jvm, jvm_descriptor(compiler, jvm), false))
}

impl<'link> Compiler<'link> {
    /// Number of dictionary parameters prepended to a function by
    /// where-clause dict passing. Keyed by FnId so overload siblings with
    /// distinct constraint sets resolve independently.
    fn dict_count_for(&self, fn_id: krypton_ir::FnId) -> usize {
        self.traits
            .impl_dict_requirements
            .get(&fn_id)
            .map(|r| r.len())
            .unwrap_or(0)
    }

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
            if path.as_str() == module_path {
                continue;
            }
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
            if path.as_str() == module_path {
                continue;
            }
            let TypeSummaryKind::Record { fields } = &ts.kind else {
                continue;
            };
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
            let ir_fields: Vec<(String, krypton_ir::Type)> = fields
                .iter()
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
            if path.as_str() == module_path {
                continue;
            }
            let TypeSummaryKind::Sum { variants } = &ts.kind else {
                continue;
            };
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
            let ir_variants: Vec<krypton_ir::VariantDef> = variants
                .iter()
                .enumerate()
                .map(|(tag, v)| krypton_ir::VariantDef {
                    name: v.name.clone(),
                    tag: tag as u32,
                    fields: v
                        .fields
                        .iter()
                        .map(|ty| krypton_ir::Type::from(ty.clone()))
                        .collect(),
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

    /// Ensure the `Never` empty sum type is always registered.
    ///
    /// `panic`/`todo`/`unreachable` are intrinsics that return `Never`, so every
    /// module implicitly references the type even without importing `core/never`.
    pub(super) fn ensure_never_registered(&mut self) -> Result<(), CodegenError> {
        if self.types.sum_type_info.contains_key("Never") {
            return Ok(());
        }
        let qualified = "core/never/Never";
        let class_index = self.cp.add_class(qualified)?;
        let desc = format!("L{qualified};");
        self.types.class_descriptors.insert(class_index, desc);
        self.types.sum_type_info.insert(
            "Never".to_string(),
            SumTypeInfo {
                interface_class_index: class_index,
                variants: HashMap::new(),
            },
        );
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

        // Populate dict requirements from IR (FnId-keyed)
        for (fn_id, requirements) in &ir_module.fn_dict_requirements {
            self.traits
                .impl_dict_requirements
                .entry(*fn_id)
                .or_insert_with(|| {
                    requirements
                        .iter()
                        .map(|(trait_name, type_vars)| DictRequirement {
                            trait_name: trait_name.clone(),
                            type_vars: type_vars.clone(),
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
                let interface_bytes = generate_trait_interface_class(
                    &qualified_trait,
                    &methods_for_gen,
                    trait_def.direct_superclasses.len(),
                )?;
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

    /// Register extern trait bridge classes for Java interface adaptation.
    pub(super) fn register_extern_traits_ir(
        &mut self,
        ir_module: &krypton_ir::Module,
    ) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
        let mut result_classes = Vec::new();

        for extern_trait in &ir_module.extern_traits {
            let krypton_trait_name = extern_trait.trait_name.jvm_qualified();
            let java_interface = extern_trait.java_interface.replace('.', "/");
            let bridge_class_name = format!("{krypton_trait_name}$$Bridge");

            // Resolve Java types for each bridge method
            let methods: Vec<super::trait_class_gen::BridgeMethodInfo> = extern_trait
                .methods
                .iter()
                .map(|m| {
                    let java_param_descs: Vec<String> = m
                        .param_types
                        .iter()
                        .map(|ty| {
                            let jvm = extern_type_to_jvm(self, ty)?;
                            Ok(jvm_descriptor(self, jvm))
                        })
                        .collect::<Result<_, CodegenError>>()?;
                    let is_void_return = matches!(m.return_type, krypton_ir::Type::Unit);
                    let java_return_desc = if is_void_return {
                        "V".to_string()
                    } else {
                        let jvm = extern_type_to_jvm(self, &m.return_type)?;
                        jvm_descriptor(self, jvm)
                    };
                    // krypton_param_count = self + non-self params
                    let krypton_param_count = m.param_types.len() + 1;
                    Ok(super::trait_class_gen::BridgeMethodInfo {
                        name: m.name.clone(),
                        java_param_descs,
                        java_return_desc,
                        is_void_return,
                        krypton_param_count,
                    })
                })
                .collect::<Result<_, CodegenError>>()?;

            let bridge_bytes = generate_extern_trait_bridge_class(
                &bridge_class_name,
                &java_interface,
                &krypton_trait_name,
                &methods,
            )?;
            result_classes.push((bridge_class_name.clone(), bridge_bytes));

            // Register bridge class and constructor in the constant pool
            let bridge_class_idx = self.cp.add_class(&bridge_class_name)?;
            let bridge_init = self.cp.add_method_ref(
                bridge_class_idx,
                "<init>",
                "(Ljava/lang/Object;Ljava/lang/Object;)V",
            )?;

            self.traits.extern_trait_bridges.insert(
                extern_trait.trait_name.clone(),
                super::compiler::ExternTraitBridgeInfo {
                    bridge_class: bridge_class_idx,
                    bridge_init,
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
                    (trait_key, vec![builtin_type]),
                    InstanceSingletonInfo { instance_field_ref },
                );
            }
        }
        Ok(result_classes)
    }

    pub(super) fn register_imported_instances(
        &mut self,
        imported_instances: &HashMap<(TraitName, Vec<krypton_ir::Type>), ImportedInstanceInfo>,
    ) -> Result<(), CodegenError> {
        for ((trait_name, _target_types), imported_instance) in imported_instances {
            let inst_class_idx = self.cp.add_class(&imported_instance.class_name)?;
            let inst_desc = format!("L{};", imported_instance.class_name);
            self.types
                .class_descriptors
                .insert(inst_class_idx, inst_desc.clone());
            let is_parameterized = imported_instance.target_types.iter().any(type_has_vars);
            if !is_parameterized {
                let instance_field_ref =
                    self.cp
                        .add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;
                self.traits.instance_singletons.insert(
                    (trait_name.clone(), imported_instance.target_types.clone()),
                    InstanceSingletonInfo { instance_field_ref },
                );
            } else {
                self.traits
                    .parameterized_instances
                    .entry(trait_name.clone())
                    .or_default()
                    .push(ParameterizedInstanceInfo {
                        class_name: imported_instance.class_name.clone(),
                        target_types: imported_instance.target_types.clone(),
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
        instance_class_map: &HashMap<(TraitName, Vec<krypton_ir::Type>), ImportedInstanceInfo>,
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
                ir_module.module_path.as_str(),
                inst.trait_name.local_name,
                inst.target_type_name
            );
            // The trait interface class uses the qualified trait name
            let q_trait = inst.trait_name.jvm_qualified();
            let dict_requirements: Vec<DictRequirement> = inst
                .sub_dict_requirements
                .iter()
                .map(|(trait_name, type_vars)| DictRequirement {
                    trait_name: trait_name.clone(),
                    type_vars: type_vars.clone(),
                })
                .collect();

            // Superclass slots are stored on the instance class at class-load
            // time, not passed as static-method parameters. Only impl-head
            // sub_dicts appear in FnDef params (see lower.rs instance method
            // assembly). Split the dict count along the layout boundary:
            // sub_dict_requirements[..superclass_count] are slot-only;
            // sub_dict_requirements[superclass_count..] are fn-def params.
            let superclass_count = ir_module
                .traits
                .iter()
                .find(|t| t.trait_name == inst.trait_name)
                .map(|t| t.direct_superclasses.len())
                .unwrap_or(0);
            let impl_head_count = dict_requirements.len() - superclass_count;

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

                // Skip impl-head dict params (the FnDef params), NOT the
                // superclass-slot count.
                let user_params: Vec<&Type> = fn_def
                    .params
                    .iter()
                    .skip(impl_head_count)
                    .map(|(_vid, ty)| ty)
                    .collect();

                let param_jvm: Vec<JvmType> = user_params
                    .iter()
                    .map(|t| self.type_to_jvm(t))
                    .collect::<Result<_, _>>()?;
                let ret_jvm = self.type_to_jvm(&fn_def.return_type)?;

                self.traits
                    .impl_dict_requirements
                    .insert(*fn_id, dict_requirements.clone());

                let mut all_param_jvm = Vec::new();
                // Static method signature: impl-head dict params + user params.
                for _ in 0..impl_head_count {
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

            let is_parameterized = inst.target_types.iter().any(type_has_vars);

            if !is_parameterized {
                // Resolve each superclass slot to its concrete source class
                // name. The slot's target is the ancestor's trait applied to
                // the substituted position tuple: look up the trait's stored
                // superclass args, substitute `inst.target_types` for the
                // trait's own `type_var_ids`, and use the result as the lookup
                // key. For single-parameter traits this is the same target
                // tuple as the descendant's; for multi-parameter traits it
                // may be a permutation or subset (e.g. `Codec[fmt, ty]` with
                // superclass `MyShow[ty]` substitutes to `[Int]`).
                let trait_def = ir_module
                    .traits
                    .iter()
                    .find(|t| t.trait_name == inst.trait_name)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: no TraitDef in ir_module for instance {}[{}]",
                            inst.trait_name.local_name, inst.target_type_name,
                        )
                    });
                let mut superclass_slots: Vec<super::trait_class_gen::ConcreteSuperclassSlot<'_>> =
                    Vec::new();
                let direct_scs = trait_def.direct_superclasses.as_slice();
                let trait_params = trait_def.type_var_ids.as_slice();
                for (slot_idx, (sc_trait, _)) in inst.sub_dict_requirements.iter().enumerate() {
                    // Superclass slots come first in sub_dict_requirements,
                    // in the same order as direct_superclasses.
                    if slot_idx >= direct_scs.len() || trait_params.len() != inst.target_types.len()
                    {
                        return Err(CodegenError::TypeError(
                            format!(
                                "ICE: superclass slot {} out of range / arity mismatch for {}[{}]",
                                slot_idx, inst.trait_name.local_name, inst.target_type_name,
                            ),
                            None,
                        ));
                    }
                    let sc_target_types: Vec<Type> = direct_scs[slot_idx]
                        .1
                        .iter()
                        .map(|t| substitute_type_vars(t, trait_params, &inst.target_types))
                        .collect();
                    let key = (sc_trait.clone(), sc_target_types.clone());
                    let src_info = instance_class_map.get(&key).ok_or_else(|| {
                        let target_display = sc_target_types
                            .iter()
                            .map(|t| format!("{}", t))
                            .collect::<Vec<_>>()
                            .join(", ");
                        CodegenError::TypeError(
                            format!(
                                "ICE: no class entry for superclass slot {}[{}] of {}[{}]",
                                sc_trait.local_name,
                                target_display,
                                inst.trait_name.local_name,
                                inst.target_type_name,
                            ),
                            None,
                        )
                    })?;
                    superclass_slots.push(super::trait_class_gen::ConcreteSuperclassSlot {
                        index: slot_idx,
                        source_class: src_info.class_name.as_str(),
                    });
                }
                let instance_bytes = generate_instance_class(
                    &instance_class_name,
                    &q_trait,
                    class_name,
                    &method_info,
                    &param_jvm_types_map,
                    &return_jvm_types_map,
                    &param_class_names_map,
                    &superclass_slots,
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
                    (inst.trait_name.clone(), inst.target_types.clone()),
                    InstanceSingletonInfo { instance_field_ref },
                );
            } else {
                // Look up the superclass count for this instance's trait.
                // Direct superclasses always lay out at the front of the
                // sub_dict slots (see InstanceDef layout rule).
                let superclass_count = ir_module
                    .traits
                    .iter()
                    .find(|t| t.trait_name == inst.trait_name)
                    .map(|t| t.direct_superclasses.len())
                    .unwrap_or(0);
                let instance_bytes = generate_parameterized_instance_class(
                    TraitClassNames {
                        class: &instance_class_name,
                        trait_interface: &q_trait,
                        main: class_name,
                    },
                    TraitMethodSignatures {
                        methods: &method_info,
                        param_jvm_types: &param_jvm_types_map,
                        return_jvm_types: &return_jvm_types_map,
                        param_class_names: &param_class_names_map,
                    },
                    dict_requirements.len(),
                    superclass_count,
                )?;
                result_classes.push((instance_class_name.clone(), instance_bytes));

                let new_info = ParameterizedInstanceInfo {
                    class_name: instance_class_name.clone(),
                    target_types: inst.target_types.clone(),
                    requirements: dict_requirements,
                };
                let entries = self
                    .traits
                    .parameterized_instances
                    .entry(inst.trait_name.clone())
                    .or_default();
                let canonical: Vec<String> = inst
                    .target_types
                    .iter()
                    .map(krypton_ir::type_to_canonical_name)
                    .collect();
                if let Some(pos) = entries.iter().position(|e| {
                    e.target_types
                        .iter()
                        .map(krypton_ir::type_to_canonical_name)
                        .collect::<Vec<_>>()
                        == canonical
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
        if !self.types.struct_info.contains_key("Vec") {
            return Ok(());
        }
        let Some(builder_struct) = self.types.struct_info.get("VecBuilder") else {
            return Ok(());
        };
        let builder_class = builder_struct.class_index;
        let builder_new = self.cp.add_method_ref(
            builder_class,
            "builderNew",
            "()Lkrypton/runtime/KryptonArrayBuilder;",
        )?;
        let builder_push = self.cp.add_method_ref(
            builder_class,
            "builderPush",
            "(Lkrypton/runtime/KryptonArrayBuilder;Ljava/lang/Object;)Lkrypton/runtime/KryptonArrayBuilder;",
        )?;
        let builder_freeze = self.cp.add_method_ref(
            builder_class,
            "builderFreeze",
            "(Lkrypton/runtime/KryptonArrayBuilder;)Lkrypton/runtime/KryptonArray;",
        )?;
        self.vec_builder_info = Some(VecBuilderInfo {
            builder_class_index: builder_class,
            builder_new_ref: builder_new,
            builder_push_ref: builder_push,
            builder_freeze_ref: builder_freeze,
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
            let impl_dict_count = self.dict_count_for(fn_def.id);

            // FnDef params already include dict params prepended by the lowerer.
            // We need to build the JVM descriptor from all params.
            let all_param_types: Vec<JvmType> = fn_def
                .params
                .iter()
                .map(|(_vid, ty)| self.type_to_jvm(ty))
                .collect::<Result<_, _>>()?;
            let return_type = self.type_to_jvm(&fn_def.return_type)?;

            // JVM supports method-level overloading via descriptor, so the
            // method name stays `fn_def.name` (not `exported_symbol`) —
            // `javap` output stays readable and the verifier disambiguates
            // via the descriptor.
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

            let fn_info = FunctionInfo {
                method_ref,
                param_types: all_param_types,
                return_type,
                is_void: false,
            };
            self.types
                .functions
                .entry(name.clone())
                .or_default()
                .push(fn_info.clone());
            self.types.fn_tc_types.insert(
                name.clone(),
                (tc_param_types.clone(), fn_def.return_type.clone()),
            );
            // Overload-safe mirrors keyed by FnId.
            self.types.fn_info_by_id.insert(fn_def.id, fn_info);
            self.types
                .fn_tc_types_by_id
                .insert(fn_def.id, (tc_param_types, fn_def.return_type.clone()));
        }

        // Register wrapper method refs for all Java externs (nullable and non-nullable).
        // The wrapper lives on this_class; consumers import it as a regular function.
        for ext in ir_module
            .extern_fns
            .iter()
            .filter(|ext| matches!(ext.target, krypton_ir::ExternTarget::Java { .. }))
        {
            let impl_dict_count = self.dict_count_for(ext.id);
            let object_class = self.builder.refs.object_class;
            let mut wrapper_param_types: Vec<JvmType> = Vec::new();
            for _ in 0..impl_dict_count {
                wrapper_param_types.push(JvmType::StructRef(object_class));
            }
            let user_param_types: Vec<JvmType> = ext
                .param_types
                .iter()
                .map(|ty| self.type_to_jvm(ty))
                .collect::<Result<_, _>>()?;
            wrapper_param_types.extend(user_param_types);
            let wrapper_return_type = self.type_to_jvm(&ext.return_type)?;
            let wrapper_desc = self
                .types
                .build_descriptor(&wrapper_param_types, wrapper_return_type);
            let wrapper_ref = self
                .cp
                .add_method_ref(this_class, &ext.name, &wrapper_desc)?;
            let wrapper_info = FunctionInfo {
                method_ref: wrapper_ref,
                param_types: wrapper_param_types,
                return_type: wrapper_return_type,
                is_void: false,
            };
            self.types
                .functions
                .entry(ext.name.clone())
                .or_insert_with(|| vec![wrapper_info.clone()]);
            // Externs are singletons (check_duplicate_function_names
            // forbids extern overloads), but the Call site dispatches by
            // FnId — mirror into the FnId-keyed map so lookup succeeds.
            self.types.fn_info_by_id.insert(ext.id, wrapper_info);
        }

        // Register raw extern method refs (pointing to the actual Java host class).
        // These are used by the wrapper body to invoke the real extern.
        for ext in &ir_module.extern_fns {
            let (_, extern_class) = match &ext.target {
                krypton_ir::ExternTarget::Java { class } => {
                    let jvm = class.replace('.', "/");
                    let ci = self.cp.add_class(&jvm)?;
                    (jvm, ci)
                }
                krypton_ir::ExternTarget::Js { .. } => continue,
            };

            // Store extern class index for constructor codegen
            self.raw_extern_classes
                .insert(ext.name.clone(), extern_class);

            let skip_first = ext.call_kind == krypton_ir::ExternCallKind::Instance;

            let mut param_jvm_types = Vec::new();
            let mut param_desc = String::from("(");
            for (i, pt) in ext.param_types.iter().enumerate() {
                if skip_first && i == 0 {
                    continue; // self param not part of JVM descriptor
                }
                let bridge = ext.bridge_params.get(i).and_then(|b| b.as_ref());
                if let Some(bridge) = bridge {
                    // Bridged param: use the Java interface type, not Object
                    let iface_jvm = bridge.java_interface.replace('.', "/");
                    let iface_class = self.cp.add_class(&iface_jvm)?;
                    param_jvm_types.push(JvmType::StructRef(iface_class));
                    param_desc.push_str(&format!("L{iface_jvm};"));
                } else {
                    let (jvm, desc) = extern_param_info(self, pt)?;
                    param_jvm_types.push(jvm);
                    param_desc.push_str(&desc);
                }
            }

            // Append non-bridged dict params to the raw descriptor.
            // When an extern has `where k: Eq + Hash` and Eq/Hash are not extern traits
            // (no bridge class), we pass the dict objects directly to the Java host method.
            let dict_requirements = self
                .traits
                .impl_dict_requirements
                .get(&ext.id)
                .cloned()
                .unwrap_or_default();
            for dr in &dict_requirements {
                if !self
                    .traits
                    .extern_trait_bridges
                    .contains_key(&dr.trait_name)
                {
                    let object_class = self.builder.refs.object_class;
                    param_jvm_types.push(JvmType::StructRef(object_class));
                    param_desc.push_str("Ljava/lang/Object;");
                }
            }

            param_desc.push(')');

            match ext.call_kind {
                krypton_ir::ExternCallKind::Constructor => {
                    // Java <init> always returns void; wrapper produces the new'd object
                    let descriptor = format!("{param_desc}V");
                    let method_ref = self
                        .cp
                        .add_method_ref(extern_class, "<init>", &descriptor)?;
                    let info = FunctionInfo {
                        method_ref,
                        param_types: param_jvm_types,
                        return_type: JvmType::StructRef(extern_class),
                        is_void: false,
                    };
                    self.raw_extern_functions.insert(ext.name.clone(), info);
                }
                _ => {
                    let (return_type, ret_desc, is_void) =
                        extern_return_info(self, &ext.return_type, ext.nullable, ext.throws)?;
                    let descriptor = format!("{param_desc}{ret_desc}");
                    let method_ref =
                        self.cp
                            .add_method_ref(extern_class, &ext.name, &descriptor)?;
                    let info = FunctionInfo {
                        method_ref,
                        param_types: param_jvm_types,
                        return_type,
                        is_void,
                    };
                    self.raw_extern_functions.insert(ext.name.clone(), info);
                }
            }
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

            let impl_dict_count = self.dict_count_for(imp.id);
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

            let fn_info = FunctionInfo {
                method_ref,
                param_types: all_param_types,
                return_type,
                is_void: false,
            };
            self.types
                .functions
                .entry(imp.name.clone())
                .or_default()
                .push(fn_info.clone());
            self.types.fn_tc_types.insert(
                imp.name.clone(),
                (imp.param_types.clone(), imp.return_type.clone()),
            );
            // Overload-safe FnId-keyed mirrors.
            self.types.fn_info_by_id.insert(imp.id, fn_info);
            self.types
                .fn_tc_types_by_id
                .insert(imp.id, (imp.param_types.clone(), imp.return_type.clone()));
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
            if path.as_str() == ir_module.module_path.as_str() {
                continue;
            }
            let krypton_typechecker::module_interface::TypeSummaryKind::Sum { variants } = &ts.kind
            else {
                continue;
            };
            let mut tag_map = std::collections::HashMap::new();
            for (tag, variant) in variants.iter().enumerate() {
                tag_map.insert(tag as u32, variant.name.clone());
                let ir_fields: Vec<krypton_ir::Type> = variant
                    .fields
                    .iter()
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
            .filter(|ext| matches!(ext.target, krypton_ir::ExternTarget::Java { .. }))
        {
            if ext.nullable {
                extra_methods.push(self.compile_nullable_extern_wrapper(ext)?);
            } else if ext.throws {
                extra_methods.push(self.compile_throws_extern_wrapper(ext)?);
            } else {
                extra_methods.push(self.compile_nonnullable_extern_wrapper(ext)?);
            }
        }
        Ok(extra_methods)
    }

    /// Emit the raw extern call parameters for the wrapper body.
    ///
    /// The wrapper has `dict_count` leading dict params followed by user params.
    /// For non-bridged user params, we load them directly. For bridged params,
    /// we construct a bridge class instance wrapping the user value and its dict.
    fn emit_extern_call_params(
        &mut self,
        ext: &krypton_ir::ExternFnDef,
        param_slots: &[(u16, JvmType)],
        dict_count: usize,
    ) -> Result<(), CodegenError> {
        if dict_count == 0 {
            // No dicts — load all params directly (the common case)
            for (slot, jvm_ty) in param_slots {
                self.builder.emit_load(*slot, *jvm_ty);
            }
            return Ok(());
        }

        // Build a mapping from trait_name → dict slot index for bridged params.
        let dict_requirements = self
            .traits
            .impl_dict_requirements
            .get(&ext.id)
            .cloned()
            .unwrap_or_default();

        // Only load user params (skip dict params), constructing bridges where needed.
        let user_param_slots = &param_slots[dict_count..];
        for (user_idx, (slot, jvm_ty)) in user_param_slots.iter().enumerate() {
            let bridge = ext.bridge_params.get(user_idx).and_then(|b| b.as_ref());
            if let Some(bridge) = bridge {
                // Find the dict slot for this bridge's trait
                let dict_slot_idx = dict_requirements
                    .iter()
                    .position(|dr| dr.trait_name == bridge.trait_name)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: No dict requirement found for bridge trait {:?} on extern {}",
                            bridge.trait_name, ext.name
                        )
                    });
                let (dict_slot, _) = param_slots[dict_slot_idx];

                // Look up bridge class info
                let bridge_info = self
                    .traits
                    .extern_trait_bridges
                    .get(&bridge.trait_name)
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: No bridge class info for trait {:?}",
                            bridge.trait_name
                        )
                    });
                let bridge_class = bridge_info.bridge_class;
                let bridge_init = bridge_info.bridge_init;

                // new BridgeClass; dup; aload value; aload dict; invokespecial <init>
                self.builder.emit_new_dup(bridge_class);
                self.builder.emit_load(*slot, *jvm_ty);
                self.builder.emit_load(
                    dict_slot,
                    JvmType::StructRef(self.builder.refs.object_class),
                );
                // Frame: [... Uninitialized Uninitialized value dict]
                // invokespecial pops: dict, value, dup'd Uninitialized, new Uninitialized
                // then pushes: initialized Object ref
                self.builder.frame.pop_type(); // dict
                self.builder.frame.pop_type(); // value
                self.builder.frame.pop_type(); // dup'd Uninitialized
                self.builder.frame.pop_type(); // new Uninitialized
                self.builder.emit(Instruction::Invokespecial(bridge_init));
                self.builder.push_jvm_type(JvmType::StructRef(bridge_class));
            } else {
                self.builder.emit_load(*slot, *jvm_ty);
            }
        }

        // Load non-bridged dict params after user params.
        // These are dicts for where-clause constraints on traits that don't have
        // extern trait bridges (e.g., Eq, Hash on map operations).
        for (dict_idx, dr) in dict_requirements.iter().enumerate() {
            if !self
                .traits
                .extern_trait_bridges
                .contains_key(&dr.trait_name)
            {
                let (dict_slot, dict_jvm) = param_slots[dict_idx];
                self.builder.emit_load(dict_slot, dict_jvm);
            }
        }
        Ok(())
    }

    /// Emit the raw Java invoke for an extern function. Handles static, instance,
    /// and constructor call kinds. Returns `Some(jvm_type)` for the result on the
    /// stack, or `None` if the call is void.
    fn emit_extern_invoke(
        &mut self,
        ext: &krypton_ir::ExternFnDef,
        raw_info: &FunctionInfo,
        param_slots: &[(u16, JvmType)],
        dict_count: usize,
    ) -> Result<Option<JvmType>, CodegenError> {
        match ext.call_kind {
            krypton_ir::ExternCallKind::Static => {
                self.emit_extern_call_params(ext, param_slots, dict_count)?;
                for jvm_ty in raw_info.param_types.iter().rev() {
                    self.builder.pop_jvm_type(*jvm_ty);
                }
                self.builder
                    .emit(Instruction::Invokestatic(raw_info.method_ref));
                if raw_info.is_void {
                    Ok(None)
                } else {
                    self.builder.push_jvm_type(raw_info.return_type);
                    Ok(Some(raw_info.return_type))
                }
            }
            krypton_ir::ExternCallKind::Instance => {
                self.emit_extern_call_params(ext, param_slots, dict_count)?;
                // Pop non-self params (raw_info.param_types excludes self)
                for jvm_ty in raw_info.param_types.iter().rev() {
                    self.builder.pop_jvm_type(*jvm_ty);
                }
                // Pop self (objectref) — first param in ext.param_types
                let self_jvm = extern_type_to_jvm(self, &ext.param_types[0])?;
                self.builder.pop_jvm_type(self_jvm);
                self.builder
                    .emit(Instruction::Invokevirtual(raw_info.method_ref));
                if raw_info.is_void {
                    Ok(None)
                } else {
                    self.builder.push_jvm_type(raw_info.return_type);
                    Ok(Some(raw_info.return_type))
                }
            }
            krypton_ir::ExternCallKind::Constructor => {
                let extern_class = *self
                    .raw_extern_classes
                    .get(&ext.name)
                    .expect("ICE: no extern class for constructor");
                self.builder.emit_new_dup(extern_class);
                self.emit_extern_call_params(ext, param_slots, dict_count)?;
                for jvm_ty in raw_info.param_types.iter().rev() {
                    self.builder.pop_jvm_type(*jvm_ty);
                }
                self.builder.frame.pop_type(); // pop dup'd Uninitialized
                self.builder.frame.pop_type(); // pop new Uninitialized
                self.builder
                    .emit(Instruction::Invokespecial(raw_info.method_ref));
                let result = JvmType::StructRef(extern_class);
                self.builder.push_jvm_type(result);
                Ok(Some(result))
            }
        }
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

        let dict_count = self.dict_count_for(ext.id);
        let invoke_result = self.emit_extern_invoke(ext, &raw_info, &param_slots, dict_count)?;
        let result_jvm = invoke_result.expect("ICE: @nullable extern must not return void");

        let raw_slot = self.builder.alloc_anonymous_local(result_jvm);
        self.builder.emit(Instruction::Astore(raw_slot as u8));
        self.builder.frame.pop_type();

        self.builder.emit(Instruction::Aload(raw_slot as u8));
        self.builder.push_jvm_type(result_jvm);
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
        self.builder.push_jvm_type(result_jvm);

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
            _ => result_jvm,
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

    fn compile_throws_extern_wrapper(
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

        let dict_count = self.dict_count_for(ext.id);

        // try_start:
        let try_start = self.builder.current_offset();

        // Load params and invoke the raw extern
        let invoke_result = self.emit_extern_invoke(ext, &raw_info, &param_slots, dict_count)?;

        let (ok_class, ok_ctor, result_iface, ok_fields) =
            self.result_variant_construct_info(&ext.return_type, "Ok")?;

        match invoke_result {
            Some(result_jvm) => {
                // Non-void: store raw result so we can emit new/dup before the value
                let raw_slot = self.builder.alloc_anonymous_local(result_jvm);
                self.builder.emit_store(raw_slot, result_jvm);

                self.builder.emit_new_dup(ok_class);
                self.builder.emit_load(raw_slot, result_jvm);

                let expected = if ok_fields[0].is_erased {
                    JvmType::StructRef(self.builder.refs.object_class)
                } else {
                    ok_fields[0].jvm_type
                };
                self.emit_type_coercion(result_jvm, expected);
                self.emit_variant_invokespecial(ok_ctor, &ok_fields, result_iface);
            }
            None => {
                // Void return (e.g., Result[String, Unit]): wrap Unit in Ok
                self.builder.emit_new_dup(ok_class);
                self.builder.emit(Instruction::Iconst_0); // Unit value
                self.builder.push_jvm_type(JvmType::Int);
                let expected = if ok_fields[0].is_erased {
                    JvmType::StructRef(self.builder.refs.object_class)
                } else {
                    ok_fields[0].jvm_type
                };
                self.emit_type_coercion(JvmType::Int, expected);
                self.emit_variant_invokespecial(ok_ctor, &ok_fields, result_iface);
            }
        }
        self.builder.emit(Instruction::Areturn);

        // try_end (one past the last protected instruction):
        let try_end = self.builder.current_offset();

        // handler: catch java/lang/Exception
        let handler = self.builder.current_offset();
        // Record frame at handler — only params in locals (raw_slot not yet initialized)
        let exception_class = self.cp.add_class("java/lang/Exception")?;
        self.builder.frame.stack_types.clear();
        self.builder.frame.local_types.clear();
        for (_, jvm_ty) in &param_slots {
            self.builder
                .frame
                .local_types
                .extend(self.builder.jvm_type_to_vtypes(*jvm_ty));
        }
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: exception_class,
        });
        self.builder.frame.record_frame(handler);

        // Store exception, get message into a local
        let exc_slot = self
            .builder
            .alloc_anonymous_local(JvmType::StructRef(exception_class));
        self.builder.emit(Instruction::Astore(exc_slot as u8));
        self.builder.frame.pop_type();

        self.builder.emit(Instruction::Aload(exc_slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: exception_class,
        });
        let get_message =
            self.cp
                .add_method_ref(exception_class, "getMessage", "()Ljava/lang/String;")?;
        self.builder.emit(Instruction::Invokevirtual(get_message));
        self.builder.frame.pop_type(); // pop exception
        let string_jvm = JvmType::StructRef(self.builder.refs.string_class);
        self.builder.push_jvm_type(string_jvm);

        // Store message string, then new Err, dup, load message, invokespecial
        let msg_slot = self.builder.alloc_anonymous_local(string_jvm);
        self.builder.emit_store(msg_slot, string_jvm);

        let (err_class, err_ctor, err_result_iface, err_fields) =
            self.result_variant_construct_info(&ext.return_type, "Err")?;

        self.builder.emit_new_dup(err_class);
        self.builder.emit_load(msg_slot, string_jvm);

        let err_expected = if err_fields[0].is_erased {
            JvmType::StructRef(self.builder.refs.object_class)
        } else {
            err_fields[0].jvm_type
        };
        self.emit_type_coercion(string_jvm, err_expected);
        self.emit_variant_invokespecial(err_ctor, &err_fields, err_result_iface);
        self.builder.emit(Instruction::Areturn);

        // Add exception table entry
        self.builder
            .add_exception_entry(try_start..try_end, handler, exception_class);

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

    fn compile_nonnullable_extern_wrapper(
        &mut self,
        ext: &krypton_ir::ExternFnDef,
    ) -> Result<Method, CodegenError> {
        self.reset_method_state();

        let wrapper_info = self
            .types
            .get_function(&ext.name)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "ICE: No wrapper FunctionInfo for non-nullable extern '{}'",
                    ext.name
                )
            });
        let raw_info = self
            .raw_extern_functions
            .get(&ext.name)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "ICE: No raw FunctionInfo for non-nullable extern '{}'",
                    ext.name
                )
            });

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

        let dict_count = self.dict_count_for(ext.id);

        // Load params and invoke the raw extern
        let invoke_result = self.emit_extern_invoke(ext, &raw_info, &param_slots, dict_count)?;
        match invoke_result {
            None => {
                // Void → push Unit (Iconst_0)
                self.builder.emit(Instruction::Iconst_0);
                self.builder.push_jvm_type(JvmType::Int);
            }
            Some(actual) => {
                self.emit_type_coercion(actual, wrapper_info.return_type);
            }
        }

        let ret_instr = match wrapper_info.return_type {
            JvmType::Long => Instruction::Lreturn,
            JvmType::Double => Instruction::Dreturn,
            JvmType::Int => Instruction::Ireturn,
            JvmType::StructRef(_) => Instruction::Areturn,
        };
        self.builder.emit(ret_instr);

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
