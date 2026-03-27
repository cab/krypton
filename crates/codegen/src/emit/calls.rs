//! Function call resolution, dict/trait dispatch, and call emission.

use std::collections::HashMap;

use krypton_ir::{bind_type_vars, TraitName, Type};
use ristretto_classfile::attributes::{Instruction, VerificationType};

use super::compiler::{
    CodegenError, Compiler, DictRequirement, JvmType, ParameterizedInstanceInfo,
};

impl Compiler {
    /// Coerce an Object result from invokeinterface to the expected JVM type.
    /// Used by both higher-order calls and trait method dispatch.
    pub(super) fn coerce_interface_return(&mut self, expected_ret: JvmType) {
        // Push Object result onto frame
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });
        // Unbox primitives
        self.builder.unbox_if_needed(expected_ret);
        // Checkcast for StructRef
        match expected_ret {
            JvmType::StructRef(idx) if idx != self.builder.refs.object_class => {
                self.builder.emit(Instruction::Checkcast(idx));
                self.builder.frame.pop_type();
                self.builder
                    .frame
                    .push_type(VerificationType::Object { cpool_index: idx });
            }
            _ => {}
        }
    }

    // --- Dict / trait resolution helpers ---

    pub(super) fn resolve_dict_requirement_type(
        requirement: &DictRequirement,
        instance_info: &ParameterizedInstanceInfo,
        concrete_ty: &Type,
    ) -> Option<Type> {
        let type_var = &requirement.type_var;
        let mut bindings = HashMap::new();
        if bind_type_vars(&instance_info.target_type, concrete_ty, &mut bindings) {
            bindings.get(type_var).cloned()
        } else {
            None
        }
    }

    pub(super) fn resolve_function_ref_requirement_type(
        requirement: &DictRequirement,
        declared_param_types: &[Type],
        actual_param_types: &[Type],
    ) -> Option<Type> {
        let type_var = &requirement.type_var;
        let mut bindings = HashMap::new();
        for (declared, actual) in declared_param_types.iter().zip(actual_param_types.iter()) {
            if !bind_type_vars(declared, actual, &mut bindings) {
                return None;
            }
        }
        bindings.get(type_var).cloned()
    }

    pub(super) fn emit_dict_argument_for_type(
        &mut self,
        trait_name: &TraitName,
        ty: &Type,
        pushed_class: u16,
    ) -> Result<(), CodegenError> {
        if matches!(ty, Type::Var(_))
            || matches!(ty, Type::App(ctor, _) if Self::is_abstract_type_ctor(ctor))
        {
            let var_id = match ty {
                Type::Var(id) => Some(*id),
                Type::App(ctor, _) => match ctor.as_ref() {
                    Type::Var(id) => Some(*id),
                    _ => None,
                },
                _ => None,
            };
            let dict_slot = var_id
                .and_then(|id| self.traits.get_dict_local(trait_name, id))
                .or_else(|| self.traits.get_dict_local_by_trait(trait_name));
            if let Some(dict_slot) = dict_slot {
                self.builder.emit(Instruction::Aload(dict_slot as u8));
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: pushed_class,
                });
                // Dict locals are declared as Object; cast to the interface type
                if pushed_class != self.builder.refs.object_class {
                    self.builder.emit(Instruction::Checkcast(pushed_class));
                }
                return Ok(());
            }
        }

        let lookup_type = ty.strip_own();
        // Try full type first (concrete instances), then head-only (HKT instances like Functor[Box])
        let singleton_key = (trait_name.clone(), lookup_type.clone());
        let head_key = (
            trait_name.clone(),
            Type::Named(krypton_ir::head_type_name(ty), vec![]),
        );
        if let Some(singleton) = self
            .traits
            .instance_singletons
            .get(&singleton_key)
            .or_else(|| self.traits.instance_singletons.get(&head_key))
        {
            self.builder
                .emit(Instruction::Getstatic(singleton.instance_field_ref));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: pushed_class,
            });
            return Ok(());
        }

        if let Some(instance_info) = self
            .traits
            .parameterized_instances
            .get(trait_name)
            .and_then(|instances| {
                instances.iter().find(|inst| {
                    let mut bindings = HashMap::new();
                    bind_type_vars(&inst.target_type, ty, &mut bindings)
                })
            })
            .cloned()
        {
            let inst_class = self.cp.add_class(&instance_info.class_name)?;
            self.types
                .class_descriptors
                .insert(inst_class, format!("L{};", instance_info.class_name));
            let mut init_desc = String::from("(");
            for _ in &instance_info.requirements {
                init_desc.push_str("Ljava/lang/Object;");
            }
            init_desc.push_str(")V");
            let init_ref = self.cp.add_method_ref(inst_class, "<init>", &init_desc)?;
            self.builder.emit(Instruction::New(inst_class));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: inst_class,
            });
            self.builder.emit(Instruction::Dup);
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: inst_class,
            });
            for requirement in &instance_info.requirements {
                let requirement_ty =
                    Self::resolve_dict_requirement_type(requirement, &instance_info, ty)
                        .ok_or_else(|| {
                            CodegenError::UndefinedVariable(
                                format!(
                                    "could not resolve dictionary requirement {} for {ty}",
                                    requirement.trait_name()
                                ),
                                None,
                            )
                        })?;
                self.emit_dict_argument_for_type(
                    requirement.trait_name(),
                    &requirement_ty,
                    self.builder.refs.object_class,
                )?;
            }
            self.builder.emit(Instruction::Invokespecial(init_ref));
            for _ in &instance_info.requirements {
                self.builder.frame.pop_type();
            }
            self.builder.frame.pop_type();
            return Ok(());
        }

        Err(CodegenError::UndefinedVariable(
            format!("no instance of {trait_name} for {ty}"),
            None,
        ))
    }
}
