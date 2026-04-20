//! Function call resolution, dict/trait dispatch, and call emission.

use rustc_hash::FxHashMap;

use krypton_ir::{bind_instance_targets, TraitName, Type};
use ristretto_classfile::attributes::{Instruction, VerificationType};

use super::compiler::{
    CodegenError, Compiler, DictRequirement, JvmType, ParameterizedInstanceInfo,
};

impl<'link> Compiler<'link> {
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

    pub(super) fn resolve_dict_requirement_types(
        requirement: &DictRequirement,
        instance_info: &ParameterizedInstanceInfo,
        concrete_tys: &[Type],
    ) -> Option<Vec<Type>> {
        let mut bindings = FxHashMap::default();
        if bind_instance_targets(&instance_info.target_types, concrete_tys, &mut bindings) {
            requirement
                .type_vars
                .iter()
                .map(|tv| bindings.get(tv).cloned())
                .collect()
        } else {
            None
        }
    }

    /// Single-parameter convenience wrapper: emit a dict argument for a single
    /// concrete type. Delegates to the multi-parameter form.
    pub(super) fn emit_dict_argument_for_type(
        &mut self,
        trait_name: &TraitName,
        ty: &Type,
        pushed_class: u16,
    ) -> Result<(), CodegenError> {
        self.emit_dict_argument_for_types(trait_name, std::slice::from_ref(ty), pushed_class)
    }

    pub(super) fn emit_dict_argument_for_types(
        &mut self,
        trait_name: &TraitName,
        tys: &[Type],
        pushed_class: u16,
    ) -> Result<(), CodegenError> {
        // Fast path: every position is a type var (or abstract-head App) —
        // dispatch through the enclosing function's dict locals.
        let all_abstract = tys.iter().all(|ty| {
            matches!(ty, Type::Var(_))
                || matches!(ty, Type::App(ctor, _) if Self::is_abstract_type_ctor(ctor))
        });
        if all_abstract && !tys.is_empty() {
            let var_ids: Option<Vec<krypton_ir::TypeVarId>> = tys
                .iter()
                .map(|ty| match ty {
                    Type::Var(id) => Some(*id),
                    Type::App(ctor, _) => match ctor.as_ref() {
                        Type::Var(id) => Some(*id),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();
            let dict_slot = var_ids
                .as_ref()
                .and_then(|ids| self.traits.get_dict_local_many(trait_name, ids))
                .or_else(|| self.traits.get_dict_local_by_trait(trait_name));
            if let Some(dict_slot) = dict_slot {
                self.builder.emit(Instruction::Aload(dict_slot as u8));
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: pushed_class,
                });
                if pushed_class != self.builder.refs.object_class {
                    self.builder.emit(Instruction::Checkcast(pushed_class));
                }
                return Ok(());
            }
        }

        let lookup_types: Vec<Type> = tys.iter().map(|t| t.strip_own()).collect();
        // Try full type first (concrete instances), then head-only (HKT instances like Functor[Box])
        let singleton_key = (trait_name.clone(), lookup_types.clone());
        let head_key = if tys.len() == 1 {
            Some((
                trait_name.clone(),
                vec![Type::Named(krypton_ir::head_type_name(&tys[0]), vec![])],
            ))
        } else {
            None
        };
        if let Some(singleton) = self
            .traits
            .instance_singletons
            .get(&singleton_key)
            .or_else(|| {
                head_key
                    .as_ref()
                    .and_then(|k| self.traits.instance_singletons.get(k))
            })
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
                    let mut bindings = FxHashMap::default();
                    bind_instance_targets(&inst.target_types, tys, &mut bindings)
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
                let requirement_tys =
                    Self::resolve_dict_requirement_types(requirement, &instance_info, tys)
                        .ok_or_else(|| {
                            CodegenError::UndefinedVariable(
                                format!(
                                    "could not resolve dictionary requirement {} for instance",
                                    requirement.trait_name()
                                ),
                                None,
                            )
                        })?;
                self.emit_dict_argument_for_types(
                    requirement.trait_name(),
                    &requirement_tys,
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

        let display = tys
            .iter()
            .map(|t| format!("{t}"))
            .collect::<Vec<_>>()
            .join(", ");
        Err(CodegenError::UndefinedVariable(
            format!("no instance of {trait_name} for {display}"),
            None,
        ))
    }
}
