//! Lambda/closure compilation and function reference emission.

use std::collections::HashMap;

use krypton_typechecker::types::Type as TcType;
use krypton_ir::Type;
use ristretto_classfile::attributes::{BootstrapMethod, Instruction, VerificationType};
use ristretto_classfile::{ConstantPool, Method, MethodAccessFlags, ReferenceKind};

use super::builder::BytecodeBuilder;
use super::compiler::{Compiler, CodegenError, JvmType};

/// Lambda/closure compilation state.
pub(super) struct LambdaState {
    pub(super) lambda_counter: u16,
    pub(super) lambda_methods: Vec<Method>,
    pub(super) bootstrap_methods: Vec<BootstrapMethod>,
    pub(super) metafactory_handle: Option<u16>,
    pub(super) fun_classes: HashMap<u8, u16>,
    pub(super) fun_apply_refs: HashMap<u8, u16>,
}

impl LambdaState {
    pub(super) fn ensure_fun_interface(
        &mut self,
        arity: u8,
        cp: &mut ConstantPool,
        class_descriptors: &mut HashMap<u16, String>,
    ) -> Result<(), CodegenError> {
        if self.fun_classes.contains_key(&arity) {
            return Ok(());
        }
        let class_name = format!("krypton/runtime/Fun{arity}");
        let class_idx = cp.add_class(&class_name)?;
        let class_desc = format!("L{class_name};");
        class_descriptors.insert(class_idx, class_desc);

        let mut apply_desc = String::from("(");
        for _ in 0..arity {
            apply_desc.push_str("Ljava/lang/Object;");
        }
        apply_desc.push_str(")Ljava/lang/Object;");

        let apply_ref = cp.add_interface_method_ref(class_idx, "apply", &apply_desc)?;
        self.fun_classes.insert(arity, class_idx);
        self.fun_apply_refs.insert(arity, apply_ref);
        Ok(())
    }

    pub(super) fn ensure_metafactory(&mut self, cp: &mut ConstantPool) -> Result<u16, CodegenError> {
        if let Some(handle) = self.metafactory_handle {
            return Ok(handle);
        }
        let lmf_class = cp.add_class("java/lang/invoke/LambdaMetafactory")?;
        let metafactory_ref = cp.add_method_ref(
            lmf_class,
            "metafactory",
            "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;",
        )?;
        let handle = cp.add_method_handle(ReferenceKind::InvokeStatic, metafactory_ref)?;
        self.metafactory_handle = Some(handle);
        Ok(handle)
    }
}

/// Saved outer builder state for nested method compilation.
pub(super) struct MethodScope {
    saved: BytecodeBuilder,
}

impl Compiler {
    /// Stash the current builder and install a fresh one for compiling a nested method.
    pub(super) fn push_method_scope(&mut self) -> MethodScope {
        let refs = self.builder.refs.clone();
        let saved = std::mem::replace(&mut self.builder, BytecodeBuilder::new(refs));
        MethodScope { saved }
    }

    /// Restore the outer builder after nested method compilation.
    pub(super) fn pop_method_scope(&mut self, scope: MethodScope) {
        self.builder = scope.saved;
    }

    pub(super) fn load_bridge_arg(&mut self, slot: u16, actual_type: JvmType) {
        self.builder.emit(Instruction::Aload(slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });
        match actual_type {
            JvmType::Long | JvmType::Double | JvmType::Int => self.builder.unbox_if_needed(actual_type),
            JvmType::StructRef(idx) if idx != self.builder.refs.object_class => {
                self.builder.emit(Instruction::Checkcast(idx));
                self.builder.frame.pop_type();
                self.builder.frame
                    .push_type(VerificationType::Object { cpool_index: idx });
            }
            JvmType::StructRef(_) => {}
        }
    }

    pub(super) fn emit_fun_reference_indy(
        &mut self,
        arity: u8,
        bridge_name: &str,
        bridge_desc: &str,
        fun_class_idx: u16,
        capture_count: usize,
    ) -> Result<JvmType, CodegenError> {
        let bsm_handle = self.lambda.ensure_metafactory(&mut self.cp)?;
        let bridge_ref = self
            .cp
            .add_method_ref(self.this_class, bridge_name, bridge_desc)?;
        let bridge_handle = self
            .cp
            .add_method_handle(ReferenceKind::InvokeStatic, bridge_ref)?;

        let mut sam_desc = String::from("(");
        for _ in 0..arity {
            sam_desc.push_str("Ljava/lang/Object;");
        }
        sam_desc.push_str(")Ljava/lang/Object;");
        let sam_type = self.cp.add_method_type(&sam_desc)?;
        let instantiated_type = self.cp.add_method_type(&sam_desc)?;

        let bsm_index = self.lambda.bootstrap_methods.len() as u16;
        self.lambda.bootstrap_methods.push(BootstrapMethod {
            bootstrap_method_ref: bsm_handle,
            arguments: vec![sam_type, bridge_handle, instantiated_type],
        });

        let fun_class_name = format!("krypton/runtime/Fun{arity}");
        let mut callsite_desc = String::from("(");
        for _ in 0..capture_count {
            callsite_desc.push_str("Ljava/lang/Object;");
        }
        callsite_desc.push_str(&format!(")L{fun_class_name};"));
        let indy_idx = self
            .cp
            .add_invoke_dynamic(bsm_index, "apply", &callsite_desc)?;

        self.builder.emit(Instruction::Invokedynamic(indy_idx));
        for _ in 0..capture_count {
            self.builder.frame.pop_type();
        }
        let result_type = JvmType::StructRef(fun_class_idx);
        self.builder.push_jvm_type(result_type);
        Ok(result_type)
    }

    pub(super) fn compile_fn_ref(&mut self, name: &str, expr_ty: &TcType) -> Result<JvmType, CodegenError> {
        let fn_type = match expr_ty {
            TcType::Own(inner) => inner.as_ref(),
            other => other,
        };
        let (param_types, ret_type) = match fn_type {
            TcType::Fn(param_types, ret_type) => (param_types, ret_type),
            other => {
                return Err(CodegenError::TypeError(format!(
                    "function reference has non-function type: {other}"
                ), None))
            }
        };
        let param_jvm_types = param_types
            .iter()
            .map(|ty| self.tc_type_to_jvm(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let ret_jvm = self.tc_type_to_jvm(ret_type)?;
        let arity = param_jvm_types.len() as u8;

        self.lambda
            .ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
        let fun_class_idx = self.lambda.fun_classes[&arity];

        let dict_requirements = self.traits.impl_dict_requirements
            .get(name)
            .cloned()
            .unwrap_or_default();

        let bridge_name = format!("lambda${}", self.lambda.lambda_counter);
        self.lambda.lambda_counter += 1;
        let mut bridge_desc = String::from("(");
        for _ in &dict_requirements {
            bridge_desc.push_str("Ljava/lang/Object;");
        }
        for _ in &param_jvm_types {
            bridge_desc.push_str("Ljava/lang/Object;");
        }
        bridge_desc.push_str(")Ljava/lang/Object;");

        let scope = self.push_method_scope();
        self.builder.next_local = (dict_requirements.len() + param_jvm_types.len()) as u16;

        for _ in &dict_requirements {
            self.builder.frame.local_types.push(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
        }
        for _ in &param_jvm_types {
            self.builder.frame.local_types.push(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
        }

        if let Some(info) = self.types.get_function(name) {
            let param_types = info.param_types.clone();
            let return_type = info.return_type;
            let is_void = info.is_void;
            let method_ref = info.method_ref;

            if param_types.len() != dict_requirements.len() + param_jvm_types.len() {
                return Err(CodegenError::UnsupportedExpr(format!(
                    "function reference `{name}` has mismatched parameter metadata"
                ), None));
            }

            let mut bridge_slot = 0u16;
            for _ in &dict_requirements {
                self.builder.emit(Instruction::Aload(bridge_slot as u8));
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.object_class,
                });
                bridge_slot += 1;
            }

            for (i, actual_type) in param_jvm_types.iter().copied().enumerate() {
                self.load_bridge_arg(bridge_slot, actual_type);
                let expected_type = param_types[dict_requirements.len() + i];
                if let JvmType::StructRef(idx) = expected_type {
                    if idx == self.builder.refs.object_class
                        && !matches!(actual_type, JvmType::StructRef(_))
                    {
                        self.builder.box_if_needed(actual_type);
                    }
                }
                bridge_slot += 1;
            }

            self.builder.emit(Instruction::Invokestatic(method_ref));
            for actual_type in param_types.iter().rev().copied() {
                self.builder.pop_jvm_type(actual_type);
            }
            if is_void {
                self.builder.emit(Instruction::Iconst_0);
                self.builder.frame.push_type(VerificationType::Integer);
            } else {
                self.builder.push_jvm_type(return_type);
                match ret_jvm {
                    JvmType::Long | JvmType::Double | JvmType::Int
                        if matches!(return_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class) =>
                    {
                        self.builder.unbox_if_needed(ret_jvm);
                    }
                    JvmType::StructRef(idx)
                        if idx != self.builder.refs.object_class
                            && matches!(return_type, JvmType::StructRef(ret_idx) if ret_idx == self.builder.refs.object_class) =>
                    {
                        self.builder.emit(Instruction::Checkcast(idx));
                        self.builder.frame.pop_type();
                        self.builder.frame
                            .push_type(VerificationType::Object { cpool_index: idx });
                    }
                    _ => {}
                }
            }
        } else if let Some(si) = self.types.struct_info.get(name) {
            let class_index = si.class_index;
            let constructor_ref = si.constructor_ref;
            let field_types: Vec<JvmType> = si.fields.iter().map(|(_, ty)| *ty).collect();

            self.builder.emit_new_dup(class_index);

            for (i, actual_type) in field_types.iter().copied().enumerate() {
                self.load_bridge_arg(i as u16, actual_type);
            }

            self.builder.emit(Instruction::Invokespecial(constructor_ref));
            for actual_type in field_types.iter().rev().copied() {
                self.builder.pop_jvm_type(actual_type);
            }
            self.builder.frame.pop_type();
            self.builder.frame.pop_type();
            self.builder.push_jvm_type(JvmType::StructRef(class_index));
        } else if self.types.variant_to_sum.contains_key(name) {
            let (class_idx, ctor_ref, iface_idx, fields) = self.variant_construct_info(name)?;

            self.builder.emit_new_dup(class_idx);

            for (i, (f, actual_type)) in
                fields.iter().zip(param_jvm_types.iter().copied()).enumerate()
            {
                self.load_bridge_arg(i as u16, actual_type);
                if f.is_erased {
                    self.builder.box_if_needed(actual_type);
                } else if matches!(
                    (f.jvm_type, actual_type),
                    (JvmType::StructRef(a), JvmType::StructRef(b))
                    if a == self.builder.refs.object_class || b == self.builder.refs.object_class
                ) {
                    // Erased generic (Object) is compatible with any concrete StructRef
                } else if f.jvm_type != actual_type {
                    return Err(CodegenError::TypeError(format!(
                        "variant reference `{name}` expected bridge arg type {:?}, got {actual_type:?}", f.jvm_type
                    ), None));
                }
            }

            self.emit_variant_invokespecial(ctor_ref, &fields, iface_idx);
        } else {
            return Err(CodegenError::UndefinedVariable(name.to_string(), None));
        }

        let bridge_result = self.builder.box_if_needed(ret_jvm);
        debug_assert!(matches!(bridge_result, JvmType::StructRef(_)));
        self.builder.emit(Instruction::Areturn);

        let bridge_name_idx = self.cp.add_utf8(&bridge_name)?;
        let bridge_desc_idx = self.cp.add_utf8(&bridge_desc)?;
        self.lambda.lambda_methods.push(Method {
            access_flags: MethodAccessFlags::PRIVATE
                | MethodAccessFlags::STATIC
                | MethodAccessFlags::SYNTHETIC,
            name_index: bridge_name_idx,
            descriptor_index: bridge_desc_idx,
            attributes: vec![self.builder.finish_method()],
        });

        self.pop_method_scope(scope);

        if !dict_requirements.is_empty() {
            let ir_param_types: Vec<Type> = param_types.iter().map(|t| t.clone().into()).collect();
            let declared_param_types = self
                .types
                .fn_tc_types
                .get(name)
                .map(|(params, _)| params.clone())
                .unwrap_or_else(|| ir_param_types.clone());
            for requirement in &dict_requirements {
                let requirement_ty = Self::resolve_function_ref_requirement_type(
                    requirement,
                    &declared_param_types,
                    &ir_param_types,
                )
                .ok_or_else(|| {
                    CodegenError::UndefinedVariable(format!(
                        "could not resolve function reference dictionary requirement {} for {name}",
                        requirement.trait_name()
                    ), None)
                })?;
                self.emit_dict_argument_for_type(
                    requirement.trait_name(),
                    &requirement_ty,
                    self.builder.refs.object_class,
                )?;
            }
        }

        self.emit_fun_reference_indy(
            arity,
            &bridge_name,
            &bridge_desc,
            fun_class_idx,
            dict_requirements.len(),
        )
    }

}
