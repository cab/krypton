//! Lambda/closure compilation and function reference emission.

use std::collections::HashMap;

use ristretto_classfile::attributes::{BootstrapMethod, Instruction, VerificationType};
use ristretto_classfile::{ConstantPool, Method, ReferenceKind};

use super::builder::BytecodeBuilder;
use super::compiler::{CodegenError, Compiler, JvmType};

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

    pub(super) fn ensure_metafactory(
        &mut self,
        cp: &mut ConstantPool,
    ) -> Result<u16, CodegenError> {
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
            JvmType::Long | JvmType::Double | JvmType::Int => {
                self.builder.unbox_if_needed(actual_type)
            }
            JvmType::StructRef(idx) if idx != self.builder.refs.object_class => {
                self.builder.emit(Instruction::Checkcast(idx));
                self.builder.frame.pop_type();
                self.builder
                    .frame
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
}
