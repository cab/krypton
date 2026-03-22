//! Lambda/closure compilation and function reference emission.

use std::collections::HashMap;

use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind};
use krypton_typechecker::types::{Type, TypeVarId};
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

    pub(super) fn compile_fn_ref(&mut self, name: &str, expr_ty: &Type) -> Result<JvmType, CodegenError> {
        let fn_type = match expr_ty {
            Type::Own(inner) => inner.as_ref(),
            other => other,
        };
        let (param_types, ret_type) = match fn_type {
            Type::Fn(param_types, ret_type) => (param_types, ret_type),
            other => {
                return Err(CodegenError::TypeError(format!(
                    "function reference has non-function type: {other}"
                ), None))
            }
        };
        let param_jvm_types = param_types
            .iter()
            .map(|ty| self.type_to_jvm(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let ret_jvm = self.type_to_jvm(ret_type)?;
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
        } else if let Some(sum_name) = self.types.variant_to_sum.get(name).cloned() {
            let sum_info = &self.types.sum_type_info[&sum_name];
            let variant = &sum_info.variants[name];
            let class_index = variant.class_index;
            let constructor_ref = variant.constructor_ref;
            let interface_class_index = sum_info.interface_class_index;
            let fields = variant.fields.clone();

            self.builder.emit_new_dup(class_index);

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

            self.builder.emit(Instruction::Invokespecial(constructor_ref));
            for f in fields.iter().rev() {
                if f.is_erased {
                    self.builder.frame.pop_type();
                } else {
                    self.builder.pop_jvm_type(f.jvm_type);
                }
            }
            self.builder.frame.pop_type();
            self.builder.frame.pop_type();
            self.builder.push_jvm_type(JvmType::StructRef(interface_class_index));
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
            let declared_param_types = self
                .types
                .fn_tc_types
                .get(name)
                .map(|(params, _)| params.clone())
                .unwrap_or_else(|| param_types.clone());
            for requirement in &dict_requirements {
                let requirement_ty = Self::resolve_function_ref_requirement_type(
                    requirement,
                    &declared_param_types,
                    param_types,
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

    /// Compile a lambda expression.
    pub(super) fn compile_lambda(
        &mut self,
        params: &[String],
        body: &TypedExpr,
        lambda_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        let arity = params.len() as u8;

        // Extract param types from the TypedExpr's type
        let fn_type = match lambda_ty {
            Type::Own(inner) => inner.as_ref(),
            other => other,
        };
        let param_jvm_types = match fn_type {
            Type::Fn(param_types, _) => param_types
                .iter()
                .map(|t| self.type_to_jvm(t))
                .collect::<Result<Vec<_>, _>>()?,
            _ => {
                return Err(CodegenError::TypeError(
                    "lambda has non-function type".to_string(), None))
            }
        };

        // Ensure FunN interface exists
        self.lambda
            .ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
        let fun_class_idx = self.lambda.fun_classes[&arity];

        // Find captured variables: scan body for Var names that are in self.builder.locals but not lambda params
        let param_names: std::collections::HashSet<&str> =
            params.iter().map(|s| s.as_str()).collect();
        let mut captures: Vec<(String, u16, JvmType)> = Vec::new();
        self.collect_captures(body, &param_names, &mut captures);
        // Deduplicate
        let mut seen = std::collections::HashSet::new();
        captures.retain(|(name, _, _)| seen.insert(name.clone()));

        // Capture dict locals (trait dicts from `where` clauses) that the lambda body needs.
        // These are stored in traits.dict_locals, not builder.locals, so collect_captures misses them.
        let dict_captures: Vec<((String, TypeVarId), u16)> = self
            .traits
            .dict_locals
            .iter()
            .map(|(key, &slot)| (key.clone(), slot))
            .collect();

        // Save compiler state for the outer method
        let saved_dict_locals = self.traits.dict_locals.clone();
        // Save local_fn_info for captured function-typed variables before scope swap
        let saved_local_fn_info = self.builder.local_fn_info.clone();
        let scope = self.push_method_scope();

        // Register captured vars as first params (all boxed to Object)
        for (cap_name, _, cap_type) in &captures {
            let slot = self.builder.next_local;
            self.builder.locals.insert(cap_name.clone(), (slot, *cap_type));
            self.builder.frame.local_types.push(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
            self.builder.next_local += 1;
            // Propagate local_fn_info for function-typed captures so higher-order calls work
            if let Some(fn_info) = saved_local_fn_info.get(cap_name) {
                self.builder.local_fn_info.insert(cap_name.clone(), fn_info.clone());
            }
        }

        // Register captured dict locals and remap dict_locals to new slots in the lambda method
        for (dict_key, _) in &dict_captures {
            let slot = self.builder.next_local;
            self.traits.dict_locals.insert(dict_key.clone(), slot);
            self.builder.frame.local_types.push(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
            self.builder.next_local += 1;
        }

        // Register lambda params (all as Object, will unbox)
        let mut lambda_param_slots = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let slot = self.builder.next_local;
            // Store as Object initially
            self.builder.locals.insert(
                p.clone(),
                (slot, JvmType::StructRef(self.builder.refs.object_class)),
            );
            self.builder.frame.local_types.push(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
            lambda_param_slots.push((slot, param_jvm_types[i]));
            self.builder.next_local += 1;
        }

        // Unbox primitive params from Object to actual types
        for (i, p) in params.iter().enumerate() {
            let actual_type = param_jvm_types[i];
            if matches!(actual_type, JvmType::Long | JvmType::Double | JvmType::Int) {
                let slot = lambda_param_slots[i].0;
                self.builder.emit(Instruction::Aload(slot as u8));
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.object_class,
                });
                self.builder.unbox_if_needed(actual_type);
                let new_slot = self.builder.alloc_local(p.clone(), actual_type);
                self.builder.emit_store(new_slot, actual_type);
            }
        }

        // Cast struct-typed params from Object to their actual struct type
        for (i, p) in params.iter().enumerate() {
            let actual_type = param_jvm_types[i];
            if let JvmType::StructRef(class_idx) = actual_type {
                if class_idx != self.builder.refs.object_class {
                    let slot = lambda_param_slots[i].0;
                    self.builder.emit(Instruction::Aload(slot as u8));
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: self.builder.refs.object_class,
                    });
                    self.builder.emit(Instruction::Checkcast(class_idx));
                    self.builder.frame.pop_type();
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    let new_slot = self.builder.next_local;
                    self.builder.next_local += 1;
                    self.builder.emit(Instruction::Astore(new_slot as u8));
                    self.builder.frame.pop_type();
                    self.builder.frame.local_types.push(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    self.builder.locals.insert(p.clone(), (new_slot, actual_type));
                }
            }
        }

        // Also unbox captured vars if they are primitive types
        for (cap_name, _, cap_type) in &captures {
            let actual_type = *cap_type;
            if matches!(actual_type, JvmType::Long | JvmType::Double | JvmType::Int) {
                let (slot, _) = self.builder.locals[cap_name];
                self.builder.emit(Instruction::Aload(slot as u8));
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.object_class,
                });
                self.builder.unbox_if_needed(actual_type);
                let new_slot = self.builder.alloc_local(cap_name.clone(), actual_type);
                self.builder.emit_store(new_slot, actual_type);
            }
        }

        // Cast struct-typed captured vars from Object to their actual struct type
        for (cap_name, _, cap_type) in &captures {
            let actual_type = *cap_type;
            if let JvmType::StructRef(class_idx) = actual_type {
                if class_idx != self.builder.refs.object_class {
                    let (slot, _) = self.builder.locals[cap_name];
                    self.builder.emit(Instruction::Aload(slot as u8));
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: self.builder.refs.object_class,
                    });
                    self.builder.emit(Instruction::Checkcast(class_idx));
                    self.builder.frame.pop_type();
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    let new_slot = self.builder.next_local;
                    self.builder.next_local += 1;
                    self.builder.emit(Instruction::Astore(new_slot as u8));
                    self.builder.frame.pop_type();
                    self.builder.frame.local_types.push(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    self.builder.locals
                        .insert(cap_name.clone(), (new_slot, actual_type));
                }
            }
        }

        // Set up recur support for lambda
        let lambda_fn_params: Vec<(u16, JvmType)> = params.iter()
            .map(|p| self.builder.locals[p])
            .collect();
        self.builder.fn_params = lambda_fn_params;
        let lambda_return_type = match fn_type {
            Type::Fn(_, ret) => self.type_to_jvm(ret)?,
            _ => JvmType::StructRef(self.builder.refs.object_class),
        };
        self.builder.fn_return_type = Some(lambda_return_type);
        self.builder.emit(Instruction::Nop);
        self.builder.recur_target = self.builder.code.len() as u16;
        self.builder.recur_frame_locals = self.builder.frame.local_types.clone();

        // Compile the body
        let body_type = self.compile_expr(body, true)?;

        // Box the result if needed
        self.builder.box_if_needed(body_type);

        // Return
        self.builder.emit(Instruction::Areturn);

        // Build the lambda method
        let lambda_name = format!("lambda${}", self.lambda.lambda_counter);
        self.lambda.lambda_counter += 1;

        // Descriptor: all Object params (captures + dict_captures + lambda params) -> Object
        let total_params = captures.len() + dict_captures.len() + params.len();
        let mut lambda_desc = String::from("(");
        for _ in 0..total_params {
            lambda_desc.push_str("Ljava/lang/Object;");
        }
        lambda_desc.push_str(")Ljava/lang/Object;");

        let lambda_name_idx = self.cp.add_utf8(&lambda_name)?;
        let lambda_desc_idx = self.cp.add_utf8(&lambda_desc)?;

        let lambda_method = Method {
            access_flags: MethodAccessFlags::PRIVATE
                | MethodAccessFlags::STATIC
                | MethodAccessFlags::SYNTHETIC,
            name_index: lambda_name_idx,
            descriptor_index: lambda_desc_idx,
            attributes: vec![self.builder.finish_method()],
        };

        self.lambda.lambda_methods.push(lambda_method);

        // Restore compiler state
        self.pop_method_scope(scope);
        self.traits.dict_locals = saved_dict_locals;

        // Now set up invokedynamic in the outer method

        // 1. Ensure metafactory bootstrap handle
        let bsm_handle = self.lambda.ensure_metafactory(&mut self.cp)?;

        // 2. Create method ref for the lambda impl
        let this_class = self.this_class;
        let lambda_impl_ref = self
            .cp
            .add_method_ref(this_class, &lambda_name, &lambda_desc)?;
        let lambda_impl_handle = self
            .cp
            .add_method_handle(ReferenceKind::InvokeStatic, lambda_impl_ref)?;

        // 3. SAM method type: (Object, ...)Object for the apply method
        let mut sam_desc = String::from("(");
        for _ in 0..arity {
            sam_desc.push_str("Ljava/lang/Object;");
        }
        sam_desc.push_str(")Ljava/lang/Object;");
        let sam_type = self.cp.add_method_type(&sam_desc)?;
        let instantiated_type = self.cp.add_method_type(&sam_desc)?;

        // 4. Create bootstrap method entry
        let bsm_index = self.lambda.bootstrap_methods.len() as u16;
        self.lambda.bootstrap_methods.push(BootstrapMethod {
            bootstrap_method_ref: bsm_handle,
            arguments: vec![sam_type, lambda_impl_handle, instantiated_type],
        });

        // 5. Build the call site descriptor
        let total_captures = captures.len() + dict_captures.len();
        let fun_class_name = format!("krypton/runtime/Fun{arity}");
        let mut callsite_desc = String::from("(");
        for _ in 0..total_captures {
            callsite_desc.push_str("Ljava/lang/Object;");
        }
        callsite_desc.push_str(&format!(")L{fun_class_name};"));

        let indy_idx = self
            .cp
            .add_invoke_dynamic(bsm_index, "apply", &callsite_desc)?;

        // 6. Push captured variables onto stack (boxed)
        for (_cap_name, cap_slot, cap_type) in &captures {
            self.builder.emit_load(*cap_slot, *cap_type);
            self.builder.box_if_needed(*cap_type);
        }
        // Push captured dict locals onto stack
        for (_dict_key, dict_slot) in &dict_captures {
            self.builder.emit(Instruction::Aload(*dict_slot as u8));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
        }

        // 7. Emit invokedynamic
        self.builder.emit(Instruction::Invokedynamic(indy_idx));

        // Pop capture args from stack
        for _ in 0..total_captures {
            self.builder.frame.pop_type(); // each boxed capture is a single Object ref
        }

        // Push result type
        let result_type = JvmType::StructRef(fun_class_idx);
        self.builder.push_jvm_type(result_type);

        Ok(result_type)
    }

    /// Collect captured variables from an expression.
    pub(super) fn collect_captures(
        &self,
        expr: &TypedExpr,
        param_names: &std::collections::HashSet<&str>,
        captures: &mut Vec<(String, u16, JvmType)>,
    ) {
        use std::rc::Rc;
        let initial: Rc<std::collections::HashSet<&str>> = Rc::new(param_names.clone());
        let mut work: Vec<(&TypedExpr, Rc<std::collections::HashSet<&str>>)> =
            Vec::with_capacity(16);
        work.push((expr, initial));
        while let Some((expr, param_names)) = work.pop() {
            match &expr.kind {
                TypedExprKind::Var(name) => {
                    if !param_names.contains(name.as_str()) {
                        if let Some(&(slot, ty)) = self.builder.locals.get(name) {
                            captures.push((name.clone(), slot, ty));
                        }
                    }
                }
                TypedExprKind::Lambda { body, params } => {
                    let mut inner_params = (*param_names).clone();
                    for p in params {
                        inner_params.insert(p.as_str());
                    }
                    work.push((body, Rc::new(inner_params)));
                }
                TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                    work.push((lhs, Rc::clone(&param_names)));
                    work.push((rhs, param_names));
                }
                TypedExprKind::UnaryOp { operand, .. } => {
                    work.push((operand, param_names));
                }
                TypedExprKind::If { cond, then_, else_ } => {
                    work.push((cond, Rc::clone(&param_names)));
                    work.push((then_, Rc::clone(&param_names)));
                    work.push((else_, param_names));
                }
                TypedExprKind::Let { value, body, .. }
                | TypedExprKind::LetPattern { value, body, .. } => {
                    if let Some(body) = body {
                        work.push((body, Rc::clone(&param_names)));
                    }
                    work.push((value, param_names));
                }
                TypedExprKind::Do(exprs) => {
                    for e in exprs {
                        work.push((e, Rc::clone(&param_names)));
                    }
                }
                TypedExprKind::App { func, args } => {
                    work.push((func, Rc::clone(&param_names)));
                    for a in args {
                        work.push((a, Rc::clone(&param_names)));
                    }
                }
                TypedExprKind::TypeApp { expr, .. } => {
                    work.push((expr, param_names));
                }
                TypedExprKind::Match { scrutinee, arms } => {
                    work.push((scrutinee, Rc::clone(&param_names)));
                    for arm in arms {
                        work.push((&arm.body, Rc::clone(&param_names)));
                    }
                }
                TypedExprKind::FieldAccess { expr, .. }
                | TypedExprKind::QuestionMark { expr, .. } => {
                    work.push((expr, param_names));
                }
                TypedExprKind::StructLit { fields, .. } => {
                    for (_, e) in fields {
                        work.push((e, Rc::clone(&param_names)));
                    }
                }
                TypedExprKind::StructUpdate { base, fields } => {
                    work.push((base, Rc::clone(&param_names)));
                    for (_, e) in fields {
                        work.push((e, Rc::clone(&param_names)));
                    }
                }
                TypedExprKind::Tuple(elems)
                | TypedExprKind::Recur(elems)
                | TypedExprKind::VecLit(elems) => {
                    for e in elems {
                        work.push((e, Rc::clone(&param_names)));
                    }
                }
                TypedExprKind::Lit(_) => {}
            }
        }
    }
}
