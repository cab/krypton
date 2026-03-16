use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind};
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{Instruction, VerificationType};

use super::compiler::{Compiler, CodegenError, DictRequirement, JvmType};

/// Resolved calling convention for a function application.
pub(super) enum CallTarget {
    Intrinsic,
    Constructor {
        class_index: u16,
        constructor_ref: u16,
        fields: Vec<(String, JvmType)>,
    },
    VariantConstructor {
        class_index: u16,
        constructor_ref: u16,
        interface_class_index: u16,
        fields: Vec<(String, JvmType, bool)>, // (name, type, is_erased)
    },
    HigherOrder {
        slot: u16,
        jvm_ty: JvmType,
        param_types: Vec<JvmType>,
        ret_type: JvmType,
    },
    TraitMethod {
        trait_name: String,
        iface_method_ref: u16,
        iface_class: u16,
        dict_ty: Type,
    },
    StaticCall {
        method_ref: u16,
        param_types: Vec<JvmType>,
        return_type: JvmType,
        is_void: bool,
        explicit_requirements: Vec<DictRequirement>,
        constraint_traits: Vec<(String, usize)>,
    },
}

impl Compiler {
    pub(super) fn compile_var(&mut self, name: &str) -> Result<JvmType, CodegenError> {
        // Check if this is a nullary variant constructor
        if let Some(sum_name) = self.types.variant_to_sum.get(name).cloned() {
            let sum_info = &self.types.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            if vi.fields.is_empty() {
                let singleton_field_ref = vi.singleton_field_ref.unwrap();
                let interface_class_index = sum_info.interface_class_index;
                self.builder.emit(Instruction::Getstatic(singleton_field_ref));
                let result_type = JvmType::StructRef(interface_class_index);
                self.builder.push_jvm_type(result_type);
                return Ok(result_type);
            }
        }

        let (slot, ty) = self
            .builder.locals
            .get(name)
            .copied()
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;

        self.builder.emit_load(slot, ty);

        Ok(ty)
    }

    pub(super) fn compile_intrinsic(
        &mut self,
        name: &str,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        match name {
            "panic" => {
                let re_class = self.builder.refs.runtime_exception_class;
                let re_init = self.builder.refs.runtime_exception_init;
                self.builder.emit_new_dup(re_class);
                // Compile the String argument
                self.compile_expr(&args[0], false)?;
                // invokespecial RuntimeException.<init>(String)V
                self.builder.emit(Instruction::Invokespecial(re_init));
                self.builder.frame.pop_type(); // string arg
                self.builder.frame.pop_type(); // dup'd uninit
                self.builder.frame.pop_type(); // original uninit
                self.builder.emit(Instruction::Athrow);
                // Push the expected return type onto the frame for verification
                let jvm_ret = self.type_to_jvm(result_ty)?;
                self.builder.push_jvm_type(jvm_ret);
                Ok(jvm_ret)
            }
            _ => Err(CodegenError::UnsupportedExpr(format!(
                "unknown intrinsic: {name}"
            ))),
        }
    }

    pub(super) fn compile_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        let (name, target) = self.resolve_call(func, args, result_ty)?;
        self.emit_call(target, &name, func, args, result_ty)
    }

    /// Extract the function name from a call expression.
    pub(super) fn extract_call_name<'a>(func: &'a TypedExpr) -> Result<&'a str, CodegenError> {
        match &func.kind {
            TypedExprKind::Var(name) => Ok(name.as_str()),
            TypedExprKind::TypeApp { expr } => match &expr.kind {
                TypedExprKind::Var(name) => Ok(name.as_str()),
                other => Err(CodegenError::UnsupportedExpr(format!(
                    "non-variable function call: {other:?}"
                ))),
            },
            other => Err(CodegenError::UnsupportedExpr(format!(
                "non-variable function call: {other:?}"
            ))),
        }
    }

    /// Pure lookup: determine the calling convention without emitting bytecode.
    pub(super) fn resolve_call(
        &self,
        func: &TypedExpr,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<(String, CallTarget), CodegenError> {
        let name = Self::extract_call_name(func)?;

        // Intrinsic
        if name == "panic" {
            return Ok((name.to_string(), CallTarget::Intrinsic));
        }

        // Struct constructor
        if let Some(si) = self.types.struct_info.get(name) {
            let fields = si.fields.clone();
            return Ok((name.to_string(), CallTarget::Constructor {
                class_index: si.class_index,
                constructor_ref: si.constructor_ref,
                fields,
            }));
        }

        // Variant constructor
        if let Some(sum_name) = self.types.variant_to_sum.get(name) {
            let sum_info = &self.types.sum_type_info[sum_name];
            let vi = &sum_info.variants[name];
            return Ok((name.to_string(), CallTarget::VariantConstructor {
                class_index: vi.class_index,
                constructor_ref: vi.constructor_ref,
                interface_class_index: sum_info.interface_class_index,
                fields: vi.fields.clone(),
            }));
        }

        // Higher-order call (local variable holding a lambda)
        if let Some(&(slot, jvm_ty)) = self.builder.locals.get(name) {
            if let Some((_ho_param_types, ho_ret_type)) = self.builder.local_fn_info.get(name) {
                return Ok((name.to_string(), CallTarget::HigherOrder {
                    slot,
                    jvm_ty,
                    param_types: _ho_param_types.clone(),
                    ret_type: *ho_ret_type,
                }));
            }
        }

        // Trait method dispatch
        if let Some(trait_name) = self.traits.trait_method_map.get(name) {
            if let Some(dispatch) = self.traits.trait_dispatch.get(trait_name) {
                let dict_ty = if args.is_empty() {
                    match &func.ty {
                        Type::Fn(_, ret) => ret.as_ref().clone(),
                        _ => result_ty.clone(),
                    }
                } else {
                    args[0].ty.clone()
                };
                let is_type_var = matches!(&dict_ty, Type::Var(_));
                if is_type_var && !self.traits.dict_locals.contains_key(trait_name) {
                    return Err(CodegenError::UndefinedVariable(format!(
                        "no dict local for trait {trait_name}"
                    )));
                }
                return Ok((name.to_string(), CallTarget::TraitMethod {
                    trait_name: trait_name.clone(),
                    iface_method_ref: dispatch.method_refs[name],
                    iface_class: dispatch.interface_class,
                    dict_ty,
                }));
            }
        }

        // Static call (user-defined function)
        let explicit_requirements = self
            .traits
            .impl_dict_requirements
            .get(name)
            .cloned()
            .unwrap_or_default();
        let constraint_traits = self
            .traits
            .fn_constraints
            .get(name)
            .cloned()
            .unwrap_or_default();

        let func_params: Vec<Type> = match &func.ty {
            Type::Fn(params, _) => params.clone(),
            Type::Own(inner) => match inner.as_ref() {
                Type::Fn(params, _) => params.clone(),
                _ => vec![],
            },
            _ => vec![],
        };
        let info = self
            .types
            .get_function_by_params(name, &func_params)
            .or_else(|| self.types.get_function(name))
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;

        Ok((name.to_string(), CallTarget::StaticCall {
            method_ref: info.method_ref,
            param_types: info.param_types.clone(),
            return_type: info.return_type,
            is_void: info.is_void,
            explicit_requirements,
            constraint_traits,
        }))
    }

    /// Coerce an Object result from invokeinterface to the expected JVM type.
    /// Used by both higher-order calls and trait method dispatch.
    pub(super) fn coerce_interface_return(&mut self, expected_ret: JvmType) {
        // Push Object result onto frame
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });
        // Unbox primitives
        self.builder.unbox_if_needed(expected_ret);
        // Checkcast for Ref/StructRef
        match expected_ret {
            JvmType::Ref => {
                self.builder
                    .emit(Instruction::Checkcast(self.builder.refs.string_class));
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.string_class,
                });
            }
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

    /// Emit bytecode for a resolved call target.
    pub(super) fn emit_call(
        &mut self,
        target: CallTarget,
        name: &str,
        func: &TypedExpr,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        match target {
            CallTarget::Intrinsic => self.compile_intrinsic(name, args, result_ty),

            CallTarget::Constructor {
                class_index,
                constructor_ref,
                fields,
            } => {
                let result_type = JvmType::StructRef(class_index);
                self.builder.emit_new_dup(class_index);
                for arg in args {
                    self.compile_expr(arg, false)?;
                }
                for (_, ft) in &fields {
                    self.builder.pop_jvm_type(*ft);
                }
                self.builder.frame.pop_type(); // dup'd uninit
                self.builder.frame.pop_type(); // original uninit
                self.builder
                    .emit(Instruction::Invokespecial(constructor_ref));
                self.builder.push_jvm_type(result_type);
                Ok(result_type)
            }

            CallTarget::VariantConstructor {
                class_index,
                constructor_ref,
                interface_class_index,
                fields,
            } => {
                let result_type = JvmType::StructRef(interface_class_index);
                self.builder.emit_new_dup(class_index);
                for (i, arg) in args.iter().enumerate() {
                    let arg_type = self.compile_expr(arg, false)?;
                    let (_fname, _field_jvm_type, is_erased) = &fields[i];
                    if *is_erased {
                        self.builder.box_if_needed(arg_type);
                    }
                }
                for (_, ft, is_erased) in &fields {
                    if *is_erased {
                        self.builder.frame.pop_type(); // Object ref
                    } else {
                        self.builder.pop_jvm_type(*ft);
                    }
                }
                self.builder.frame.pop_type(); // dup'd uninit
                self.builder.frame.pop_type(); // original uninit
                self.builder
                    .emit(Instruction::Invokespecial(constructor_ref));
                self.builder.push_jvm_type(result_type);
                Ok(result_type)
            }

            CallTarget::HigherOrder {
                slot,
                jvm_ty,
                ret_type,
                ..
            } => {
                let arity = args.len() as u8;
                self.builder.emit(Instruction::Aload(slot as u8));
                self.builder.push_jvm_type(jvm_ty);
                for arg in args {
                    let arg_type = self.compile_expr(arg, false)?;
                    self.builder.box_if_needed(arg_type);
                }
                let apply_ref = self.lambda.fun_apply_refs[&arity];
                self.builder
                    .emit(Instruction::Invokeinterface(apply_ref, arity + 1));
                for _ in 0..arity {
                    self.builder.frame.pop_type();
                }
                self.builder.pop_jvm_type(jvm_ty);
                self.coerce_interface_return(ret_type);
                Ok(ret_type)
            }

            CallTarget::TraitMethod {
                trait_name,
                iface_method_ref,
                iface_class,
                dict_ty,
            } => {
                self.emit_dict_argument_for_type(&trait_name, &dict_ty, iface_class)?;
                let arity = args.len();
                for arg in args {
                    let arg_type = self.compile_expr(arg, false)?;
                    self.builder.box_if_needed(arg_type);
                }
                self.builder.emit(Instruction::Invokeinterface(
                    iface_method_ref,
                    (arity + 1) as u8,
                ));
                for _ in 0..arity {
                    self.builder.frame.pop_type();
                }
                self.builder.frame.pop_type(); // receiver (dict)

                // Determine expected return type from the interface method
                let result_jvm = self
                    .type_to_jvm(&func.ty)
                    .unwrap_or(JvmType::StructRef(self.builder.refs.object_class));
                let expected_ret = if let Type::Fn(_, ret) = &func.ty {
                    self.type_to_jvm(ret)
                        .unwrap_or(JvmType::StructRef(self.builder.refs.object_class))
                } else {
                    result_jvm
                };

                self.coerce_interface_return(expected_ret);
                Ok(expected_ret)
            }

            CallTarget::StaticCall {
                method_ref,
                param_types,
                return_type,
                is_void,
                explicit_requirements,
                constraint_traits,
            } => {
                // Push dict args first for constrained functions
                if !explicit_requirements.is_empty() {
                    if let Some((param_patterns, ret_pattern)) =
                        self.types.fn_tc_types.get(name).cloned()
                    {
                        for requirement in &explicit_requirements {
                            let requirement_ty = Self::resolve_function_requirement_type(
                                requirement,
                                &param_patterns,
                                args,
                                Some((&ret_pattern, result_ty)),
                            )
                            .ok_or_else(|| {
                                CodegenError::UndefinedVariable(format!(
                                    "could not resolve function dictionary requirement {} for {name}",
                                    requirement.trait_name()
                                ))
                            })?;
                            self.emit_dict_argument_for_type(
                                requirement.trait_name(),
                                &requirement_ty,
                                self.builder.refs.object_class,
                            )?;
                        }
                    }
                } else if !constraint_traits.is_empty() {
                    for (trait_name, param_idx) in &constraint_traits {
                        if let Some(target_arg) = args.get(*param_idx) {
                            self.emit_dict_argument_for_type(
                                trait_name,
                                &target_arg.ty,
                                self.builder.refs.object_class,
                            )?;
                        }
                    }
                }

                // Compile each argument, boxing/casting if needed for erased type params
                let dict_offset = if !explicit_requirements.is_empty() {
                    explicit_requirements.len()
                } else {
                    constraint_traits.len()
                };
                for (i, arg) in args.iter().enumerate() {
                    let arg_type = self.compile_expr(arg, false)?;
                    let expected = param_types[i + dict_offset];
                    if let JvmType::StructRef(idx) = expected {
                        if idx == self.builder.refs.object_class
                            && !matches!(arg_type, JvmType::StructRef(_) | JvmType::Ref)
                        {
                            self.builder.box_if_needed(arg_type);
                        } else if idx != self.builder.refs.object_class {
                            if let JvmType::StructRef(arg_idx) = arg_type {
                                if arg_idx == self.builder.refs.object_class && arg_idx != idx {
                                    self.builder.emit(Instruction::Checkcast(idx));
                                    self.builder.frame.pop_type();
                                    self.builder.frame.push_type(VerificationType::Object {
                                        cpool_index: idx,
                                    });
                                }
                            }
                        }
                    }
                }

                // Pop argument types from stack
                for pt in param_types.iter().rev() {
                    self.builder.pop_jvm_type(*pt);
                }

                self.builder.emit(Instruction::Invokestatic(method_ref));

                if is_void {
                    self.builder.emit(Instruction::Iconst_0);
                    self.builder.frame.push_type(VerificationType::Integer);
                    Ok(JvmType::Int)
                } else {
                    self.builder.push_jvm_type(return_type);
                    Ok(return_type)
                }
            }
        }
    }
}
