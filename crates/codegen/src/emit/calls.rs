//! Function call resolution, dict/trait dispatch, and call emission.

use std::collections::HashMap;

use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind};
use krypton_typechecker::types::{Type, TypeVarId};
use ristretto_classfile::attributes::{Instruction, VerificationType};

use super::compiler::{Compiler, CodegenError, DictRequirement, JvmType, ParameterizedInstanceInfo};

/// Extract head type constructor name for parameterized instance lookup.
fn head_type_name(ty: &Type) -> Result<String, CodegenError> {
    match ty {
        Type::Own(inner) => head_type_name(inner),
        Type::Named(name, _) => Ok(name.clone()),
        Type::Int => Ok("Int".to_string()),
        Type::Float => Ok("Float".to_string()),
        Type::Bool => Ok("Bool".to_string()),
        Type::String => Ok("String".to_string()),
        other => Err(CodegenError::TypeError(format!(
            "cannot extract head type name from {other:?}"
        ))),
    }
}

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
            "trait_dict" => {
                // trait_dict(TraitName) — load the dict for the named trait from locals
                let trait_name = match &args[0].kind {
                    TypedExprKind::Var(name) => name.clone(),
                    _ => {
                        return Err(CodegenError::UnsupportedExpr(
                            "trait_dict argument must be a trait name".to_string(),
                        ));
                    }
                };
                let object_class = self.builder.refs.object_class;
                if let Some(&dict_slot) = self.traits.dict_locals.get(&trait_name) {
                    self.builder.emit(Instruction::Aload(dict_slot as u8));
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: object_class,
                    });
                    Ok(JvmType::StructRef(object_class))
                } else {
                    Err(CodegenError::UndefinedVariable(format!(
                        "no dict local for trait_dict({trait_name})"
                    )))
                }
            }
            "is_null" => {
                // Compile arg — should be Object reference from extern Java call
                self.compile_expr(&args[0], false)?;
                // Ifnonnull: if NOT null, jump to false branch
                let false_label = self.builder.emit_placeholder(Instruction::Ifnonnull(0));
                self.builder.frame.pop_type();
                // null case: push true
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                let end_label = self.builder.emit_placeholder(Instruction::Goto(0));
                self.builder.frame.pop_type();
                // not-null case
                let false_pos = self.builder.code.len();
                self.builder.frame.record_frame(false_pos as u16);
                self.builder.emit(Instruction::Iconst_0);
                self.builder.frame.push_type(VerificationType::Integer);
                let end_pos = self.builder.code.len();
                self.builder.frame.record_frame(end_pos as u16);
                // Patch jumps
                self.builder.patch(false_label, Instruction::Ifnonnull(false_pos as u16));
                self.builder.patch(end_label, Instruction::Goto(end_pos as u16));
                Ok(JvmType::Int) // Bool = Int on JVM
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
        if Self::extract_call_name(func).is_ok() {
            let (name, target) = self.resolve_call(func, args, result_ty)?;
            self.emit_call(target, &name, func, args, result_ty)
        } else {
            self.compile_expr_call(func, args)
        }
    }

    /// Compile a call where the callee is an arbitrary expression (not a named function).
    /// Evaluates the callee onto the stack, then uses invokeinterface FunN.apply.
    fn compile_expr_call(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
    ) -> Result<JvmType, CodegenError> {
        // Determine arity and return type from the callee's type
        let (arity, ret_ty) = match &func.ty {
            Type::Fn(params, ret) => (params.len() as u8, ret.as_ref().clone()),
            Type::Own(inner) => match inner.as_ref() {
                Type::Fn(params, ret) => (params.len() as u8, ret.as_ref().clone()),
                other => return Err(CodegenError::TypeError(format!(
                    "expression call on non-function type: {other:?}"
                ))),
            },
            other => return Err(CodegenError::TypeError(format!(
                "expression call on non-function type: {other:?}"
            ))),
        };
        let ret_jvm = self.type_to_jvm(&ret_ty)?;

        // Ensure the FunN interface exists for this arity
        self.lambda.ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
        let fun_class = self.lambda.fun_classes[&arity];
        let apply_ref = self.lambda.fun_apply_refs[&arity];

        // Compile the callee expression — puts function object on stack
        let callee_jvm = self.compile_expr(func, false)?;

        // If the callee came back as Object (erased), checkcast to FunN
        if let JvmType::StructRef(idx) = callee_jvm {
            if idx != fun_class {
                self.builder.emit(Instruction::Checkcast(fun_class));
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: fun_class,
                });
            }
        }

        // Compile and box each argument
        for arg in args {
            let arg_type = self.compile_expr(arg, false)?;
            self.builder.box_if_needed(arg_type);
        }

        // invokeinterface FunN.apply(args)
        self.builder.emit(Instruction::Invokeinterface(apply_ref, arity + 1));
        for _ in 0..arity {
            self.builder.frame.pop_type();
        }
        self.builder.pop_jvm_type(JvmType::StructRef(fun_class));

        // Coerce the Object return to the expected type
        self.coerce_interface_return(ret_jvm);
        Ok(ret_jvm)
    }

    /// Extract the function name from a call expression.
    pub(super) fn extract_call_name<'a>(func: &'a TypedExpr) -> Result<&'a str, CodegenError> {
        match &func.kind {
            TypedExprKind::Var(name) => Ok(name.as_str()),
            TypedExprKind::TypeApp { expr, .. } => match &expr.kind {
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
        if name == "panic" || name == "trait_dict" || name == "is_null" {
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
                    if let TypedExprKind::TypeApp { type_args, .. } = &func.kind {
                        if !type_args.is_empty() {
                            type_args[0].clone()
                        } else {
                            match &func.ty {
                                Type::Fn(_, ret) => ret.as_ref().clone(),
                                _ => result_ty.clone(),
                            }
                        }
                    } else {
                        match &func.ty {
                            Type::Fn(_, ret) => ret.as_ref().clone(),
                            _ => result_ty.clone(),
                        }
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
                            && !matches!(arg_type, JvmType::StructRef(_))
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

    // --- Dict / trait resolution helpers ---

    pub(super) fn bind_type_vars(pattern: &Type, actual: &Type, bindings: &mut HashMap<TypeVarId, Type>) -> bool {
        match (pattern, actual) {
            (Type::Var(id), ty) => {
                bindings.insert(*id, ty.clone());
                true
            }
            (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) => {
                p_name == a_name
                    && p_args.len() == a_args.len()
                    && p_args
                        .iter()
                        .zip(a_args.iter())
                        .all(|(pattern_arg, actual_arg)| {
                            Self::bind_type_vars(pattern_arg, actual_arg, bindings)
                        })
            }
            (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
                Self::bind_type_vars(p_ctor, a_ctor, bindings)
                    && p_args.len() == a_args.len()
                    && p_args
                        .iter()
                        .zip(a_args.iter())
                        .all(|(pattern_arg, actual_arg)| {
                            Self::bind_type_vars(pattern_arg, actual_arg, bindings)
                        })
            }
            (Type::App(p_ctor, p_args), Type::Named(a_name, a_args)) => {
                p_args.len() == a_args.len()
                    && Self::bind_type_vars(
                        p_ctor,
                        &Type::Named(a_name.clone(), Vec::new()),
                        bindings,
                    )
                    && p_args
                        .iter()
                        .zip(a_args.iter())
                        .all(|(pattern_arg, actual_arg)| {
                            Self::bind_type_vars(pattern_arg, actual_arg, bindings)
                        })
            }
            (Type::Own(pattern_inner), ty) => Self::bind_type_vars(pattern_inner, ty, bindings),
            (ty, Type::Own(actual_inner)) => Self::bind_type_vars(ty, actual_inner, bindings),
            (Type::Tuple(p_elems), Type::Tuple(a_elems)) => {
                p_elems.len() == a_elems.len()
                    && p_elems
                        .iter()
                        .zip(a_elems.iter())
                        .all(|(pattern_elem, actual_elem)| {
                            Self::bind_type_vars(pattern_elem, actual_elem, bindings)
                        })
            }
            (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
                p_params.len() == a_params.len()
                    && p_params
                        .iter()
                        .zip(a_params.iter())
                        .all(|(p, a)| Self::bind_type_vars(p, a, bindings))
                    && Self::bind_type_vars(p_ret, a_ret, bindings)
            }
            _ => pattern == actual,
        }
    }

    pub(super) fn extract_type_arg(ty: &Type, param_idx: usize) -> Option<Type> {
        match ty {
            Type::Named(_, args) => args.get(param_idx).cloned(),
            Type::Own(inner) => Self::extract_type_arg(inner, param_idx),
            _ => None,
        }
    }

    pub(super) fn resolve_dict_requirement_type(
        requirement: &DictRequirement,
        instance_info: &ParameterizedInstanceInfo,
        concrete_ty: &Type,
    ) -> Option<Type> {
        match requirement {
            DictRequirement::TypeParam { param_idx, .. } => {
                Self::extract_type_arg(concrete_ty, *param_idx)
            }
            DictRequirement::Constraint { type_var, .. } => {
                let mut bindings = HashMap::new();
                if Self::bind_type_vars(&instance_info.target_type, concrete_ty, &mut bindings) {
                    bindings.get(type_var).cloned()
                } else {
                    None
                }
            }
        }
    }

    pub(super) fn resolve_function_requirement_type(
        requirement: &DictRequirement,
        param_types: &[Type],
        args: &[TypedExpr],
        ret_info: Option<(&Type, &Type)>,
    ) -> Option<Type> {
        match requirement {
            DictRequirement::TypeParam { param_idx, .. } => {
                args.get(*param_idx).map(|arg| arg.ty.clone())
            }
            DictRequirement::Constraint { type_var, .. } => {
                let mut bindings = HashMap::new();
                for (param_ty, arg) in param_types.iter().zip(args.iter()) {
                    if !Self::bind_type_vars(param_ty, &arg.ty, &mut bindings) {
                        return None;
                    }
                }
                // For zero-arg functions, also try binding from return type
                if bindings.get(type_var).is_none() {
                    if let Some((ret_pattern, ret_actual)) = ret_info {
                        Self::bind_type_vars(ret_pattern, ret_actual, &mut bindings);
                    }
                }
                bindings.get(type_var).cloned()
            }
        }
    }

    pub(super) fn resolve_function_ref_requirement_type(
        requirement: &DictRequirement,
        declared_param_types: &[Type],
        actual_param_types: &[Type],
    ) -> Option<Type> {
        match requirement {
            DictRequirement::TypeParam { param_idx, .. } => {
                actual_param_types.get(*param_idx).cloned()
            }
            DictRequirement::Constraint { type_var, .. } => {
                let mut bindings = HashMap::new();
                for (declared, actual) in declared_param_types.iter().zip(actual_param_types.iter()) {
                    if !Self::bind_type_vars(declared, actual, &mut bindings) {
                        return None;
                    }
                }
                bindings.get(type_var).cloned()
            }
        }
    }

    pub(super) fn emit_dict_argument_for_type(
        &mut self,
        trait_name: &str,
        ty: &Type,
        pushed_class: u16,
    ) -> Result<(), CodegenError> {
        if matches!(ty, Type::Var(_))
            || matches!(ty, Type::App(ctor, _) if Self::is_abstract_type_ctor(ctor))
        {
            if let Some(&dict_slot) = self.traits.dict_locals.get(trait_name) {
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
        let singleton_key = (trait_name.to_string(), lookup_type.clone());
        let head_key = (trait_name.to_string(), Type::Named(head_type_name(ty)?, vec![]));
        if let Some(singleton) = self
            .traits
            .instance_singletons
            .get(&singleton_key)
            .or_else(|| self.traits.instance_singletons.get(&head_key))
        {
            self.builder.emit(Instruction::Getstatic(singleton.instance_field_ref));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: pushed_class,
            });
            return Ok(());
        }

        let head_name = head_type_name(ty)?;
        if let Some(instance_info) = self
            .traits
            .parameterized_instances
            .get(&(trait_name.to_string(), head_name))
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
                            CodegenError::UndefinedVariable(format!(
                                "could not resolve dictionary requirement {} for {ty}",
                                requirement.trait_name()
                            ))
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

        Err(CodegenError::UndefinedVariable(format!(
            "no instance of {trait_name} for {ty}"
        )))
    }
}
