use std::collections::HashMap;

use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedFnDecl};
use krypton_typechecker::types::{Type, TypeVarId};
use ristretto_classfile::attributes::{Attribute, Instruction, VerificationType};
use ristretto_classfile::{ClassAccessFlags, ClassFile, ConstantPool, Method, MethodAccessFlags};

use super::{jvm_type_to_field_descriptor, type_to_jvm_basic, type_to_name, JAVA_21};
use super::builder::{BytecodeBuilder, CpoolRefs};
use super::lambda::LambdaState;

/// Tracks the JVM type of a value on the operand stack.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum JvmType {
    Long,
    Double,
    Int,
    Ref,
    StructRef(u16), // cpool class index for struct type
}

/// Error type for codegen failures.
#[derive(Debug)]
pub enum CodegenError {
    ClassFile(ristretto_classfile::Error),
    NoMainFunction,
    UnsupportedExpr(String),
    UndefinedVariable(String),
    TypeError(String),
    RecurNotInTailPosition,
}

impl From<ristretto_classfile::Error> for CodegenError {
    fn from(e: ristretto_classfile::Error) -> Self {
        CodegenError::ClassFile(e)
    }
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodegenError::ClassFile(e) => write!(f, "class file error: {e}"),
            CodegenError::NoMainFunction => write!(f, "no main function found"),
            CodegenError::UnsupportedExpr(s) => write!(f, "unsupported expression: {s}"),
            CodegenError::UndefinedVariable(s) => write!(f, "undefined variable: {s}"),
            CodegenError::TypeError(s) => write!(f, "type error: {s}"),
            CodegenError::RecurNotInTailPosition => {
                write!(f, "recur must be in tail position")
            }
        }
    }
}

/// Info about a compiled user-defined function, used for invokestatic calls.
pub(super) struct FunctionInfo {
    pub(super) method_ref: u16,
    pub(super) param_types: Vec<JvmType>,
    pub(super) return_type: JvmType,
    pub(super) is_void: bool,
    pub(super) tc_param_types: Vec<Type>,
}

/// Info about a struct type for codegen.
#[derive(Debug)]
pub(super) struct StructInfo {
    pub(super) class_index: u16,
    pub(super) class_name: String,
    pub(super) fields: Vec<(String, JvmType)>,
    pub(super) constructor_ref: u16,
    pub(super) accessor_refs: HashMap<String, u16>,
}

/// Info about a single variant of a sum type.
pub(super) struct VariantInfo {
    pub(super) class_index: u16,
    pub(super) class_name: String,
    pub(super) fields: Vec<(String, JvmType, bool)>, // (name, jvm_type, is_erased)
    pub(super) constructor_ref: u16,
    pub(super) field_refs: Vec<u16>, // field ref indices in main cpool
    pub(super) singleton_field_ref: Option<u16>, // Some(field_ref) for nullary variants
}

/// Info about a sum type (sealed interface).
pub(super) struct SumTypeInfo {
    pub(super) interface_class_index: u16,
    pub(super) variants: HashMap<String, VariantInfo>,
}

/// Info about a tuple type (backed by krypton/runtime/TupleN).
pub(super) struct TupleInfo {
    pub(super) class_index: u16,
    pub(super) constructor_ref: u16,
    pub(super) field_refs: Vec<u16>,
}

/// Type registry for codegen (structs, sum types, tuples, functions).
pub(super) struct CodegenTypeInfo {
    pub(super) struct_info: HashMap<String, StructInfo>,
    pub(super) class_descriptors: HashMap<u16, String>,
    pub(super) sum_type_info: HashMap<String, SumTypeInfo>,
    pub(super) variant_to_sum: HashMap<String, String>,
    pub(super) tuple_info: HashMap<usize, TupleInfo>,
    pub(super) functions: HashMap<String, Vec<FunctionInfo>>,
    pub(super) fn_tc_types: HashMap<String, (Vec<Type>, Type)>,
}

impl CodegenTypeInfo {
    /// Get the first (or only) function info for a name.
    pub(super) fn get_function(&self, name: &str) -> Option<&FunctionInfo> {
        self.functions.get(name).and_then(|v| v.first())
    }

    /// Get a function info by matching TC param types (for overload disambiguation).
    pub(super) fn get_function_by_params(&self, name: &str, param_types: &[Type]) -> Option<&FunctionInfo> {
        let entries = self.functions.get(name)?;
        if entries.len() == 1 {
            return entries.first();
        }
        entries.iter().find(|fi| fi.tc_param_types == *param_types)
    }

    pub(super) fn jvm_type_descriptor(&self, ty: JvmType) -> String {
        match ty {
            JvmType::StructRef(idx) => self.class_descriptors[&idx].clone(),
            other => jvm_type_to_field_descriptor(other),
        }
    }

    pub(super) fn build_descriptor(&self, params: &[JvmType], ret: JvmType) -> String {
        let mut desc = String::from("(");
        for p in params {
            desc.push_str(&self.jvm_type_descriptor(*p));
        }
        desc.push(')');
        desc.push_str(&self.jvm_type_descriptor(ret));
        desc
    }
}

/// Info about a trait for dispatch.
pub(super) struct TraitDispatchInfo {
    pub(super) interface_class: u16, // class index of the trait interface in main cpool
    pub(super) method_refs: HashMap<String, u16>, // method_name → interface method_ref
}

/// Info about a trait instance singleton.
pub(super) struct InstanceSingletonInfo {
    pub(super) instance_field_ref: u16, // field_ref for INSTANCE field (for getstatic)
}

/// Trait dispatch state for codegen.
pub(super) struct TraitState {
    pub(super) trait_dispatch: HashMap<String, TraitDispatchInfo>,
    pub(super) instance_singletons: HashMap<(String, String), InstanceSingletonInfo>,
    pub(super) trait_method_map: HashMap<String, String>,
    pub(super) fn_constraints: HashMap<String, Vec<(String, usize)>>,
    pub(super) impl_dict_requirements: HashMap<String, Vec<DictRequirement>>,
    pub(super) dict_locals: HashMap<String, u16>,
    pub(super) parameterized_instances: HashMap<(String, String), ParameterizedInstanceInfo>,
}

#[derive(Clone)]
pub(super) enum DictRequirement {
    TypeParam {
        trait_name: String,
        param_idx: usize,
    },
    Constraint {
        trait_name: String,
        type_var: TypeVarId,
    },
}

impl DictRequirement {
    pub(super) fn trait_name(&self) -> &str {
        match self {
            DictRequirement::TypeParam { trait_name, .. }
            | DictRequirement::Constraint { trait_name, .. } => trait_name,
        }
    }
}

#[derive(Clone)]
pub(super) struct ParameterizedInstanceInfo {
    pub(super) class_name: String,
    pub(super) target_type: Type,
    pub(super) requirements: Vec<DictRequirement>,
}

/// Info about the Vec backing class (KryptonArray).
#[derive(Clone)]
pub(super) struct VecInfo {
    pub(super) class_index: u16,
    pub(super) init_ref: u16,
    pub(super) set_ref: u16,
    pub(super) freeze_ref: u16,
}

pub(super) struct Compiler {
    pub(super) cp: ConstantPool,
    pub(super) this_class: u16,
    pub(super) builder: BytecodeBuilder,
    pub(super) lambda: LambdaState,
    pub(super) types: CodegenTypeInfo,
    pub(super) traits: TraitState,
    pub(super) vec_info: Option<VecInfo>,
    pub(super) auto_close: krypton_typechecker::typed_ast::AutoCloseInfo,
}

impl Compiler {
    pub(super) fn is_abstract_type_ctor(ty: &Type) -> bool {
        match ty {
            Type::Var(_) => true,
            Type::Own(inner) => Self::is_abstract_type_ctor(inner),
            Type::App(ctor, _) => Self::is_abstract_type_ctor(ctor),
            _ => false,
        }
    }

    pub(super) fn new(class_name: &str) -> Result<(Self, u16, u16), CodegenError> {
        let mut cp = ConstantPool::default();

        let this_class = cp.add_class(class_name)?;
        let object_class = cp.add_class("java/lang/Object")?;
        let code_utf8 = cp.add_utf8("Code")?;
        let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
        let init_name = cp.add_utf8("<init>")?;
        let init_desc = cp.add_utf8("()V")?;

        // StackMapTable support
        let smt_name = cp.add_utf8("StackMapTable")?;
        let string_class = cp.add_class("java/lang/String")?;
        let string_arr_class = cp.add_class("[Ljava/lang/String;")?;

        // Boxing support: Long.valueOf, Double.valueOf, Boolean.valueOf
        let long_box_class = cp.add_class("java/lang/Long")?;
        let long_box_valueof =
            cp.add_method_ref(long_box_class, "valueOf", "(J)Ljava/lang/Long;")?;
        let double_box_class = cp.add_class("java/lang/Double")?;
        let double_box_valueof =
            cp.add_method_ref(double_box_class, "valueOf", "(D)Ljava/lang/Double;")?;
        let bool_box_class = cp.add_class("java/lang/Boolean")?;
        let bool_box_valueof =
            cp.add_method_ref(bool_box_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;

        // Unboxing support
        let long_unbox = cp.add_method_ref(long_box_class, "longValue", "()J")?;
        let double_unbox = cp.add_method_ref(double_box_class, "doubleValue", "()D")?;
        let bool_unbox = cp.add_method_ref(bool_box_class, "booleanValue", "()Z")?;

        // String operations
        let string_concat = cp.add_method_ref(
            string_class,
            "concat",
            "(Ljava/lang/String;)Ljava/lang/String;",
        )?;
        let string_equals = cp.add_method_ref(string_class, "equals", "(Ljava/lang/Object;)Z")?;

        // Intrinsic support
        let runtime_exception_class = cp.add_class("java/lang/RuntimeException")?;
        let runtime_exception_init =
            cp.add_method_ref(runtime_exception_class, "<init>", "(Ljava/lang/String;)V")?;
        let refs = CpoolRefs {
            code_utf8,
            object_init,
            init_name,
            init_desc,
            smt_name,
            string_class,
            long_box_valueof,
            double_box_valueof,
            bool_box_valueof,
            long_box_class,
            long_unbox,
            double_box_class,
            double_unbox,
            bool_box_class,
            bool_unbox,
            object_class,
            string_concat,
            string_equals,
            runtime_exception_class,
            runtime_exception_init,
        };
        let mut builder = BytecodeBuilder::new(refs);
        builder.next_local = 1; // slot 0 = String[] args for main
        builder.frame.local_types = vec![VerificationType::Object {
            cpool_index: string_arr_class,
        }];

        let compiler = Compiler {
            cp,
            this_class,
            builder,
            lambda: LambdaState {
                lambda_counter: 0,
                lambda_methods: Vec::new(),
                bootstrap_methods: Vec::new(),
                metafactory_handle: None,
                fun_classes: HashMap::new(),
                fun_apply_refs: HashMap::new(),
            },
            types: CodegenTypeInfo {
                struct_info: HashMap::new(),
                class_descriptors: HashMap::new(),
                sum_type_info: HashMap::new(),
                variant_to_sum: HashMap::new(),
                tuple_info: HashMap::new(),
                functions: HashMap::new(),
                fn_tc_types: HashMap::new(),
            },
            traits: TraitState {
                trait_dispatch: HashMap::new(),
                instance_singletons: HashMap::new(),
                trait_method_map: HashMap::new(),
                fn_constraints: HashMap::new(),
                impl_dict_requirements: HashMap::new(),
                dict_locals: HashMap::new(),
                parameterized_instances: HashMap::new(),
            },
            vec_info: None,
            auto_close: krypton_typechecker::typed_ast::AutoCloseInfo::default(),
        };

        Ok((compiler, this_class, object_class))
    }

    /// Map a typechecker Type to a JvmType, using struct_info/sum_type_info for Named types.
    pub(super) fn type_to_jvm(&self, ty: &Type) -> Result<JvmType, CodegenError> {
        match ty {
            Type::Named(name, _) => {
                if name == "Object" {
                    return Ok(JvmType::StructRef(self.builder.refs.object_class));
                }
                if name == "Vec" {
                    if let Some(info) = &self.vec_info {
                        return Ok(JvmType::StructRef(info.class_index));
                    }
                }
                if let Some(info) = self.types.struct_info.get(name) {
                    Ok(JvmType::StructRef(info.class_index))
                } else if let Some(info) = self.types.sum_type_info.get(name) {
                    Ok(JvmType::StructRef(info.interface_class_index))
                } else {
                    Err(CodegenError::TypeError(format!(
                        "unknown named type: {name}"
                    )))
                }
            }
            Type::Var(_) => Ok(JvmType::StructRef(self.builder.refs.object_class)),
            Type::Fn(params, _) => {
                let arity = params.len() as u8;
                if let Some(&class_idx) = self.lambda.fun_classes.get(&arity) {
                    Ok(JvmType::StructRef(class_idx))
                } else {
                    Ok(JvmType::StructRef(self.builder.refs.object_class))
                }
            }
            Type::Tuple(elems) => {
                let arity = elems.len();
                if let Some(info) = self.types.tuple_info.get(&arity) {
                    Ok(JvmType::StructRef(info.class_index))
                } else {
                    Err(CodegenError::TypeError(format!(
                        "unknown tuple arity: {arity}"
                    )))
                }
            }
            Type::Own(inner) => self.type_to_jvm(inner),
            Type::App(ctor, _) if Self::is_abstract_type_ctor(ctor) => {
                Ok(JvmType::StructRef(self.builder.refs.object_class))
            }
            Type::App(_, _) => {
                Err(CodegenError::TypeError(format!(
                    "unexpected unreduced concrete type application during codegen erasure: {ty}"
                )))
            }
            other => type_to_jvm_basic(other),
        }
    }

    /// Reset per-method compilation state.
    pub(super) fn reset_method_state(&mut self) {
        self.builder.reset();
        self.traits.dict_locals.clear();
    }

    pub(super) fn compile_expr(
        &mut self,
        expr: &TypedExpr,
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        match &expr.kind {
            TypedExprKind::Lit(value) => self.compile_lit(value),
            TypedExprKind::BinaryOp { op, lhs, rhs } => self.compile_binop(op, lhs, rhs),
            TypedExprKind::If { cond, then_, else_ } => {
                self.compile_if(cond, then_, else_, in_tail)
            }
            TypedExprKind::Let { name, value, body } => {
                self.compile_let(name, value, body, in_tail, expr.span)
            }
            TypedExprKind::Var(name) => {
                let fn_type = match &expr.ty {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                if matches!(fn_type, Type::Fn(_, _)) && !self.builder.locals.contains_key(name) {
                    if self.types.functions.contains_key(name)
                        || self.types.struct_info.contains_key(name)
                        || self
                            .types
                            .variant_to_sum
                            .get(name)
                            .and_then(|sum_name| self.types.sum_type_info.get(sum_name))
                            .and_then(|sum_info| sum_info.variants.get(name))
                            .is_some_and(|variant| !variant.fields.is_empty())
                    {
                        return self.compile_fn_ref(name, &expr.ty);
                    }
                }
                self.compile_var(name)
            }
            TypedExprKind::Do(exprs) => self.compile_do(exprs, in_tail),
            TypedExprKind::App { func, args } => self.compile_app(func, args, &expr.ty),
            TypedExprKind::TypeApp { expr: inner } => {
                if let TypedExprKind::Var(name) = &inner.kind {
                    let fn_type = match &expr.ty {
                        Type::Own(inner) => inner.as_ref(),
                        other => other,
                    };
                    if matches!(fn_type, Type::Fn(_, _)) && !self.builder.locals.contains_key(name) {
                        if self.types.functions.contains_key(name)
                            || self.types.struct_info.contains_key(name)
                            || self
                                .types
                                .variant_to_sum
                                .get(name)
                                .and_then(|sum_name| self.types.sum_type_info.get(sum_name))
                                .and_then(|sum_info| sum_info.variants.get(name))
                                .is_some_and(|variant| !variant.fields.is_empty())
                        {
                            return self.compile_fn_ref(name, &expr.ty);
                        }
                    }
                }
                self.compile_expr(inner, in_tail)
            }
            TypedExprKind::Recur(args) => self.compile_recur(args, in_tail, expr.span),
            TypedExprKind::FieldAccess {
                expr: target,
                field,
            } => self.compile_field_access(target, field),
            TypedExprKind::Tuple(elems) => self.compile_tuple(elems, &expr.ty),
            TypedExprKind::LetPattern {
                pattern,
                value,
                body,
            } => self.compile_let_pattern(pattern, value, body, in_tail),
            TypedExprKind::StructLit { fields, .. } => self.compile_struct_lit(fields, &expr.ty),
            TypedExprKind::StructUpdate { base, fields } => {
                self.compile_struct_update(base, fields)
            }
            TypedExprKind::Match { scrutinee, arms } => {
                self.compile_match(scrutinee, arms, in_tail)
            }
            TypedExprKind::UnaryOp { op, operand } => self.compile_unaryop(op, operand),
            TypedExprKind::Lambda { params, body } => self.compile_lambda(params, body, &expr.ty),
            TypedExprKind::QuestionMark {
                expr: inner,
                is_option,
            } => self.compile_question_mark(inner, *is_option, &expr.ty, expr.span),
            TypedExprKind::VecLit(elems) => self.compile_vec_lit(elems),
            other => Err(CodegenError::UnsupportedExpr(format!("{other:?}"))),
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
                return Ok(());
            }
        }

        let type_name = type_to_name(ty);
        if let Some(singleton) = self
            .traits
            .instance_singletons
            .get(&(trait_name.to_string(), type_name.clone()))
        {
            self.builder.emit(Instruction::Getstatic(singleton.instance_field_ref));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: pushed_class,
            });
            return Ok(());
        }

        if let Some(instance_info) = self
            .traits
            .parameterized_instances
            .get(&(trait_name.to_string(), type_name))
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

    /// Compile a function declaration into a JVM Method.
    pub(super) fn compile_function(&mut self, decl: &TypedFnDecl) -> Result<Method, CodegenError> {
        self.reset_method_state();

        // Look up the function's type info
        let info = self
            .types
            .get_function(&decl.name)
            .ok_or_else(|| CodegenError::UndefinedVariable(decl.name.clone()))?;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;

        // Get typechecker types for this function's params (for detecting Fn-typed params)
        let tc_types = self.types.fn_tc_types.get(&decl.name).cloned();

        // Register dict params for constrained functions (leading params before user params)
        let dict_requirements = if let Some(requirements) =
            self.traits.impl_dict_requirements.get(&decl.name)
        {
            requirements.clone()
        } else {
            self.traits
                .fn_constraints
                .get(&decl.name)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .map(|(trait_name, param_idx)| DictRequirement::TypeParam {
                    trait_name,
                    param_idx,
                })
                .collect()
        };
        let num_dict_params = dict_requirements.len();
        let mut fn_params = Vec::new();
        for requirement in &dict_requirements {
            let slot = self.builder.next_local;
            let jvm_ty = JvmType::StructRef(self.builder.refs.object_class);
            self.traits
                .dict_locals
                .insert(requirement.trait_name().to_string(), slot);
            fn_params.push((slot, jvm_ty));
            self.builder.next_local += 1;
            self.builder.frame.local_types.push(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
        }

        // Register user parameters as locals and save fn_params for recur
        for (i, (param_name, &jvm_ty)) in decl
            .params
            .iter()
            .zip(param_types[num_dict_params..].iter())
            .enumerate()
        {
            let slot = self.builder.alloc_local(param_name.clone(), jvm_ty);
            fn_params.push((slot, jvm_ty));

            // If this param is function-typed, register in local_fn_info
            if let Some((ref tc_param_types, _)) = tc_types {
                let tc_param_type = match &tc_param_types[i] {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                if let Type::Fn(inner_params, inner_ret) = tc_param_type {
                    let inner_param_jvm: Vec<JvmType> = inner_params
                        .iter()
                        .map(|t| self.type_to_jvm(t))
                        .collect::<Result<_, _>>()?;
                    let inner_ret_jvm = self.type_to_jvm(inner_ret)?;
                    let arity = inner_params.len() as u8;
                    self.lambda.ensure_fun_interface(
                        arity,
                        &mut self.cp,
                        &mut self.types.class_descriptors,
                    )?;
                    self.builder.local_fn_info
                        .insert(param_name.clone(), (inner_param_jvm, inner_ret_jvm));
                }
            }
        }
        self.builder.fn_params = fn_params;
        self.builder.fn_return_type = Some(return_type);

        // Emit Nop as recur back-edge target at instruction 0.
        self.builder.emit(Instruction::Nop);
        self.builder.recur_target = self.builder.code.len() as u16;
        self.builder.recur_frame_locals = self.builder.frame.local_types.clone();

        // Compile function body
        let body_type = self.compile_expr(&decl.body, true)?;

        // If body type is Object but return type is primitive, unbox
        if matches!(body_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
            && !matches!(return_type, JvmType::StructRef(_) | JvmType::Ref)
        {
            self.builder.unbox_if_needed(return_type);
        }
        // If body type is primitive but return type is Object, box
        else if matches!(return_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
            && !matches!(body_type, JvmType::StructRef(_) | JvmType::Ref)
        {
            self.builder.box_if_needed(body_type);
        }
        // If body type is Object but return type is a specific reference type, checkcast
        else if matches!(body_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
            && matches!(return_type, JvmType::Ref | JvmType::StructRef(_))
            && !matches!(return_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
        {
            let cast_class = match return_type {
                JvmType::Ref => self.builder.refs.string_class,
                JvmType::StructRef(idx) => idx,
                _ => unreachable!(),
            };
            self.builder.emit(Instruction::Checkcast(cast_class));
            self.builder.frame.pop_type();
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: cast_class,
            });
        }

        // Auto-close live resources at function exit
        if let Some(bindings) = self.auto_close.fn_exits.get(&decl.name).cloned() {
            // Save return value to temp
            let ret_slot = self.builder.alloc_anonymous_local(return_type);
            self.builder.emit_store(ret_slot, return_type);

            for binding in &bindings {
                self.emit_auto_close(binding)?;
            }

            // Reload return value
            self.builder.emit_load(ret_slot, return_type);
        }

        // Emit typed return
        let ret_instr = match return_type {
            JvmType::Long => Instruction::Lreturn,
            JvmType::Double => Instruction::Dreturn,
            JvmType::Int => Instruction::Ireturn,
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Areturn,
        };
        self.builder.emit(ret_instr);

        let descriptor = self.types.build_descriptor(&param_types, return_type);
        let name_idx = self.cp.add_utf8(&decl.name)?;
        let desc_idx = self.cp.add_utf8(&descriptor)?;

        Ok(Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![self.builder.finish_method()],
        })
    }

    pub(super) fn build_class(
        mut self,
        this_class: u16,
        object_class: u16,
        extra_methods: Vec<Method>,
        is_main: bool,
    ) -> Result<Vec<u8>, CodegenError> {
        let constructor = Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: self.builder.refs.init_name,
            descriptor_index: self.builder.refs.init_desc,
            attributes: vec![Attribute::Code {
                name_index: self.builder.refs.code_utf8,
                max_stack: 1,
                max_locals: 1,
                code: vec![
                    Instruction::Aload_0,
                    Instruction::Invokespecial(self.builder.refs.object_init),
                    Instruction::Return,
                ],
                exception_table: vec![],
                attributes: vec![],
            }],
        };

        let mut methods = vec![constructor];
        methods.extend(extra_methods);
        // Add lambda methods
        methods.extend(std::mem::take(&mut self.lambda.lambda_methods));

        if is_main {
            let main_name = self.cp.add_utf8("main")?;
            let main_desc = self.cp.add_utf8("([Ljava/lang/String;)V")?;

            let main_method = Method {
                access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
                name_index: main_name,
                descriptor_index: main_desc,
                attributes: vec![self.builder.finish_method()],
            };
            methods.push(main_method);
        }

        // Build class attributes (BootstrapMethods if any)
        let mut class_attributes = Vec::new();
        if !self.lambda.bootstrap_methods.is_empty() {
            let bsm_name = self.cp.add_utf8("BootstrapMethods")?;
            class_attributes.push(Attribute::BootstrapMethods {
                name_index: bsm_name,
                methods: std::mem::take(&mut self.lambda.bootstrap_methods),
            });
        }

        let class_file = ClassFile {
            version: JAVA_21,
            access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
            constant_pool: self.cp,
            this_class,
            super_class: object_class,
            methods,
            attributes: class_attributes,
            ..Default::default()
        };

        let mut buffer = Vec::new();
        class_file.to_bytes(&mut buffer)?;
        Ok(buffer)
    }
}
