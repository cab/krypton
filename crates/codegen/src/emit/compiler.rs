use std::collections::{BTreeMap, HashMap};

use krypton_parser::ast::{BinOp, Lit, UnaryOp};
use krypton_typechecker::typed_ast::{
    TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedPattern,
};
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{
    Attribute, BootstrapMethod, Instruction, StackFrame, VerificationType,
};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Method, MethodAccessFlags, ReferenceKind,
};

use super::{is_intrinsic, jvm_type_to_field_descriptor, type_to_jvm_basic, type_to_name, JAVA_21};

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

/// Well-known constant pool indices, set once in `new()`, read-only after.
pub(super) struct CpoolRefs {
    pub(super) code_utf8: u16,
    pub(super) object_init: u16,
    pub(super) init_name: u16,
    pub(super) init_desc: u16,
    pub(super) smt_name: u16,
    pub(super) string_class: u16,
    pub(super) long_box_valueof: u16,
    pub(super) double_box_valueof: u16,
    pub(super) bool_box_valueof: u16,
    pub(super) long_box_class: u16,
    pub(super) long_unbox: u16,
    pub(super) double_box_class: u16,
    pub(super) double_unbox: u16,
    pub(super) bool_box_class: u16,
    pub(super) bool_unbox: u16,
    pub(super) object_class: u16,
    pub(super) string_concat: u16,
    pub(super) string_equals: u16,
    // Intrinsic support
    pub(super) runtime_exception_class: u16,
    pub(super) runtime_exception_init: u16,
}

/// StackMapTable / verification type tracking.
pub(super) struct FrameState {
    pub(super) stack_types: Vec<VerificationType>,
    pub(super) local_types: Vec<VerificationType>,
    pub(super) frames: BTreeMap<u16, (Vec<VerificationType>, Vec<VerificationType>)>,
    pub(super) max_stack_depth: usize,
}

impl FrameState {
    fn update_max_depth(&mut self) {
        self.max_stack_depth = self.max_stack_depth.max(self.stack_types.len());
    }

    fn max_stack(&self) -> u16 {
        (self.max_stack_depth as u16).max(1)
    }

    fn push_type(&mut self, vt: VerificationType) {
        self.stack_types.push(vt);
        self.update_max_depth();
    }

    fn push_long_type(&mut self) {
        self.stack_types.push(VerificationType::Long);
        self.stack_types.push(VerificationType::Top);
        self.update_max_depth();
    }

    fn push_double_type(&mut self) {
        self.stack_types.push(VerificationType::Double);
        self.stack_types.push(VerificationType::Top);
        self.update_max_depth();
    }

    pub(super) fn pop_type(&mut self) {
        self.stack_types.pop();
    }

    pub(super) fn pop_type_n(&mut self, n: usize) {
        self.stack_types.truncate(self.stack_types.len() - n);
    }

    fn record_frame(&mut self, instr_idx: u16) {
        fn strip_tops(types: &[VerificationType]) -> Vec<VerificationType> {
            types
                .iter()
                .filter(|vt| !matches!(vt, VerificationType::Top))
                .cloned()
                .collect()
        }
        self.frames.insert(
            instr_idx,
            (strip_tops(&self.local_types), strip_tops(&self.stack_types)),
        );
    }

    fn jvm_type_to_vtypes(&self, ty: JvmType, string_class: u16) -> Vec<VerificationType> {
        match ty {
            JvmType::Long => vec![VerificationType::Long, VerificationType::Top],
            JvmType::Double => vec![VerificationType::Double, VerificationType::Top],
            JvmType::Int => vec![VerificationType::Integer],
            JvmType::Ref => vec![VerificationType::Object {
                cpool_index: string_class,
            }],
            JvmType::StructRef(idx) => vec![VerificationType::Object { cpool_index: idx }],
        }
    }

    fn push_jvm_type(&mut self, ty: JvmType, string_class: u16) {
        for vt in self.jvm_type_to_vtypes(ty, string_class) {
            self.stack_types.push(vt);
        }
        self.update_max_depth();
    }

    fn pop_jvm_type(&mut self, ty: JvmType) {
        match ty {
            JvmType::Long | JvmType::Double => self.pop_type_n(2),
            JvmType::Int | JvmType::Ref | JvmType::StructRef(_) => self.pop_type(),
        }
    }

    fn build_stack_map_frames(&self) -> Vec<StackFrame> {
        let mut frames = Vec::new();
        let mut prev_offset: Option<u16> = None;

        for (&instr_idx, (locals, stack)) in &self.frames {
            let offset_delta = match prev_offset {
                None => instr_idx,
                Some(prev) => instr_idx - prev - 1,
            };
            prev_offset = Some(instr_idx);

            frames.push(StackFrame::FullFrame {
                frame_type: 255,
                offset_delta,
                locals: locals.clone(),
                stack: stack.clone(),
            });
        }

        frames
    }

    fn reset(&mut self) {
        self.stack_types.clear();
        self.local_types.clear();
        self.frames.clear();
        self.max_stack_depth = 0;
    }
}

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
        let class_name = format!("Fun{arity}");
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

    fn ensure_metafactory(&mut self, cp: &mut ConstantPool) -> Result<u16, CodegenError> {
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

/// Type registry for codegen (structs, sum types, tuples, functions).
pub(super) struct CodegenTypeInfo {
    pub(super) struct_info: HashMap<String, StructInfo>,
    pub(super) class_descriptors: HashMap<u16, String>,
    pub(super) sum_type_info: HashMap<String, SumTypeInfo>,
    pub(super) variant_to_sum: HashMap<String, String>,
    pub(super) tuple_info: HashMap<usize, TupleInfo>,
    pub(super) functions: HashMap<String, FunctionInfo>,
    pub(super) fn_tc_types: HashMap<String, (Vec<Type>, Type)>,
}

impl CodegenTypeInfo {
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
        type_var: u32,
    },
}

impl DictRequirement {
    fn trait_name(&self) -> &str {
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
    pub(super) refs: CpoolRefs,
    pub(super) frame: FrameState,
    pub(super) lambda: LambdaState,
    pub(super) types: CodegenTypeInfo,
    pub(super) code: Vec<Instruction>,
    pub(super) locals: HashMap<String, (u16, JvmType)>,
    pub(super) next_local: u16,
    pub(super) fn_params: Vec<(u16, JvmType)>,
    pub(super) fn_return_type: Option<JvmType>,
    pub(super) nested_ifeq_patches: Vec<usize>,
    pub(super) local_fn_info: HashMap<String, (Vec<JvmType>, JvmType)>,
    pub(super) traits: TraitState,
    pub(super) vec_info: Option<VecInfo>,
    pub(super) auto_close: krypton_typechecker::typed_ast::AutoCloseInfo,
}

impl Compiler {
    fn is_abstract_type_ctor(ty: &Type) -> bool {
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
        let compiler = Compiler {
            cp,
            this_class,
            refs: CpoolRefs {
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
            },
            frame: FrameState {
                stack_types: Vec::new(),
                local_types: vec![VerificationType::Object {
                    cpool_index: string_arr_class,
                }],
                frames: BTreeMap::new(),
                max_stack_depth: 0,
            },
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
            code: Vec::new(),
            locals: HashMap::new(),
            next_local: 1, // slot 0 = String[] args for main
            fn_params: Vec::new(),
            fn_return_type: None,
            nested_ifeq_patches: Vec::new(),
            local_fn_info: HashMap::new(),
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
            Type::Var(_) => Ok(JvmType::StructRef(self.refs.object_class)),
            Type::Fn(params, _) => {
                let arity = params.len() as u8;
                if let Some(&class_idx) = self.lambda.fun_classes.get(&arity) {
                    Ok(JvmType::StructRef(class_idx))
                } else {
                    Ok(JvmType::StructRef(self.refs.object_class))
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
                Ok(JvmType::StructRef(self.refs.object_class))
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
        self.code.clear();
        self.locals.clear();
        self.next_local = 0;
        self.frame.reset();
        self.fn_params.clear();
        self.fn_return_type = None;
        self.local_fn_info.clear();
        self.traits.dict_locals.clear();
    }

    pub(super) fn emit(&mut self, instr: Instruction) {
        self.code.push(instr);
    }

    // Convenience delegators to FrameState (avoid passing string_class everywhere)
    pub(super) fn push_jvm_type(&mut self, ty: JvmType) {
        self.frame.push_jvm_type(ty, self.refs.string_class);
    }

    fn pop_jvm_type(&mut self, ty: JvmType) {
        self.frame.pop_jvm_type(ty);
    }

    fn jvm_type_to_vtypes(&self, ty: JvmType) -> Vec<VerificationType> {
        self.frame.jvm_type_to_vtypes(ty, self.refs.string_class)
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
                if matches!(fn_type, Type::Fn(_, _)) && !self.locals.contains_key(name) {
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
                    if matches!(fn_type, Type::Fn(_, _)) && !self.locals.contains_key(name) {
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

    fn compile_lit(&mut self, lit: &Lit) -> Result<JvmType, CodegenError> {
        match lit {
            Lit::Int(n) => {
                match *n {
                    0 => self.emit(Instruction::Lconst_0),
                    1 => self.emit(Instruction::Lconst_1),
                    _ => {
                        let idx = self.cp.add_long(*n)?;
                        self.emit(Instruction::Ldc2_w(idx));
                    }
                }
                self.frame.push_long_type();
                Ok(JvmType::Long)
            }
            Lit::Float(f) => {
                let idx = self.cp.add_double(*f)?;
                self.emit(Instruction::Ldc2_w(idx));
                self.frame.push_double_type();
                Ok(JvmType::Double)
            }
            Lit::Bool(b) => {
                self.emit(if *b {
                    Instruction::Iconst_1
                } else {
                    Instruction::Iconst_0
                });
                self.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            Lit::String(s) => {
                let idx = self.cp.add_string(s)?;
                if idx <= 255 {
                    self.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.emit(Instruction::Ldc_w(idx));
                }
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.string_class,
                });
                Ok(JvmType::Ref)
            }
            Lit::Unit => {
                self.emit(Instruction::Iconst_0);
                self.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
        }
    }

    fn compile_binop(
        &mut self,
        op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
    ) -> Result<JvmType, CodegenError> {
        // Check the operand type from the typed AST to determine dispatch strategy
        let operand_jvm = self.type_to_jvm(&lhs.ty)?;

        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                match operand_jvm {
                    JvmType::Long => {
                        self.compile_expr(lhs, false)?;
                        self.compile_expr(rhs, false)?;
                        let instr = match op {
                            BinOp::Add => Instruction::Ladd,
                            BinOp::Sub => Instruction::Lsub,
                            BinOp::Mul => Instruction::Lmul,
                            BinOp::Div => Instruction::Ldiv,
                            _ => unreachable!(),
                        };
                        self.emit(instr);
                        self.frame.pop_type_n(4);
                        self.frame.push_long_type();
                        Ok(JvmType::Long)
                    }
                    JvmType::Double => {
                        self.compile_expr(lhs, false)?;
                        self.compile_expr(rhs, false)?;
                        let instr = match op {
                            BinOp::Add => Instruction::Dadd,
                            BinOp::Sub => Instruction::Dsub,
                            BinOp::Mul => Instruction::Dmul,
                            BinOp::Div => Instruction::Ddiv,
                            _ => unreachable!(),
                        };
                        self.emit(instr);
                        self.frame.pop_type_n(4);
                        self.frame.push_double_type();
                        Ok(JvmType::Double)
                    }
                    JvmType::Ref if matches!(op, BinOp::Add) => {
                        // String concat: invokevirtual String.concat
                        self.compile_expr(lhs, false)?;
                        self.compile_expr(rhs, false)?;
                        self.emit(Instruction::Invokevirtual(self.refs.string_concat));
                        self.frame.pop_type(); // pop rhs string
                                               // receiver consumed, result string pushed (net: pop 1 push 0, but
                                               // invokevirtual pops receiver+arg and pushes result, so just pop rhs)
                        Ok(JvmType::Ref)
                    }
                    _ => {
                        // User-type trait dispatch
                        let (trait_name, method_name) = match op {
                            BinOp::Add => ("Semigroup", "combine"),
                            BinOp::Sub => ("Sub", "sub"),
                            BinOp::Mul => ("Mul", "mul"),
                            BinOp::Div => ("Div", "div"),
                            _ => unreachable!(),
                        };
                        self.compile_trait_binop(trait_name, method_name, lhs, rhs, operand_jvm)
                    }
                }
            }
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.compile_comparison(op, lhs, rhs)
            }
            BinOp::And => {
                // Short-circuit AND: if lhs is false, result is false
                self.compile_expr(lhs, false)?;
                let false_label = self.code.len();
                self.emit(Instruction::Ifeq(0)); // placeholder
                self.frame.pop_type();
                self.compile_expr(rhs, false)?;
                let end_label = self.code.len();
                self.emit(Instruction::Goto(0)); // placeholder
                self.frame.pop_type();
                let false_pos = self.code.len();
                // Record frame at false_pos (Ifeq target: stack has no boolean result)
                self.frame.record_frame(false_pos as u16);
                self.emit(Instruction::Iconst_0);
                self.frame.push_type(VerificationType::Integer);
                let end_pos = self.code.len();
                // Record frame at end_pos (both paths converge with Integer on stack)
                self.frame.record_frame(end_pos as u16);
                // Patch jumps
                self.code[false_label] = Instruction::Ifeq(false_pos as u16);
                self.code[end_label] = Instruction::Goto(end_pos as u16);
                Ok(JvmType::Int)
            }
            BinOp::Or => {
                // Short-circuit OR: if lhs is true, result is true
                self.compile_expr(lhs, false)?;
                let true_label = self.code.len();
                self.emit(Instruction::Ifne(0)); // placeholder
                self.frame.pop_type();
                self.compile_expr(rhs, false)?;
                let end_label = self.code.len();
                self.emit(Instruction::Goto(0)); // placeholder
                self.frame.pop_type();
                let true_pos = self.code.len();
                // Record frame at true_pos (Ifne target: stack has no boolean result)
                self.frame.record_frame(true_pos as u16);
                self.emit(Instruction::Iconst_1);
                self.frame.push_type(VerificationType::Integer);
                let end_pos = self.code.len();
                // Record frame at end_pos (both paths converge with Integer on stack)
                self.frame.record_frame(end_pos as u16);
                // Patch jumps
                self.code[true_label] = Instruction::Ifne(true_pos as u16);
                self.code[end_label] = Instruction::Goto(end_pos as u16);
                Ok(JvmType::Int)
            }
        }
    }

    /// Compile a binary operator via trait dictionary dispatch for user types.
    /// Emits: getstatic INSTANCE, box(lhs), box(rhs), invokeinterface, unbox result
    fn compile_trait_binop(
        &mut self,
        trait_name: &str,
        method_name: &str,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        result_jvm: JvmType,
    ) -> Result<JvmType, CodegenError> {
        let type_name = type_to_name(&lhs.ty);

        let dispatch = self.traits.trait_dispatch.get(trait_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no trait dispatch for {trait_name}"))
        })?;
        let iface_method_ref = *dispatch.method_refs.get(method_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no method {method_name} in {trait_name}"))
        })?;
        let iface_class = dispatch.interface_class;

        let singleton = self
            .traits
            .instance_singletons
            .get(&(trait_name.to_string(), type_name.clone()))
            .ok_or_else(|| {
                CodegenError::UndefinedVariable(format!(
                    "no instance of {trait_name} for {type_name}"
                ))
            })?;
        let field_ref = singleton.instance_field_ref;

        // Load singleton instance
        self.emit(Instruction::Getstatic(field_ref));
        self.frame.push_type(VerificationType::Object {
            cpool_index: iface_class,
        });

        // Compile and box lhs
        let lhs_jvm = self.compile_expr(lhs, false)?;
        self.box_if_needed(lhs_jvm);

        // Compile and box rhs
        let rhs_jvm = self.compile_expr(rhs, false)?;
        self.box_if_needed(rhs_jvm);

        // invokeinterface (receiver + 2 args = 3)
        self.emit(Instruction::Invokeinterface(iface_method_ref, 3));
        self.frame.pop_type(); // rhs
        self.frame.pop_type(); // lhs
        self.frame.pop_type(); // receiver
        self.frame.push_type(VerificationType::Object {
            cpool_index: self.refs.object_class,
        });

        // Unbox result
        self.unbox_if_needed(result_jvm);
        Ok(result_jvm)
    }

    /// Compile a unary operator via trait dictionary dispatch for user types.
    fn compile_trait_unaryop(
        &mut self,
        trait_name: &str,
        method_name: &str,
        operand: &TypedExpr,
        result_jvm: JvmType,
    ) -> Result<JvmType, CodegenError> {
        let type_name = type_to_name(&operand.ty);

        let dispatch = self.traits.trait_dispatch.get(trait_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no trait dispatch for {trait_name}"))
        })?;
        let iface_method_ref = *dispatch.method_refs.get(method_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no method {method_name} in {trait_name}"))
        })?;
        let iface_class = dispatch.interface_class;

        let singleton = self
            .traits
            .instance_singletons
            .get(&(trait_name.to_string(), type_name.clone()))
            .ok_or_else(|| {
                CodegenError::UndefinedVariable(format!(
                    "no instance of {trait_name} for {type_name}"
                ))
            })?;
        let field_ref = singleton.instance_field_ref;

        // Load singleton instance
        self.emit(Instruction::Getstatic(field_ref));
        self.frame.push_type(VerificationType::Object {
            cpool_index: iface_class,
        });

        // Compile and box operand
        let op_jvm = self.compile_expr(operand, false)?;
        self.box_if_needed(op_jvm);

        // invokeinterface (receiver + 1 arg = 2)
        self.emit(Instruction::Invokeinterface(iface_method_ref, 2));
        self.frame.pop_type(); // operand
        self.frame.pop_type(); // receiver
        self.frame.push_type(VerificationType::Object {
            cpool_index: self.refs.object_class,
        });

        // Unbox result
        self.unbox_if_needed(result_jvm);
        Ok(result_jvm)
    }

    fn compile_comparison(
        &mut self,
        op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
    ) -> Result<JvmType, CodegenError> {
        let operand_jvm = self.type_to_jvm(&lhs.ty)?;

        // String equality: use String.equals
        if operand_jvm == JvmType::Ref && matches!(op, BinOp::Eq | BinOp::Neq) {
            self.compile_expr(lhs, false)?;
            self.compile_expr(rhs, false)?;
            self.emit(Instruction::Invokevirtual(self.refs.string_equals));
            self.frame.pop_type(); // pop arg
            self.frame.pop_type(); // pop receiver
            self.frame.push_type(VerificationType::Integer); // boolean result
            if matches!(op, BinOp::Neq) {
                // Negate: XOR with 1
                self.emit(Instruction::Iconst_1);
                self.frame.push_type(VerificationType::Integer);
                self.emit(Instruction::Ixor);
                self.frame.pop_type_n(2);
                self.frame.push_type(VerificationType::Integer);
            }
            return Ok(JvmType::Int);
        }

        // Bool equality: use integer comparison (bools are JvmType::Int)
        if operand_jvm == JvmType::Int && matches!(op, BinOp::Eq | BinOp::Neq) {
            self.compile_expr(lhs, false)?;
            self.compile_expr(rhs, false)?;
            // XOR gives 0 if equal, 1 if different
            self.emit(Instruction::Ixor);
            self.frame.pop_type_n(2);
            self.frame.push_type(VerificationType::Integer);
            if matches!(op, BinOp::Eq) {
                // Negate: XOR with 1 (0→1, 1→0)
                self.emit(Instruction::Iconst_1);
                self.frame.push_type(VerificationType::Integer);
                self.emit(Instruction::Ixor);
                self.frame.pop_type_n(2);
                self.frame.push_type(VerificationType::Integer);
            }
            return Ok(JvmType::Int);
        }

        // User-type trait dispatch for Eq/Ord
        if !matches!(operand_jvm, JvmType::Long | JvmType::Double) {
            let (trait_name, method_name, swap, negate) = match op {
                BinOp::Eq => ("Eq", "eq", false, false),
                BinOp::Neq => ("Eq", "eq", false, true),
                BinOp::Lt => ("Ord", "lt", false, false),
                BinOp::Gt => ("Ord", "lt", true, false),
                BinOp::Le => ("Ord", "lt", true, true),
                BinOp::Ge => ("Ord", "lt", false, true),
                _ => unreachable!(),
            };
            let (lhs_arg, rhs_arg) = if swap { (rhs, lhs) } else { (lhs, rhs) };
            self.compile_trait_binop(trait_name, method_name, lhs_arg, rhs_arg, JvmType::Int)?;
            if negate {
                self.emit(Instruction::Iconst_1);
                self.frame.push_type(VerificationType::Integer);
                self.emit(Instruction::Ixor);
                self.frame.pop_type_n(2);
                self.frame.push_type(VerificationType::Integer);
            }
            return Ok(JvmType::Int);
        }

        // Primitive numeric comparison (Long/Double)
        self.compile_expr(lhs, false)?;
        self.compile_expr(rhs, false)?;

        let cmp_instr = match operand_jvm {
            JvmType::Long => Instruction::Lcmp,
            JvmType::Double => Instruction::Dcmpl,
            _ => unreachable!(),
        };
        self.emit(cmp_instr);

        // Lcmp/Dcmpl: pop two 2-slot values (4 slots), push int
        self.frame.pop_type_n(4);
        self.frame.push_type(VerificationType::Integer);

        // Materialize boolean (0/1) using branch-if-NOT pattern.
        // Ristretto uses logical instruction indices for branch targets.
        //
        // Layout (instruction indices relative to branch_idx):
        //   [branch_idx]   Ifxx(branch_idx + 3)  → jumps to Iconst_0
        //   [branch_idx+1] Iconst_1
        //   [branch_idx+2] Goto(branch_idx + 4)   → jumps past Iconst_0
        //   [branch_idx+3] Iconst_0
        //   [branch_idx+4] (next instruction)

        let branch_idx = self.code.len() as u16;
        let false_target = branch_idx + 3;
        let after_target = branch_idx + 4;

        let branch = match op {
            BinOp::Eq => Instruction::Ifne(false_target),
            BinOp::Neq => Instruction::Ifeq(false_target),
            BinOp::Lt => Instruction::Ifge(false_target),
            BinOp::Gt => Instruction::Ifle(false_target),
            BinOp::Le => Instruction::Ifgt(false_target),
            BinOp::Ge => Instruction::Iflt(false_target),
            _ => unreachable!(),
        };
        self.emit(branch);

        // Ifxx consumes the int
        self.frame.pop_type();

        // Record frame at false_target (stack state after Ifxx consumes int)
        let stack_at_false = self.frame.stack_types.clone();
        self.frame.record_frame(false_target);

        // True path: push 1
        self.emit(Instruction::Iconst_1);
        self.frame.push_type(VerificationType::Integer);

        // Record frame at after_target (stack has Integer on top)
        self.frame.record_frame(after_target);
        let stack_after = self.frame.stack_types.clone();

        self.emit(Instruction::Goto(after_target));

        // False path: restore stack to state at false_target
        self.frame.stack_types = stack_at_false;
        self.emit(Instruction::Iconst_0);
        self.frame.push_type(VerificationType::Integer);

        // After both paths merge, stack should match
        debug_assert_eq!(self.frame.stack_types, stack_after);

        Ok(JvmType::Int)
    }

    fn compile_unaryop(
        &mut self,
        op: &UnaryOp,
        operand: &TypedExpr,
    ) -> Result<JvmType, CodegenError> {
        let operand_jvm = self.type_to_jvm(&operand.ty)?;
        match op {
            UnaryOp::Neg => match operand_jvm {
                JvmType::Long => {
                    self.compile_expr(operand, false)?;
                    self.emit(Instruction::Lneg);
                    Ok(JvmType::Long)
                }
                JvmType::Double => {
                    self.compile_expr(operand, false)?;
                    self.emit(Instruction::Dneg);
                    Ok(JvmType::Double)
                }
                _ => self.compile_trait_unaryop("Neg", "neg", operand, operand_jvm),
            },
            UnaryOp::Not => {
                // Boolean NOT: XOR with 1
                self.compile_expr(operand, false)?;
                self.emit(Instruction::Iconst_1);
                self.frame.push_type(VerificationType::Integer);
                self.emit(Instruction::Ixor);
                self.frame.pop_type();
                Ok(JvmType::Int)
            }
        }
    }

    fn compile_if(
        &mut self,
        cond: &TypedExpr,
        then_: &TypedExpr,
        else_: &TypedExpr,
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // Compile condition (produces Int 0/1 on stack)
        self.compile_expr(cond, false)?;

        // Ifeq consumes the int
        self.frame.pop_type();

        // Emit Ifeq with placeholder — will be patched with instruction index
        let ifeq_idx = self.code.len();
        self.emit(Instruction::Ifeq(0)); // placeholder

        // Save stack state at branch point (after consuming condition)
        let stack_at_branch = self.frame.stack_types.clone();
        let locals_at_branch = self.locals.clone();
        let local_types_at_branch = self.frame.local_types.clone();
        let next_local_at_branch = self.next_local;

        // Compile then branch
        let then_type = self.compile_expr(then_, in_tail)?;
        let stack_after_then = self.frame.stack_types.clone();
        let then_next_local = self.next_local;

        // Restore locals for else branch (then-branch locals are out of scope)
        self.locals = locals_at_branch.clone();
        self.frame.local_types = local_types_at_branch.clone();
        self.next_local = next_local_at_branch;

        // Emit Goto with placeholder
        let goto_idx = self.code.len();
        self.emit(Instruction::Goto(0)); // placeholder

        // else starts at this instruction index
        let else_start = self.code.len() as u16;

        // Record frame at else_start with stack state from branch point
        self.frame.stack_types = stack_at_branch;
        self.frame.record_frame(else_start);

        // Compile else branch
        let _else_type = self.compile_expr(else_, in_tail)?;
        let else_next_local = self.next_local;

        // Restore locals for merge point (else-branch locals are out of scope)
        self.locals = locals_at_branch;
        self.frame.local_types = local_types_at_branch;
        self.next_local = then_next_local.max(else_next_local);

        let after_else = self.code.len() as u16;

        // Record frame at after_else
        self.frame.record_frame(after_else);

        debug_assert_eq!(self.frame.stack_types, stack_after_then);

        // Patch: Ifeq should jump to else_start instruction index
        self.code[ifeq_idx] = Instruction::Ifeq(else_start);
        // Patch: Goto should jump past else
        self.code[goto_idx] = Instruction::Goto(after_else);

        Ok(then_type)
    }

    fn compile_let(
        &mut self,
        name: &str,
        value: &TypedExpr,
        body: &Option<Box<TypedExpr>>,
        in_tail: bool,
        span: krypton_parser::ast::Span,
    ) -> Result<JvmType, CodegenError> {
        // Function-typed bindings need local_fn_info so later `f(args)` calls can
        // unbox/cast the invokeinterface result correctly.
        let is_fn_value = matches!(value.kind, TypedExprKind::Lambda { .. })
            || matches!(
                match &value.ty {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                },
                Type::Fn(_, _)
            );

        // Emit shadow close for old binding before compiling new value
        // (shadow close happens after new value is on stack but before store)
        let shadow_close = self.auto_close.shadow_closes.get(&span).cloned();

        let ty = self.compile_expr(value, false)?;

        // Emit shadow close after evaluating value but before storing
        if let Some(binding) = shadow_close {
            // Save the new value to a temp slot to preserve it while we close the old binding
            let temp_slot = self.next_local;
            self.next_local += 1;
            let temp_store = match ty {
                JvmType::Long | JvmType::Double => unreachable!("resource is always ref"),
                JvmType::Int => Instruction::Istore(temp_slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Astore(temp_slot as u8),
            };
            self.emit(temp_store.clone());
            self.pop_jvm_type(ty);
            let vtypes = self.jvm_type_to_vtypes(ty);
            self.frame.local_types.extend(vtypes);

            self.emit_auto_close(&binding)?;

            // Reload the new value
            let temp_load = match ty {
                JvmType::Long | JvmType::Double => unreachable!("resource is always ref"),
                JvmType::Int => Instruction::Iload(temp_slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(temp_slot as u8),
            };
            self.emit(temp_load);
            self.push_jvm_type(ty);
        }

        let slot = self.next_local;
        let slot_size = match ty {
            JvmType::Long | JvmType::Double => 2,
            _ => 1,
        };
        self.next_local += slot_size;

        let store = match ty {
            JvmType::Long => Instruction::Lstore(slot as u8),
            JvmType::Double => Instruction::Dstore(slot as u8),
            JvmType::Int => Instruction::Istore(slot as u8),
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Astore(slot as u8),
        };
        self.emit(store);
        self.locals.insert(name.to_string(), (slot, ty));

        // If the value is function-typed, record local_fn_info from the TypedExpr's type.
        if is_fn_value {
            let fn_type = match &value.ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            if let Type::Fn(param_types, ret_type) = fn_type {
                let param_jvm: Result<Vec<JvmType>, _> =
                    param_types.iter().map(|t| self.type_to_jvm(t)).collect();
                if let Ok(param_jvm) = param_jvm {
                    if let Ok(ret_jvm) = self.type_to_jvm(ret_type) {
                        self.local_fn_info
                            .insert(name.to_string(), (param_jvm, ret_jvm));
                    }
                }
            }
        }

        // Pop value from stack tracker
        self.pop_jvm_type(ty);

        // Extend local_types with verification type(s)
        let vtypes = self.jvm_type_to_vtypes(ty);
        self.frame.local_types.extend(vtypes);

        if let Some(body) = body {
            self.compile_expr(body, in_tail)
        } else {
            self.emit(Instruction::Iconst_0);
            self.frame.push_type(VerificationType::Integer);
            Ok(JvmType::Int)
        }
    }

    fn compile_tuple(&mut self, elems: &[TypedExpr], _ty: &Type) -> Result<JvmType, CodegenError> {
        let arity = elems.len();
        let info = self
            .types
            .tuple_info
            .get(&arity)
            .ok_or_else(|| CodegenError::TypeError(format!("unknown tuple arity: {arity}")))?;
        let class_index = info.class_index;
        let constructor_ref = info.constructor_ref;

        // new TupleN + dup
        self.emit(Instruction::New(class_index));
        self.frame.push_type(VerificationType::UninitializedThis);
        self.emit(Instruction::Dup);
        self.frame.push_type(VerificationType::UninitializedThis);

        // Compile each element and box if primitive
        for elem in elems {
            let elem_type = self.compile_expr(elem, false)?;
            self.box_if_needed(elem_type);
        }

        // Pop args (all Object after boxing) + 2 uninit refs
        for _ in 0..arity {
            self.frame.pop_type(); // each boxed Object
        }
        self.frame.pop_type(); // dup'd uninit
        self.frame.pop_type(); // original uninit

        // invokespecial TupleN.<init>
        self.emit(Instruction::Invokespecial(constructor_ref));
        let result_type = JvmType::StructRef(class_index);
        self.push_jvm_type(result_type);

        Ok(result_type)
    }

    fn emit_int_const(&mut self, n: i32) {
        match n {
            0 => self.emit(Instruction::Iconst_0),
            1 => self.emit(Instruction::Iconst_1),
            2 => self.emit(Instruction::Iconst_2),
            3 => self.emit(Instruction::Iconst_3),
            4 => self.emit(Instruction::Iconst_4),
            5 => self.emit(Instruction::Iconst_5),
            _ => {
                let idx = self
                    .cp
                    .add_integer(n)
                    .expect("failed to add integer constant");
                if idx <= 255 {
                    self.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.emit(Instruction::Ldc_w(idx));
                }
            }
        }
    }

    fn compile_vec_lit(&mut self, elems: &[TypedExpr]) -> Result<JvmType, CodegenError> {
        let info = self
            .vec_info
            .as_ref()
            .ok_or_else(|| CodegenError::TypeError("Vec info not registered".to_string()))?
            .clone();

        let arr_vtype = VerificationType::Object {
            cpool_index: info.class_index,
        };

        // new KryptonArray(capacity)
        self.emit(Instruction::New(info.class_index));
        self.frame.push_type(VerificationType::UninitializedThis);
        self.emit(Instruction::Dup);
        self.frame.push_type(VerificationType::UninitializedThis);
        self.emit_int_const(elems.len() as i32);
        self.frame.push_type(VerificationType::Integer);
        self.emit(Instruction::Invokespecial(info.init_ref));
        self.frame.pop_type(); // int
        self.frame.pop_type(); // uninit dup
        self.frame.pop_type(); // uninit orig
        self.frame.push_type(arr_vtype.clone());
        // stack: [arr]

        for (i, elem) in elems.iter().enumerate() {
            self.emit(Instruction::Dup);
            self.frame.push_type(arr_vtype.clone());
            // stack: [arr, arr]
            self.emit_int_const(i as i32);
            self.frame.push_type(VerificationType::Integer);
            let elem_type = self.compile_expr(elem, false)?;
            self.box_if_needed(elem_type);
            // stack: [arr, arr, index, boxed_elem]
            self.emit(Instruction::Invokevirtual(info.set_ref));
            self.frame.pop_type(); // boxed_elem
            self.frame.pop_type(); // index
            self.frame.pop_type(); // arr (dup'd)
                                   // stack: [arr]
        }

        // freeze
        self.emit(Instruction::Dup);
        self.frame.push_type(arr_vtype.clone());
        self.emit(Instruction::Invokevirtual(info.freeze_ref));
        self.frame.pop_type(); // arr (dup'd, consumed by freeze)
                               // stack: [arr]

        Ok(JvmType::StructRef(info.class_index))
    }

    fn compile_let_pattern(
        &mut self,
        pattern: &TypedPattern,
        value: &TypedExpr,
        body: &Option<Box<TypedExpr>>,
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // Only support irrefutable patterns (Tuple, Var, Wildcard)
        if let TypedPattern::Constructor { .. } = pattern {
            return Err(CodegenError::UnsupportedExpr(
                "refutable let-pattern (constructor) not yet supported".into(),
            ));
        }

        // Compile the value expression
        let val_type = self.compile_expr(value, false)?;

        // Store in a temp local (the scrutinee)
        let scrutinee_slot = self.next_local;
        self.next_local += 1;
        self.emit(Instruction::Astore(scrutinee_slot as u8));
        self.pop_jvm_type(val_type);
        let vtypes = self.jvm_type_to_vtypes(val_type);
        self.frame.local_types.extend(vtypes);

        // Bind the pattern
        self.bind_irrefutable_pattern(pattern, scrutinee_slot, val_type, &value.ty)?;

        // Compile the body if present
        if let Some(body) = body {
            self.compile_expr(body, in_tail)
        } else {
            self.emit(Instruction::Iconst_0);
            self.frame.push_type(VerificationType::Integer);
            Ok(JvmType::Int)
        }
    }

    /// Bind an irrefutable pattern (Tuple, Var, Wildcard) — used by let-pattern destructuring.
    fn bind_irrefutable_pattern(
        &mut self,
        pattern: &TypedPattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
        value_ty: &Type,
    ) -> Result<(), CodegenError> {
        match pattern {
            TypedPattern::Wildcard { .. } => Ok(()),
            TypedPattern::Var { name, .. } => {
                // Load scrutinee and store in a named local
                let load = match scrutinee_type {
                    JvmType::Long => Instruction::Lload(scrutinee_slot as u8),
                    JvmType::Double => Instruction::Dload(scrutinee_slot as u8),
                    JvmType::Int => Instruction::Iload(scrutinee_slot as u8),
                    JvmType::Ref | JvmType::StructRef(_) => {
                        Instruction::Aload(scrutinee_slot as u8)
                    }
                };
                self.emit(load);
                self.push_jvm_type(scrutinee_type);

                let var_slot = self.next_local;
                let slot_size: u16 = match scrutinee_type {
                    JvmType::Long | JvmType::Double => 2,
                    _ => 1,
                };
                self.next_local += slot_size;
                let store = match scrutinee_type {
                    JvmType::Long => Instruction::Lstore(var_slot as u8),
                    JvmType::Double => Instruction::Dstore(var_slot as u8),
                    JvmType::Int => Instruction::Istore(var_slot as u8),
                    JvmType::Ref | JvmType::StructRef(_) => Instruction::Astore(var_slot as u8),
                };
                self.emit(store);
                self.pop_jvm_type(scrutinee_type);
                let vtypes = self.jvm_type_to_vtypes(scrutinee_type);
                self.frame.local_types.extend(vtypes);
                self.locals.insert(name.clone(), (var_slot, scrutinee_type));
                Ok(())
            }
            TypedPattern::Tuple { elements, .. } => {
                let elem_types = match value_ty {
                    Type::Tuple(elems) => elems,
                    _ => {
                        return Err(CodegenError::TypeError(
                            "expected tuple type for tuple pattern".into(),
                        ))
                    }
                };
                let arity = elements.len();
                let tuple_info = self.types.tuple_info.get(&arity).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown tuple arity: {arity}"))
                })?;
                let tuple_class = tuple_info.class_index;
                let field_refs: Vec<u16> = tuple_info.field_refs.clone();

                for (i, sub_pat) in elements.iter().enumerate() {
                    if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                        continue;
                    }
                    let field_ref = field_refs[i];
                    let elem_ty = &elem_types[i];
                    let elem_jvm_type = self.type_to_jvm(elem_ty)?;

                    // Load tuple, invoke accessor _i() -> Object
                    self.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: tuple_class,
                    });
                    self.emit(Instruction::Invokevirtual(field_ref));
                    self.frame.pop_type(); // pop tuple ref
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: self.refs.object_class,
                    });

                    // Unbox if primitive, checkcast if struct/string ref
                    match elem_jvm_type {
                        JvmType::StructRef(idx) => {
                            self.emit(Instruction::Checkcast(idx));
                            self.frame.pop_type();
                            self.frame
                                .push_type(VerificationType::Object { cpool_index: idx });
                        }
                        JvmType::Ref => {
                            self.emit(Instruction::Checkcast(self.refs.string_class));
                            self.frame.pop_type();
                            self.frame.push_type(VerificationType::Object {
                                cpool_index: self.refs.string_class,
                            });
                        }
                        _ => self.unbox_if_needed(elem_jvm_type),
                    }

                    // For nested tuple or var, store and recurse
                    match sub_pat {
                        TypedPattern::Var { name: var_name, .. } => {
                            let var_slot = self.next_local;
                            let slot_size: u16 = match elem_jvm_type {
                                JvmType::Long | JvmType::Double => 2,
                                _ => 1,
                            };
                            self.next_local += slot_size;
                            let store = match elem_jvm_type {
                                JvmType::Long => Instruction::Lstore(var_slot as u8),
                                JvmType::Double => Instruction::Dstore(var_slot as u8),
                                JvmType::Int => Instruction::Istore(var_slot as u8),
                                JvmType::Ref | JvmType::StructRef(_) => {
                                    Instruction::Astore(var_slot as u8)
                                }
                            };
                            self.emit(store);
                            self.pop_jvm_type(elem_jvm_type);
                            let vtypes = self.jvm_type_to_vtypes(elem_jvm_type);
                            self.frame.local_types.extend(vtypes);
                            self.locals
                                .insert(var_name.clone(), (var_slot, elem_jvm_type));
                        }
                        TypedPattern::Tuple { .. } => {
                            // Store in temp local and recurse
                            let nested_slot = self.next_local;
                            self.next_local += 1;
                            self.emit(Instruction::Astore(nested_slot as u8));
                            self.frame.pop_type();
                            self.frame.local_types.push(VerificationType::Object {
                                cpool_index: match elem_jvm_type {
                                    JvmType::StructRef(idx) => idx,
                                    _ => self.refs.object_class,
                                },
                            });
                            self.bind_irrefutable_pattern(
                                sub_pat,
                                nested_slot,
                                elem_jvm_type,
                                elem_ty,
                            )?;
                        }
                        TypedPattern::Wildcard { .. } => {
                            // Already filtered above, but handle gracefully
                            self.frame.pop_type();
                            self.emit(Instruction::Pop);
                        }
                        _ => {
                            return Err(CodegenError::UnsupportedExpr(
                                "unsupported sub-pattern in tuple destructuring".into(),
                            ));
                        }
                    }
                }
                Ok(())
            }
            _ => Err(CodegenError::UnsupportedExpr(format!(
                "unsupported pattern in let: {pattern:?}"
            ))),
        }
    }

    fn load_bridge_arg(&mut self, slot: u16, actual_type: JvmType) {
        self.emit(Instruction::Aload(slot as u8));
        self.frame.push_type(VerificationType::Object {
            cpool_index: self.refs.object_class,
        });
        match actual_type {
            JvmType::Long | JvmType::Double | JvmType::Int => self.unbox_if_needed(actual_type),
            JvmType::Ref => {
                self.emit(Instruction::Checkcast(self.refs.string_class));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.string_class,
                });
            }
            JvmType::StructRef(idx) if idx != self.refs.object_class => {
                self.emit(Instruction::Checkcast(idx));
                self.frame.pop_type();
                self.frame
                    .push_type(VerificationType::Object { cpool_index: idx });
            }
            JvmType::StructRef(_) => {}
        }
    }

    fn emit_fun_reference_indy(
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

        let fun_class_name = format!("Fun{arity}");
        let mut callsite_desc = String::from("(");
        for _ in 0..capture_count {
            callsite_desc.push_str("Ljava/lang/Object;");
        }
        callsite_desc.push_str(&format!(")L{fun_class_name};"));
        let indy_idx = self
            .cp
            .add_invoke_dynamic(bsm_index, "apply", &callsite_desc)?;

        self.emit(Instruction::Invokedynamic(indy_idx));
        for _ in 0..capture_count {
            self.frame.pop_type();
        }
        let result_type = JvmType::StructRef(fun_class_idx);
        self.push_jvm_type(result_type);
        Ok(result_type)
    }

    fn compile_fn_ref(&mut self, name: &str, expr_ty: &Type) -> Result<JvmType, CodegenError> {
        let fn_type = match expr_ty {
            Type::Own(inner) => inner.as_ref(),
            other => other,
        };
        let (param_types, ret_type) = match fn_type {
            Type::Fn(param_types, ret_type) => (param_types, ret_type),
            other => {
                return Err(CodegenError::TypeError(format!(
                    "function reference has non-function type: {other}"
                )))
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

        let dict_requirements = if let Some(requirements) =
            self.traits.impl_dict_requirements.get(name)
        {
            requirements.clone()
        } else {
            self.traits
                .fn_constraints
                .get(name)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .map(|(trait_name, param_idx)| DictRequirement::TypeParam {
                    trait_name,
                    param_idx,
                })
                .collect::<Vec<_>>()
        };

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

        let saved_code = std::mem::take(&mut self.code);
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_local_types = std::mem::take(&mut self.frame.local_types);
        let saved_next_local = self.next_local;
        let saved_stack_types = std::mem::take(&mut self.frame.stack_types);
        let saved_frames = std::mem::take(&mut self.frame.frames);
        let saved_max_stack_depth = self.frame.max_stack_depth;
        let saved_fn_params = std::mem::take(&mut self.fn_params);
        let saved_fn_return_type = self.fn_return_type.take();
        let saved_local_fn_info = std::mem::take(&mut self.local_fn_info);

        self.code.clear();
        self.locals.clear();
        self.frame.local_types.clear();
        self.next_local = (dict_requirements.len() + param_jvm_types.len()) as u16;
        self.frame.stack_types.clear();
        self.frame.frames.clear();
        self.frame.max_stack_depth = 0;
        self.fn_params.clear();
        self.fn_return_type = None;

        for _ in &dict_requirements {
            self.frame.local_types.push(VerificationType::Object {
                cpool_index: self.refs.object_class,
            });
        }
        for _ in &param_jvm_types {
            self.frame.local_types.push(VerificationType::Object {
                cpool_index: self.refs.object_class,
            });
        }

        if let Some(info) = self.types.functions.get(name) {
            let param_types = info.param_types.clone();
            let return_type = info.return_type;
            let is_void = info.is_void;
            let method_ref = info.method_ref;

            if param_types.len() != dict_requirements.len() + param_jvm_types.len() {
                return Err(CodegenError::UnsupportedExpr(format!(
                    "function reference `{name}` has mismatched parameter metadata"
                )));
            }

            let mut bridge_slot = 0u16;
            for _ in &dict_requirements {
                self.emit(Instruction::Aload(bridge_slot as u8));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });
                bridge_slot += 1;
            }

            for (i, actual_type) in param_jvm_types.iter().copied().enumerate() {
                self.load_bridge_arg(bridge_slot, actual_type);
                let expected_type = param_types[dict_requirements.len() + i];
                if let JvmType::StructRef(idx) = expected_type {
                    if idx == self.refs.object_class
                        && !matches!(actual_type, JvmType::StructRef(_) | JvmType::Ref)
                    {
                        self.box_if_needed(actual_type);
                    }
                }
                bridge_slot += 1;
            }

            self.emit(Instruction::Invokestatic(method_ref));
            for actual_type in param_types.iter().rev().copied() {
                self.pop_jvm_type(actual_type);
            }
            if is_void {
                self.emit(Instruction::Iconst_0);
                self.frame.push_type(VerificationType::Integer);
            } else {
                self.push_jvm_type(return_type);
                match ret_jvm {
                    JvmType::Long | JvmType::Double | JvmType::Int
                        if matches!(return_type, JvmType::StructRef(idx) if idx == self.refs.object_class) =>
                    {
                        self.unbox_if_needed(ret_jvm);
                    }
                    JvmType::Ref
                        if matches!(return_type, JvmType::StructRef(idx) if idx == self.refs.object_class) =>
                    {
                        self.emit(Instruction::Checkcast(self.refs.string_class));
                        self.frame.pop_type();
                        self.frame.push_type(VerificationType::Object {
                            cpool_index: self.refs.string_class,
                        });
                    }
                    JvmType::StructRef(idx)
                        if idx != self.refs.object_class
                            && matches!(return_type, JvmType::StructRef(ret_idx) if ret_idx == self.refs.object_class) =>
                    {
                        self.emit(Instruction::Checkcast(idx));
                        self.frame.pop_type();
                        self.frame
                            .push_type(VerificationType::Object { cpool_index: idx });
                    }
                    _ => {}
                }
            }
        } else if let Some(si) = self.types.struct_info.get(name) {
            let class_index = si.class_index;
            let constructor_ref = si.constructor_ref;
            let field_types: Vec<JvmType> = si.fields.iter().map(|(_, ty)| *ty).collect();

            self.emit(Instruction::New(class_index));
            self.frame.push_type(VerificationType::UninitializedThis);
            self.emit(Instruction::Dup);
            self.frame.push_type(VerificationType::UninitializedThis);

            for (i, actual_type) in field_types.iter().copied().enumerate() {
                self.load_bridge_arg(i as u16, actual_type);
            }

            self.emit(Instruction::Invokespecial(constructor_ref));
            for actual_type in field_types.iter().rev().copied() {
                self.pop_jvm_type(actual_type);
            }
            self.frame.pop_type();
            self.frame.pop_type();
            self.push_jvm_type(JvmType::StructRef(class_index));
        } else if let Some(sum_name) = self.types.variant_to_sum.get(name).cloned() {
            let sum_info = &self.types.sum_type_info[&sum_name];
            let variant = &sum_info.variants[name];
            let class_index = variant.class_index;
            let constructor_ref = variant.constructor_ref;
            let interface_class_index = sum_info.interface_class_index;
            let fields = variant.fields.clone();

            self.emit(Instruction::New(class_index));
            self.frame.push_type(VerificationType::UninitializedThis);
            self.emit(Instruction::Dup);
            self.frame.push_type(VerificationType::UninitializedThis);

            for (i, ((_field_name, field_type, is_erased), actual_type)) in
                fields.iter().zip(param_jvm_types.iter().copied()).enumerate()
            {
                self.load_bridge_arg(i as u16, actual_type);
                if *is_erased {
                    self.box_if_needed(actual_type);
                } else if *field_type != actual_type {
                    return Err(CodegenError::TypeError(format!(
                        "variant reference `{name}` expected bridge arg type {field_type:?}, got {actual_type:?}"
                    )));
                }
            }

            self.emit(Instruction::Invokespecial(constructor_ref));
            for (_field_name, actual_type, is_erased) in fields.iter().rev() {
                if *is_erased {
                    self.frame.pop_type();
                } else {
                    self.pop_jvm_type(*actual_type);
                }
            }
            self.frame.pop_type();
            self.frame.pop_type();
            self.push_jvm_type(JvmType::StructRef(interface_class_index));
        } else {
            return Err(CodegenError::UndefinedVariable(name.to_string()));
        }

        let bridge_result = self.box_if_needed(ret_jvm);
        debug_assert!(matches!(bridge_result, JvmType::Ref | JvmType::StructRef(_)));
        self.emit(Instruction::Areturn);

        let bridge_name_idx = self.cp.add_utf8(&bridge_name)?;
        let bridge_desc_idx = self.cp.add_utf8(&bridge_desc)?;
        let stack_map_frames = self.frame.build_stack_map_frames();
        let code_attributes = if stack_map_frames.is_empty() {
            vec![]
        } else {
            vec![Attribute::StackMapTable {
                name_index: self.refs.smt_name,
                frames: stack_map_frames,
            }]
        };
        self.lambda.lambda_methods.push(Method {
            access_flags: MethodAccessFlags::PRIVATE
                | MethodAccessFlags::STATIC
                | MethodAccessFlags::SYNTHETIC,
            name_index: bridge_name_idx,
            descriptor_index: bridge_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: self.refs.code_utf8,
                max_stack: self.frame.max_stack(),
                max_locals: self.next_local,
                code: std::mem::take(&mut self.code),
                exception_table: vec![],
                attributes: code_attributes,
            }],
        });

        self.code = saved_code;
        self.locals = saved_locals;
        self.frame.local_types = saved_local_types;
        self.next_local = saved_next_local;
        self.frame.stack_types = saved_stack_types;
        self.frame.frames = saved_frames;
        self.frame.max_stack_depth = saved_max_stack_depth;
        self.fn_params = saved_fn_params;
        self.fn_return_type = saved_fn_return_type;
        self.local_fn_info = saved_local_fn_info;

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
                    ))
                })?;
                self.emit_dict_argument_for_type(
                    requirement.trait_name(),
                    &requirement_ty,
                    self.refs.object_class,
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

    fn compile_var(&mut self, name: &str) -> Result<JvmType, CodegenError> {
        // Check if this is a nullary variant constructor
        if let Some(sum_name) = self.types.variant_to_sum.get(name).cloned() {
            let sum_info = &self.types.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            if vi.fields.is_empty() {
                let singleton_field_ref = vi.singleton_field_ref.unwrap();
                let interface_class_index = sum_info.interface_class_index;
                self.emit(Instruction::Getstatic(singleton_field_ref));
                let result_type = JvmType::StructRef(interface_class_index);
                self.push_jvm_type(result_type);
                return Ok(result_type);
            }
        }

        let (slot, ty) = self
            .locals
            .get(name)
            .copied()
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;

        let load = match ty {
            JvmType::Long => Instruction::Lload(slot as u8),
            JvmType::Double => Instruction::Dload(slot as u8),
            JvmType::Int => Instruction::Iload(slot as u8),
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(slot as u8),
        };
        self.emit(load);

        // Push the verification type(s)
        self.push_jvm_type(ty);

        Ok(ty)
    }

    fn compile_intrinsic(
        &mut self,
        name: &str,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        match name {
            "panic" => {
                let re_class = self.refs.runtime_exception_class;
                let re_init = self.refs.runtime_exception_init;
                self.emit(Instruction::New(re_class));
                self.frame.push_type(VerificationType::UninitializedThis);
                self.emit(Instruction::Dup);
                self.frame.push_type(VerificationType::UninitializedThis);
                // Compile the String argument
                self.compile_expr(&args[0], false)?;
                // invokespecial RuntimeException.<init>(String)V
                self.emit(Instruction::Invokespecial(re_init));
                self.frame.pop_type(); // string arg
                self.frame.pop_type(); // dup'd uninit
                self.frame.pop_type(); // original uninit
                self.emit(Instruction::Athrow);
                // Push the expected return type onto the frame for verification
                let jvm_ret = self.type_to_jvm(result_ty)?;
                self.push_jvm_type(jvm_ret);
                Ok(jvm_ret)
            }
            _ => Err(CodegenError::UnsupportedExpr(format!(
                "unknown intrinsic: {name}"
            ))),
        }
    }

    fn compile_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        let name = match &func.kind {
            TypedExprKind::Var(name) => name.as_str(),
            TypedExprKind::TypeApp { expr } => match &expr.kind {
                TypedExprKind::Var(name) => name.as_str(),
                other => {
                    return Err(CodegenError::UnsupportedExpr(format!(
                        "non-variable function call: {other:?}"
                    )))
                }
            },
            other => {
                return Err(CodegenError::UnsupportedExpr(format!(
                    "non-variable function call: {other:?}"
                )))
            }
        };

        // Check if this is an intrinsic function call
        if is_intrinsic(name) {
            return self.compile_intrinsic(name, args, result_ty);
        }

        // Check if this is a struct constructor call
        if let Some(si) = self.types.struct_info.get(name) {
            let class_index = si.class_index;
            let constructor_ref = si.constructor_ref;
            let result_type = JvmType::StructRef(class_index);

            self.emit(Instruction::New(class_index));
            self.frame.push_type(VerificationType::UninitializedThis);
            self.emit(Instruction::Dup);
            self.frame.push_type(VerificationType::UninitializedThis);

            for arg in args {
                self.compile_expr(arg, false)?;
            }

            // Pop args + 2 uninit refs, push one StructRef
            let fields = self.types.struct_info[name].fields.clone();
            for (_, ft) in &fields {
                self.pop_jvm_type(*ft);
            }
            self.frame.pop_type(); // dup'd uninit
            self.frame.pop_type(); // original uninit

            self.emit(Instruction::Invokespecial(constructor_ref));
            self.push_jvm_type(result_type);

            return Ok(result_type);
        }

        // Check if this is a variant constructor call
        if let Some(sum_name) = self.types.variant_to_sum.get(name).cloned() {
            let sum_info = &self.types.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            let class_index = vi.class_index;
            let constructor_ref = vi.constructor_ref;
            let interface_class_index = sum_info.interface_class_index;
            let fields: Vec<(String, JvmType, bool)> = vi.fields.clone();
            let result_type = JvmType::StructRef(interface_class_index);

            self.emit(Instruction::New(class_index));
            self.frame.push_type(VerificationType::UninitializedThis);
            self.emit(Instruction::Dup);
            self.frame.push_type(VerificationType::UninitializedThis);

            for (i, arg) in args.iter().enumerate() {
                let arg_type = self.compile_expr(arg, false)?;
                let (_fname, _field_jvm_type, is_erased) = &fields[i];
                if *is_erased {
                    self.box_if_needed(arg_type);
                }
            }

            // Pop args + 2 uninit refs, push one StructRef
            for (_, ft, is_erased) in &fields {
                if *is_erased {
                    self.frame.pop_type(); // Object ref
                } else {
                    self.pop_jvm_type(*ft);
                }
            }
            self.frame.pop_type(); // dup'd uninit
            self.frame.pop_type(); // original uninit

            self.emit(Instruction::Invokespecial(constructor_ref));
            self.push_jvm_type(result_type);

            return Ok(result_type);
        }

        // Check if this is a higher-order call (calling a local variable holding a lambda)
        if let Some(&(slot, jvm_ty)) = self.locals.get(name) {
            if let Some((_ho_param_types, ho_ret_type)) = self.local_fn_info.get(name).cloned() {
                let arity = args.len() as u8;
                // Load the function object
                self.emit(Instruction::Aload(slot as u8));
                self.push_jvm_type(jvm_ty);
                // Compile and box each argument
                for arg in args {
                    let arg_type = self.compile_expr(arg, false)?;
                    self.box_if_needed(arg_type);
                }
                // invokeinterface FunN.apply
                let apply_ref = self.lambda.fun_apply_refs[&arity];
                self.emit(Instruction::Invokeinterface(apply_ref, arity + 1));
                // Pop args + receiver
                for _ in 0..arity {
                    self.frame.pop_type(); // each boxed arg
                }
                self.pop_jvm_type(jvm_ty); // receiver
                                           // Push Object result
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });
                // Unbox if needed
                self.unbox_if_needed(ho_ret_type);
                // Checkcast Object → specific ref type if needed
                match ho_ret_type {
                    JvmType::Ref => {
                        self.emit(Instruction::Checkcast(self.refs.string_class));
                        self.frame.pop_type();
                        self.frame.push_type(VerificationType::Object {
                            cpool_index: self.refs.string_class,
                        });
                    }
                    JvmType::StructRef(idx) if idx != self.refs.object_class => {
                        self.emit(Instruction::Checkcast(idx));
                        self.frame.pop_type();
                        self.frame
                            .push_type(VerificationType::Object { cpool_index: idx });
                    }
                    _ => {}
                }
                return Ok(ho_ret_type);
            }
        }

        if let Some(trait_name) = self.traits.trait_method_map.get(name).cloned() {
            if let Some(dispatch) = self.traits.trait_dispatch.get(&trait_name) {
                let iface_method_ref = dispatch.method_refs[name];
                let iface_class = dispatch.interface_class;

                // Determine the concrete type for dictionary selection.
                // For zero-arg trait methods, extract from the return type instead.
                let dict_ty = if args.is_empty() {
                    match &func.ty {
                        Type::Fn(_, ret) => ret.as_ref().clone(),
                        _ => result_ty.clone(),
                    }
                } else {
                    args[0].ty.clone()
                };
                let is_type_var = matches!(&dict_ty, Type::Var(_));

                // Load the dictionary (trait interface reference)
                if is_type_var && !self.traits.dict_locals.contains_key(&trait_name) {
                    return Err(CodegenError::UndefinedVariable(format!(
                        "no dict local for trait {trait_name}"
                    )));
                }
                self.emit_dict_argument_for_type(&trait_name, &dict_ty, iface_class)?;

                // Compile and box all arguments
                let arity = args.len();
                for arg in args {
                    let arg_type = self.compile_expr(arg, false)?;
                    self.box_if_needed(arg_type);
                }

                // invokeinterface
                self.emit(Instruction::Invokeinterface(
                    iface_method_ref,
                    (arity + 1) as u8,
                ));

                // Pop args + receiver from stack tracker
                for _ in 0..arity {
                    self.frame.pop_type(); // each boxed arg
                }
                self.frame.pop_type(); // receiver (dict)

                // Push Object result
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });

                // Determine expected return type from the interface method
                // The return type is always Object from the interface — need to unbox
                // based on expected result type. Look at the expr's type.
                let result_jvm = self
                    .type_to_jvm(&func.ty)
                    .unwrap_or(JvmType::StructRef(self.refs.object_class));
                let expected_ret = if let Type::Fn(_, ret) = &func.ty {
                    self.type_to_jvm(ret)
                        .unwrap_or(JvmType::StructRef(self.refs.object_class))
                } else {
                    result_jvm
                };

                // Unbox the Object result to the expected type
                match expected_ret {
                    JvmType::Long | JvmType::Double | JvmType::Int => {
                        self.unbox_if_needed(expected_ret);
                    }
                    JvmType::Ref => {
                        self.emit(Instruction::Checkcast(self.refs.string_class));
                        self.frame.pop_type();
                        self.frame.push_type(VerificationType::Object {
                            cpool_index: self.refs.string_class,
                        });
                    }
                    JvmType::StructRef(idx) if idx != self.refs.object_class => {
                        self.emit(Instruction::Checkcast(idx));
                        self.frame.pop_type();
                        self.frame
                            .push_type(VerificationType::Object { cpool_index: idx });
                    }
                    _ => {}
                }

                return Ok(expected_ret);
            }
        }

        // Check if calling a constrained function — need to prepend dict args
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

        // Look up function info (need to clone out to avoid borrow conflict)
        let info = self
            .types
            .functions
            .get(name)
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;
        let method_ref = info.method_ref;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;
        let is_void = info.is_void;

        // Push dict args first for constrained functions
        if !explicit_requirements.is_empty() {
            if let Some((param_patterns, ret_pattern)) = self.types.fn_tc_types.get(name).cloned() {
                for requirement in &explicit_requirements {
                    let requirement_ty = Self::resolve_function_requirement_type(
                        requirement,
                        &param_patterns,
                        args,
                        Some((&ret_pattern, &result_ty)),
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
                        self.refs.object_class,
                    )?;
                }
            }
        } else if !constraint_traits.is_empty() {
            for (trait_name, param_idx) in &constraint_traits {
                // Determine concrete type from the constrained parameter
                if let Some(target_arg) = args.get(*param_idx) {
                    self.emit_dict_argument_for_type(
                        trait_name,
                        &target_arg.ty,
                        self.refs.object_class,
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
                if idx == self.refs.object_class
                    && !matches!(arg_type, JvmType::StructRef(_) | JvmType::Ref)
                {
                    // Primitive → Object: box
                    self.box_if_needed(arg_type);
                } else if idx != self.refs.object_class {
                    // Object → specific ref type: checkcast
                    if let JvmType::StructRef(arg_idx) = arg_type {
                        if arg_idx == self.refs.object_class && arg_idx != idx {
                            self.emit(Instruction::Checkcast(idx));
                            self.frame.pop_type();
                            self.frame
                                .push_type(VerificationType::Object { cpool_index: idx });
                        }
                    }
                }
            }
        }

        // Pop argument types from stack
        for pt in param_types.iter().rev() {
            self.pop_jvm_type(*pt);
        }

        // Emit invokestatic
        self.emit(Instruction::Invokestatic(method_ref));

        if is_void {
            // Void-returning extern: push dummy Unit value
            self.emit(Instruction::Iconst_0);
            self.frame.push_type(VerificationType::Integer);
            Ok(JvmType::Int)
        } else {
            // Push return type
            self.push_jvm_type(return_type);
            Ok(return_type)
        }
    }

    fn compile_field_access(
        &mut self,
        expr: &TypedExpr,
        field: &str,
    ) -> Result<JvmType, CodegenError> {
        let base_type = self.compile_expr(expr, false)?;
        let class_idx = match base_type {
            JvmType::StructRef(idx) => idx,
            _ => {
                return Err(CodegenError::TypeError(
                    "field access on non-struct type".to_string(),
                ))
            }
        };

        // Find struct info by class index
        let (struct_name, accessor_ref, field_type) = {
            let si = self
                .types
                .struct_info
                .values()
                .find(|s| s.class_index == class_idx)
                .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
            let accessor_ref = *si
                .accessor_refs
                .get(field)
                .ok_or_else(|| CodegenError::TypeError(format!("unknown field: {field}")))?;
            let field_type = si
                .fields
                .iter()
                .find(|(n, _)| n == field)
                .map(|(_, t)| *t)
                .ok_or_else(|| CodegenError::TypeError(format!("unknown field: {field}")))?;
            (si.class_name.clone(), accessor_ref, field_type)
        };

        self.pop_jvm_type(base_type);
        self.emit(Instruction::Invokevirtual(accessor_ref));
        self.push_jvm_type(field_type);

        Ok(field_type)
    }

    fn compile_question_mark(
        &mut self,
        inner: &TypedExpr,
        is_option: bool,
        result_ty: &Type,
        span: krypton_parser::ast::Span,
    ) -> Result<JvmType, CodegenError> {
        // Compile inner expression — produces a StructRef for the sum type (Result or Option)
        let inner_type = self.compile_expr(inner, false)?;

        let sum_name = if is_option { "Option" } else { "Result" };
        let success_variant = if is_option { "Some" } else { "Ok" };

        let sum_info = self
            .types
            .sum_type_info
            .get(sum_name)
            .ok_or_else(|| CodegenError::TypeError(format!("unknown sum type: {sum_name}")))?;
        let interface_class_index = sum_info.interface_class_index;
        let success_vi = sum_info.variants.get(success_variant).ok_or_else(|| {
            CodegenError::TypeError(format!("unknown variant: {success_variant}"))
        })?;
        let success_class_index = success_vi.class_index;
        let success_field_refs = success_vi.field_refs.clone();
        let success_fields = success_vi.fields.clone();

        // Store inner expression result in a temp local
        let temp_slot = self.next_local;
        self.next_local += 1;
        self.emit(Instruction::Astore(temp_slot as u8));
        self.pop_jvm_type(inner_type);
        self.frame.local_types.push(VerificationType::Object {
            cpool_index: interface_class_index,
        });

        // instanceof check: is it the success variant?
        self.emit(Instruction::Aload(temp_slot as u8));
        self.frame.push_type(VerificationType::Object {
            cpool_index: interface_class_index,
        });
        self.emit(Instruction::Instanceof(success_class_index));
        self.frame.pop_type(); // pop ref
        self.frame.push_type(VerificationType::Integer); // push int result

        // Ifeq → early return branch (not the success variant)
        let ifeq_idx = self.code.len();
        self.emit(Instruction::Ifeq(0)); // placeholder
        self.frame.pop_type(); // consume int from instanceof

        // Save stack state at branch point
        let stack_at_branch = self.frame.stack_types.clone();

        // Success path: checkcast and extract value0 field
        self.emit(Instruction::Aload(temp_slot as u8));
        self.frame.push_type(VerificationType::Object {
            cpool_index: interface_class_index,
        });
        self.emit(Instruction::Checkcast(success_class_index));
        self.frame.pop_type(); // pop old ref type
        self.frame.push_type(VerificationType::Object {
            cpool_index: success_class_index,
        });

        // Getfield value0
        let field_ref = success_field_refs[0];
        let (_fname, field_jvm_type, is_erased) = &success_fields[0];
        let field_jvm_type = *field_jvm_type;
        let is_erased = *is_erased;
        self.emit(Instruction::Getfield(field_ref));
        self.frame.pop_type(); // pop checkcast ref
        if is_erased {
            self.frame.push_type(VerificationType::Object {
                cpool_index: self.refs.object_class,
            });
        } else {
            self.push_jvm_type(field_jvm_type);
        }

        // Determine the actual JVM type of the unwrapped value
        let actual_jvm_type = self.type_to_jvm(result_ty)?;
        let result_type = if is_erased {
            // Unbox from Object to the actual type
            self.unbox_if_needed(actual_jvm_type);
            actual_jvm_type
        } else {
            field_jvm_type
        };

        let stack_after_success = self.frame.stack_types.clone();

        // Goto after (skip early return)
        let goto_idx = self.code.len();
        self.emit(Instruction::Goto(0)); // placeholder

        // Early return branch: close live resources, load temp and Areturn
        let early_return_start = self.code.len() as u16;
        self.frame.stack_types = stack_at_branch;
        self.frame.record_frame(early_return_start);

        // Auto-close live resources before early return
        if let Some(bindings) = self.auto_close.early_returns.get(&span).cloned() {
            for binding in &bindings {
                self.emit_auto_close(binding)?;
            }
        }

        self.emit(Instruction::Aload(temp_slot as u8));
        self.frame.push_type(VerificationType::Object {
            cpool_index: interface_class_index,
        });
        self.emit(Instruction::Areturn);
        self.frame.pop_type();

        // After label
        let after = self.code.len() as u16;
        self.frame.stack_types = stack_after_success;
        self.frame.record_frame(after);

        // Patch jumps
        self.code[ifeq_idx] = Instruction::Ifeq(early_return_start);
        self.code[goto_idx] = Instruction::Goto(after);

        Ok(result_type)
    }

    fn compile_struct_update(
        &mut self,
        base: &TypedExpr,
        updates: &[(String, TypedExpr)],
    ) -> Result<JvmType, CodegenError> {
        // Compile base expression and store in temp local
        let base_type = self.compile_expr(base, false)?;
        let class_idx = match base_type {
            JvmType::StructRef(idx) => idx,
            _ => {
                return Err(CodegenError::TypeError(
                    "struct update on non-struct type".to_string(),
                ))
            }
        };

        let base_slot = self.next_local;
        self.next_local += 1;
        self.emit(Instruction::Astore(base_slot as u8));
        self.pop_jvm_type(base_type);
        let vtypes = self.jvm_type_to_vtypes(base_type);
        self.frame.local_types.extend(vtypes);

        // Look up struct info
        let si = self
            .types
            .struct_info
            .values()
            .find(|s| s.class_index == class_idx)
            .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
        let constructor_ref = si.constructor_ref;
        let fields = si.fields.clone();
        let accessor_refs = si.accessor_refs.clone();

        self.emit(Instruction::New(class_idx));
        self.frame.push_type(VerificationType::UninitializedThis);
        self.emit(Instruction::Dup);
        self.frame.push_type(VerificationType::UninitializedThis);

        // Build update map
        let update_names: HashMap<&str, usize> = updates
            .iter()
            .enumerate()
            .map(|(i, (name, _))| (name.as_str(), i))
            .collect();

        for (field_name, field_type) in &fields {
            if let Some(&idx) = update_names.get(field_name.as_str()) {
                // Use updated value
                self.compile_expr(&updates[idx].1, false)?;
            } else {
                // Copy from base using accessor
                self.emit(Instruction::Aload(base_slot as u8));
                self.push_jvm_type(base_type);
                let accessor_ref = accessor_refs[field_name];
                self.emit(Instruction::Invokevirtual(accessor_ref));
                self.pop_jvm_type(base_type);
                self.push_jvm_type(*field_type);
            }
        }

        // Pop args + uninit refs
        for (_, ft) in &fields {
            self.pop_jvm_type(*ft);
        }
        self.frame.pop_type(); // dup'd uninit
        self.frame.pop_type(); // original uninit

        self.emit(Instruction::Invokespecial(constructor_ref));
        self.push_jvm_type(base_type);

        Ok(base_type)
    }

    fn compile_struct_lit(
        &mut self,
        fields: &[(String, TypedExpr)],
        struct_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        let struct_jvm = self.type_to_jvm(struct_ty)?;
        let class_idx = match struct_jvm {
            JvmType::StructRef(idx) => idx,
            _ => {
                return Err(CodegenError::TypeError(
                    "struct literal for non-struct type".to_string(),
                ))
            }
        };

        let si = self
            .types
            .struct_info
            .values()
            .find(|s| s.class_index == class_idx)
            .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
        let constructor_ref = si.constructor_ref;
        let ordered_fields = si.fields.clone();

        let field_values: HashMap<&str, &TypedExpr> = fields
            .iter()
            .map(|(name, expr)| (name.as_str(), expr))
            .collect();

        self.emit(Instruction::New(class_idx));
        self.frame.push_type(VerificationType::UninitializedThis);
        self.emit(Instruction::Dup);
        self.frame.push_type(VerificationType::UninitializedThis);

        for (field_name, _) in &ordered_fields {
            let value = field_values.get(field_name.as_str()).ok_or_else(|| {
                CodegenError::TypeError(format!("missing struct field: {field_name}"))
            })?;
            self.compile_expr(value, false)?;
        }

        for (_, field_type) in &ordered_fields {
            self.pop_jvm_type(*field_type);
        }
        self.frame.pop_type();
        self.frame.pop_type();

        self.emit(Instruction::Invokespecial(constructor_ref));
        self.push_jvm_type(struct_jvm);

        Ok(struct_jvm)
    }

    fn compile_recur(
        &mut self,
        args: &[TypedExpr],
        in_tail: bool,
        expr_span: krypton_parser::ast::Span,
    ) -> Result<JvmType, CodegenError> {
        if !in_tail {
            return Err(CodegenError::RecurNotInTailPosition);
        }
        let return_type = self
            .fn_return_type
            .ok_or_else(|| CodegenError::UnsupportedExpr("recur outside function".to_string()))?;
        let fn_params = self.fn_params.clone();

        // Auto-close live resources before recur (before compiling new args,
        // while old resource values are still in their local slots)
        if let Some(bindings) = self.auto_close.recur_closes.get(&expr_span).cloned() {
            for binding in &bindings {
                self.emit_auto_close(binding)?;
            }
        }

        // Compile all args onto the stack
        for arg in args {
            self.compile_expr(arg, false)?;
        }

        // Store to param local slots in reverse order (stack is LIFO)
        for &(slot, jvm_ty) in fn_params.iter().rev() {
            let store = match jvm_ty {
                JvmType::Long => Instruction::Lstore(slot as u8),
                JvmType::Double => Instruction::Dstore(slot as u8),
                JvmType::Int => Instruction::Istore(slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Astore(slot as u8),
            };
            self.emit(store);
            self.pop_jvm_type(jvm_ty);
        }

        // Record StackMapTable frame at instruction 1 (after Nop) for back-edge.
        // Must use initial locals (params only) and empty stack.
        let initial_locals: Vec<VerificationType> = fn_params
            .iter()
            .flat_map(|&(_, jvm_ty)| self.jvm_type_to_vtypes(jvm_ty))
            .collect();
        self.frame.frames.insert(
            1,
            (
                initial_locals
                    .iter()
                    .filter(|vt| !matches!(vt, VerificationType::Top))
                    .cloned()
                    .collect(),
                vec![],
            ),
        );

        // Goto instruction 1 (after Nop at instruction 0)
        self.emit(Instruction::Goto(1));

        // Push return type onto stack tracker for consistency with if-else merging.
        // Code after goto is unreachable, but compile_if asserts both branches match.
        self.push_jvm_type(return_type);

        Ok(return_type)
    }

    /// Box a primitive value on the stack if needed for erased type params.
    pub(super) fn box_if_needed(&mut self, actual_type: JvmType) -> JvmType {
        match actual_type {
            JvmType::Long => {
                self.frame.pop_type_n(2); // Long + Top
                self.emit(Instruction::Invokestatic(self.refs.long_box_valueof));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.long_box_class,
                });
                JvmType::Ref
            }
            JvmType::Double => {
                self.frame.pop_type_n(2); // Double + Top
                self.emit(Instruction::Invokestatic(self.refs.double_box_valueof));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.double_box_class,
                });
                JvmType::Ref
            }
            JvmType::Int => {
                self.frame.pop_type(); // Integer
                self.emit(Instruction::Invokestatic(self.refs.bool_box_valueof));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.bool_box_class,
                });
                JvmType::Ref
            }
            _ => actual_type, // already a reference type
        }
    }

    /// Unbox a value from Object to a primitive type if needed.
    fn unbox_if_needed(&mut self, target: JvmType) {
        match target {
            JvmType::Long => {
                self.emit(Instruction::Checkcast(self.refs.long_box_class));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.long_box_class,
                });
                self.emit(Instruction::Invokevirtual(self.refs.long_unbox));
                self.frame.pop_type();
                self.frame.push_long_type();
            }
            JvmType::Double => {
                self.emit(Instruction::Checkcast(self.refs.double_box_class));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.double_box_class,
                });
                self.emit(Instruction::Invokevirtual(self.refs.double_unbox));
                self.frame.pop_type();
                self.frame.push_double_type();
            }
            JvmType::Int => {
                self.emit(Instruction::Checkcast(self.refs.bool_box_class));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.bool_box_class,
                });
                self.emit(Instruction::Invokevirtual(self.refs.bool_unbox));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Integer);
            }
            _ => {} // already a reference type, no unboxing needed
        }
    }

    fn bind_type_vars(pattern: &Type, actual: &Type, bindings: &mut HashMap<u32, Type>) -> bool {
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

    fn extract_type_arg(ty: &Type, param_idx: usize) -> Option<Type> {
        match ty {
            Type::Named(_, args) => args.get(param_idx).cloned(),
            Type::Own(inner) => Self::extract_type_arg(inner, param_idx),
            _ => None,
        }
    }

    fn resolve_dict_requirement_type(
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

    fn resolve_function_requirement_type(
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

    fn resolve_function_ref_requirement_type(
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

    fn emit_dict_argument_for_type(
        &mut self,
        trait_name: &str,
        ty: &Type,
        pushed_class: u16,
    ) -> Result<(), CodegenError> {
        if matches!(ty, Type::Var(_))
            || matches!(ty, Type::App(ctor, _) if Self::is_abstract_type_ctor(ctor))
        {
            if let Some(&dict_slot) = self.traits.dict_locals.get(trait_name) {
                self.emit(Instruction::Aload(dict_slot as u8));
                self.frame.push_type(VerificationType::Object {
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
            self.emit(Instruction::Getstatic(singleton.instance_field_ref));
            self.frame.push_type(VerificationType::Object {
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
            self.emit(Instruction::New(inst_class));
            self.frame.push_type(VerificationType::Object {
                cpool_index: inst_class,
            });
            self.emit(Instruction::Dup);
            self.frame.push_type(VerificationType::Object {
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
                    self.refs.object_class,
                )?;
            }
            self.emit(Instruction::Invokespecial(init_ref));
            for _ in &instance_info.requirements {
                self.frame.pop_type();
            }
            self.frame.pop_type();
            return Ok(());
        }

        Err(CodegenError::UndefinedVariable(format!(
            "no instance of {trait_name} for {ty}"
        )))
    }

    /// Compile a lambda expression.
    fn compile_lambda(
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
                    "lambda has non-function type".to_string(),
                ))
            }
        };

        // Ensure FunN interface exists
        self.lambda
            .ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
        let fun_class_idx = self.lambda.fun_classes[&arity];

        // Find captured variables: scan body for Var names that are in self.locals but not lambda params
        let param_names: std::collections::HashSet<&str> =
            params.iter().map(|s| s.as_str()).collect();
        let mut captures: Vec<(String, u16, JvmType)> = Vec::new();
        self.collect_captures(body, &param_names, &mut captures);
        // Deduplicate
        let mut seen = std::collections::HashSet::new();
        captures.retain(|(name, _, _)| seen.insert(name.clone()));

        // Save compiler state for the outer method
        let saved_code = std::mem::take(&mut self.code);
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_local_types = std::mem::take(&mut self.frame.local_types);
        let saved_next_local = self.next_local;
        let saved_stack_types = std::mem::take(&mut self.frame.stack_types);
        let saved_frames = std::mem::take(&mut self.frame.frames);
        let saved_max_stack_depth = self.frame.max_stack_depth;
        let saved_fn_params = std::mem::take(&mut self.fn_params);
        let saved_fn_return_type = self.fn_return_type.take();
        let saved_local_fn_info = std::mem::take(&mut self.local_fn_info);

        // Reset for lambda body compilation
        self.code.clear();
        self.locals.clear();
        self.frame.local_types.clear();
        self.next_local = 0;
        self.frame.stack_types.clear();
        self.frame.frames.clear();
        self.frame.max_stack_depth = 0;
        self.fn_params.clear();
        self.fn_return_type = None;

        // Register captured vars as first params (all boxed to Object)
        for (cap_name, _, cap_type) in &captures {
            let slot = self.next_local;
            self.locals.insert(cap_name.clone(), (slot, *cap_type));
            self.frame.local_types.push(VerificationType::Object {
                cpool_index: self.refs.object_class,
            });
            self.next_local += 1;
        }

        // Register lambda params (all as Object, will unbox)
        let mut lambda_param_slots = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let slot = self.next_local;
            // Store as Object initially
            self.locals.insert(
                p.clone(),
                (slot, JvmType::StructRef(self.refs.object_class)),
            );
            self.frame.local_types.push(VerificationType::Object {
                cpool_index: self.refs.object_class,
            });
            lambda_param_slots.push((slot, param_jvm_types[i]));
            self.next_local += 1;
        }

        // JVM type erasure invariant: Lambda params and captures arrive as Object
        // (FunN.apply signature is Object -> Object). Any slot whose actual type is
        // not Object must be cast/unboxed here before the body can use it:
        //   - Primitives (Int/Long/Double): unbox via Long.longValue() etc.
        //   - Structs (StructRef != object_class): checkcast to the concrete class.
        // The same invariant applies to erased generic variant fields extracted in
        // compile_pattern_bind (e.g., Some(b) where b: Player).

        // Unbox primitive params from Object to actual types
        for (i, p) in params.iter().enumerate() {
            let actual_type = param_jvm_types[i];
            if matches!(actual_type, JvmType::Long | JvmType::Double | JvmType::Int) {
                let slot = lambda_param_slots[i].0;
                // Load the Object param
                self.emit(Instruction::Aload(slot as u8));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });
                // Unbox
                self.unbox_if_needed(actual_type);
                // Store back to a new slot with correct type
                let new_slot = self.next_local;
                let slot_size = match actual_type {
                    JvmType::Long | JvmType::Double => 2,
                    _ => 1,
                };
                self.next_local += slot_size;
                let store = match actual_type {
                    JvmType::Long => Instruction::Lstore(new_slot as u8),
                    JvmType::Double => Instruction::Dstore(new_slot as u8),
                    JvmType::Int => Instruction::Istore(new_slot as u8),
                    _ => unreachable!(),
                };
                self.emit(store);
                self.pop_jvm_type(actual_type);
                let vtypes = self.jvm_type_to_vtypes(actual_type);
                self.frame.local_types.extend(vtypes);
                self.locals.insert(p.clone(), (new_slot, actual_type));
            }
        }

        // Cast struct-typed params from Object to their actual struct type
        for (i, p) in params.iter().enumerate() {
            let actual_type = param_jvm_types[i];
            if let JvmType::StructRef(class_idx) = actual_type {
                if class_idx != self.refs.object_class {
                    let slot = lambda_param_slots[i].0;
                    self.emit(Instruction::Aload(slot as u8));
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: self.refs.object_class,
                    });
                    self.emit(Instruction::Checkcast(class_idx));
                    self.frame.pop_type();
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    let new_slot = self.next_local;
                    self.next_local += 1;
                    self.emit(Instruction::Astore(new_slot as u8));
                    self.frame.pop_type();
                    self.frame.local_types.push(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    self.locals.insert(p.clone(), (new_slot, actual_type));
                }
            }
        }

        // Cast String-typed (Ref) params from Object to String
        for (i, p) in params.iter().enumerate() {
            let actual_type = param_jvm_types[i];
            if actual_type == JvmType::Ref {
                let slot = lambda_param_slots[i].0;
                self.emit(Instruction::Aload(slot as u8));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });
                self.emit(Instruction::Checkcast(self.refs.string_class));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.string_class,
                });
                let new_slot = self.next_local;
                self.next_local += 1;
                self.emit(Instruction::Astore(new_slot as u8));
                self.frame.pop_type();
                self.frame.local_types.push(VerificationType::Object {
                    cpool_index: self.refs.string_class,
                });
                self.locals.insert(p.clone(), (new_slot, actual_type));
            }
        }

        // Also unbox captured vars if they are primitive types
        for (cap_name, _, cap_type) in &captures {
            let actual_type = *cap_type;
            if matches!(actual_type, JvmType::Long | JvmType::Double | JvmType::Int) {
                let (slot, _) = self.locals[cap_name];
                self.emit(Instruction::Aload(slot as u8));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });
                self.unbox_if_needed(actual_type);
                let new_slot = self.next_local;
                let slot_size = match actual_type {
                    JvmType::Long | JvmType::Double => 2,
                    _ => 1,
                };
                self.next_local += slot_size;
                let store = match actual_type {
                    JvmType::Long => Instruction::Lstore(new_slot as u8),
                    JvmType::Double => Instruction::Dstore(new_slot as u8),
                    JvmType::Int => Instruction::Istore(new_slot as u8),
                    _ => unreachable!(),
                };
                self.emit(store);
                self.pop_jvm_type(actual_type);
                let vtypes = self.jvm_type_to_vtypes(actual_type);
                self.frame.local_types.extend(vtypes);
                self.locals
                    .insert(cap_name.clone(), (new_slot, actual_type));
            }
        }

        // Cast struct-typed captured vars from Object to their actual struct type
        for (cap_name, _, cap_type) in &captures {
            let actual_type = *cap_type;
            if let JvmType::StructRef(class_idx) = actual_type {
                if class_idx != self.refs.object_class {
                    let (slot, _) = self.locals[cap_name];
                    self.emit(Instruction::Aload(slot as u8));
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: self.refs.object_class,
                    });
                    self.emit(Instruction::Checkcast(class_idx));
                    self.frame.pop_type();
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    let new_slot = self.next_local;
                    self.next_local += 1;
                    self.emit(Instruction::Astore(new_slot as u8));
                    self.frame.pop_type();
                    self.frame.local_types.push(VerificationType::Object {
                        cpool_index: class_idx,
                    });
                    self.locals
                        .insert(cap_name.clone(), (new_slot, actual_type));
                }
            }
        }

        // Cast String-typed (Ref) captured vars from Object to String
        for (cap_name, _, cap_type) in &captures {
            let actual_type = *cap_type;
            if actual_type == JvmType::Ref {
                let (slot, _) = self.locals[cap_name];
                self.emit(Instruction::Aload(slot as u8));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });
                self.emit(Instruction::Checkcast(self.refs.string_class));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.string_class,
                });
                let new_slot = self.next_local;
                self.next_local += 1;
                self.emit(Instruction::Astore(new_slot as u8));
                self.frame.pop_type();
                self.frame.local_types.push(VerificationType::Object {
                    cpool_index: self.refs.string_class,
                });
                self.locals
                    .insert(cap_name.clone(), (new_slot, actual_type));
            }
        }

        // Compile the body
        let body_type = self.compile_expr(body, false)?;

        // Box the result if needed
        self.box_if_needed(body_type);

        // Return
        self.emit(Instruction::Areturn);

        // Build the lambda method
        let lambda_name = format!("lambda${}", self.lambda.lambda_counter);
        self.lambda.lambda_counter += 1;

        // Descriptor: all Object params (captures + lambda params) -> Object
        let total_params = captures.len() + params.len();
        let mut lambda_desc = String::from("(");
        for _ in 0..total_params {
            lambda_desc.push_str("Ljava/lang/Object;");
        }
        lambda_desc.push_str(")Ljava/lang/Object;");

        let lambda_name_idx = self.cp.add_utf8(&lambda_name)?;
        let lambda_desc_idx = self.cp.add_utf8(&lambda_desc)?;

        let stack_map_frames = self.frame.build_stack_map_frames();
        let code_attributes = if stack_map_frames.is_empty() {
            vec![]
        } else {
            vec![Attribute::StackMapTable {
                name_index: self.refs.smt_name,
                frames: stack_map_frames,
            }]
        };

        let lambda_method = Method {
            access_flags: MethodAccessFlags::PRIVATE
                | MethodAccessFlags::STATIC
                | MethodAccessFlags::SYNTHETIC,
            name_index: lambda_name_idx,
            descriptor_index: lambda_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: self.refs.code_utf8,
                max_stack: self.frame.max_stack(),
                max_locals: self.next_local,
                code: std::mem::take(&mut self.code),
                exception_table: vec![],
                attributes: code_attributes,
            }],
        };

        self.lambda.lambda_methods.push(lambda_method);

        // Restore compiler state
        self.code = saved_code;
        self.locals = saved_locals;
        self.frame.local_types = saved_local_types;
        self.next_local = saved_next_local;
        self.frame.stack_types = saved_stack_types;
        self.frame.frames = saved_frames;
        self.frame.max_stack_depth = saved_max_stack_depth;
        self.fn_params = saved_fn_params;
        self.fn_return_type = saved_fn_return_type;
        self.local_fn_info = saved_local_fn_info;

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
        // If no captures: ()LFunN;
        // If captures: (Object, ...)LFunN;  (one Object per capture)
        let fun_class_name = format!("Fun{arity}");
        let mut callsite_desc = String::from("(");
        for _ in 0..captures.len() {
            callsite_desc.push_str("Ljava/lang/Object;");
        }
        callsite_desc.push_str(&format!(")L{fun_class_name};"));

        let indy_idx = self
            .cp
            .add_invoke_dynamic(bsm_index, "apply", &callsite_desc)?;

        // 6. Push captured variables onto stack (boxed)
        for (_cap_name, cap_slot, cap_type) in &captures {
            let load = match cap_type {
                JvmType::Long => Instruction::Lload(*cap_slot as u8),
                JvmType::Double => Instruction::Dload(*cap_slot as u8),
                JvmType::Int => Instruction::Iload(*cap_slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(*cap_slot as u8),
            };
            self.emit(load);
            self.push_jvm_type(*cap_type);
            self.box_if_needed(*cap_type);
        }

        // 7. Emit invokedynamic
        self.emit(Instruction::Invokedynamic(indy_idx));

        // Pop capture args from stack
        for _ in 0..captures.len() {
            self.frame.pop_type(); // each boxed capture is a single Object ref
        }

        // Push result type
        let result_type = JvmType::StructRef(fun_class_idx);
        self.push_jvm_type(result_type);

        Ok(result_type)
    }

    /// Collect captured variables from an expression.
    fn collect_captures(
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
                        if let Some(&(slot, ty)) = self.locals.get(name) {
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
                TypedExprKind::TypeApp { expr } => {
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

    fn compile_match(
        &mut self,
        scrutinee: &TypedExpr,
        arms: &[TypedMatchArm],
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // 1. Compile scrutinee and store in temp local
        let scrutinee_type = self.compile_expr(scrutinee, false)?;
        let scrutinee_slot = self.next_local;
        self.next_local += 1;
        self.emit(Instruction::Astore(scrutinee_slot as u8));
        self.pop_jvm_type(scrutinee_type);
        let vtypes = self.jvm_type_to_vtypes(scrutinee_type);
        self.frame.local_types.extend(vtypes);

        let stack_at_match = self.frame.stack_types.clone();
        let locals_at_match = self.locals.clone();
        let local_types_at_match = self.frame.local_types.clone();
        let next_local_at_match = self.next_local;

        let mut goto_patches: Vec<usize> = Vec::new();
        let mut result_type = None;
        let mut max_next_local = next_local_at_match;

        for (i, arm) in arms.iter().enumerate() {
            let is_last = i == arms.len() - 1;

            // Track high-water mark for locals
            if self.next_local > max_next_local {
                max_next_local = self.next_local;
            }

            // Restore state for each arm
            self.frame.stack_types = stack_at_match.clone();
            self.locals = locals_at_match.clone();
            self.frame.local_types = local_types_at_match.clone();
            self.next_local = next_local_at_match;

            // Record frame at this arm's start (branch target) — except first arm
            if i > 0 {
                let arm_start = self.code.len() as u16;
                self.frame.record_frame(arm_start);
            }

            // Compile pattern check (if not wildcard/var on last arm)
            self.nested_ifeq_patches.clear();
            let next_arm_patch = if !is_last {
                self.compile_pattern_check(
                    &arm.pattern,
                    scrutinee_slot,
                    scrutinee_type,
                    &scrutinee.ty,
                )?
            } else {
                // Last arm: bind pattern variables but no branch check
                self.compile_pattern_bind(
                    &arm.pattern,
                    scrutinee_slot,
                    scrutinee_type,
                    &scrutinee.ty,
                )?;
                None
            };
            let nested_patches = std::mem::take(&mut self.nested_ifeq_patches);

            // Compile arm body
            let arm_type = self.compile_expr(&arm.body, in_tail)?;

            // Normalize arm result type to match function return type
            let target_type = self.fn_return_type.unwrap_or(arm_type);
            if result_type.is_none() {
                result_type = Some(target_type);
            }
            // Box primitive to Object if needed
            if matches!(target_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
                && !matches!(arm_type, JvmType::StructRef(_) | JvmType::Ref)
            {
                self.box_if_needed(arm_type);
                // Fix stack type to match target (Object)
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: self.refs.object_class,
                });
            }
            // Unbox Object to primitive if needed
            else if !matches!(target_type, JvmType::StructRef(_) | JvmType::Ref)
                && matches!(arm_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
            {
                self.unbox_if_needed(target_type);
            }
            // Checkcast Object to specific ref type if needed
            else if matches!(target_type, JvmType::Ref | JvmType::StructRef(_))
                && !matches!(target_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
                && matches!(arm_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
            {
                let cast_class = match target_type {
                    JvmType::Ref => self.refs.string_class,
                    JvmType::StructRef(idx) => idx,
                    _ => unreachable!(),
                };
                self.emit(Instruction::Checkcast(cast_class));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: cast_class,
                });
            }

            // Goto after_match (except last arm)
            if !is_last {
                let goto_idx = self.code.len();
                self.emit(Instruction::Goto(0)); // placeholder
                goto_patches.push(goto_idx);
            }

            // Patch the next_arm branch target (and any nested ifeq patches)
            if let Some(patch_idx) = next_arm_patch {
                let next_arm_target = self.code.len() as u16;
                self.code[patch_idx] = Instruction::Ifeq(next_arm_target);
                for nested_idx in &nested_patches {
                    self.code[*nested_idx] = Instruction::Ifeq(next_arm_target);
                }
            }
        }

        // Track final arm's locals too
        if self.next_local > max_next_local {
            max_next_local = self.next_local;
        }

        // after_match: record frame with pre-match locals (arm-local bindings are out of scope
        // and different arms may have different types in the same slots)
        let after_match = self.code.len() as u16;
        self.frame.local_types = local_types_at_match.clone();
        self.frame.record_frame(after_match);

        // Patch all goto instructions
        for goto_idx in goto_patches {
            self.code[goto_idx] = Instruction::Goto(after_match);
        }

        // Restore locals scope but keep high-water mark for max_locals
        self.locals = locals_at_match;
        self.next_local = max_next_local;

        Ok(result_type.unwrap_or(JvmType::Int))
    }

    /// Compile pattern check: emits instanceof + ifeq for constructor patterns,
    /// binds variables, and returns the index of the ifeq to patch (if any).
    fn compile_pattern_check(
        &mut self,
        pattern: &TypedPattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
        scrutinee_tc_type: &Type,
    ) -> Result<Option<usize>, CodegenError> {
        match pattern {
            TypedPattern::Constructor { name, args, .. } => {
                // Look up variant info
                let sum_name = self
                    .types
                    .variant_to_sum
                    .get(name)
                    .cloned()
                    .ok_or_else(|| CodegenError::TypeError(format!("unknown variant: {name}")))?;
                let sum_info = &self.types.sum_type_info[&sum_name];
                let vi = &sum_info.variants[name];
                let variant_class_index = vi.class_index;
                let fields = vi.fields.clone();
                let field_refs = vi.field_refs.clone();

                // instanceof check
                self.emit(Instruction::Aload(scrutinee_slot as u8));
                self.push_jvm_type(scrutinee_type);
                self.emit(Instruction::Instanceof(variant_class_index));
                self.pop_jvm_type(scrutinee_type);
                self.frame.push_type(VerificationType::Integer);

                // ifeq placeholder → next arm
                let ifeq_idx = self.code.len();
                self.emit(Instruction::Ifeq(0)); // placeholder
                self.frame.pop_type(); // consume int from instanceof

                // If has sub-patterns, checkcast and extract fields
                if !args.is_empty() {
                    // checkcast and store cast ref in a local
                    self.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.push_jvm_type(scrutinee_type);
                    self.emit(Instruction::Checkcast(variant_class_index));
                    self.pop_jvm_type(scrutinee_type);
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    let cast_slot = self.next_local;
                    self.next_local += 1;
                    self.emit(Instruction::Astore(cast_slot as u8));
                    self.frame.pop_type();
                    self.frame.local_types.push(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    for (j, sub_pat) in args.iter().enumerate() {
                        if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                            continue;
                        }
                        let (_fname, field_jvm_type, is_erased) = &fields[j];
                        let field_ref = field_refs[j];

                        // Load cast ref, getfield
                        self.emit(Instruction::Aload(cast_slot as u8));
                        self.frame.push_type(VerificationType::Object {
                            cpool_index: variant_class_index,
                        });
                        self.emit(Instruction::Getfield(field_ref));
                        self.frame.pop_type(); // pop cast ref
                        if *is_erased {
                            self.frame.push_type(VerificationType::Object {
                                cpool_index: self.refs.string_class,
                            });
                        } else {
                            self.push_jvm_type(*field_jvm_type);
                        }

                        match sub_pat {
                            TypedPattern::Var { name: var_name, .. } => {
                                // Erased fields stay as Object refs — no unboxing here.
                                // Unboxing happens at monomorphic call sites.
                                let actual_type = if *is_erased {
                                    JvmType::StructRef(self.refs.object_class)
                                } else {
                                    *field_jvm_type
                                };
                                let var_slot = self.next_local;
                                let slot_size = match actual_type {
                                    JvmType::Long | JvmType::Double => 2,
                                    _ => 1,
                                };
                                self.next_local += slot_size;
                                let store = match actual_type {
                                    JvmType::Long => Instruction::Lstore(var_slot as u8),
                                    JvmType::Double => Instruction::Dstore(var_slot as u8),
                                    JvmType::Int => Instruction::Istore(var_slot as u8),
                                    JvmType::Ref | JvmType::StructRef(_) => {
                                        Instruction::Astore(var_slot as u8)
                                    }
                                };
                                self.emit(store);
                                self.pop_jvm_type(actual_type);
                                let vtypes = self.jvm_type_to_vtypes(actual_type);
                                self.frame.local_types.extend(vtypes);
                                self.locals
                                    .insert(var_name.clone(), (var_slot, actual_type));
                            }
                            TypedPattern::Constructor { .. } => {
                                // Nested constructor pattern: store field value in local,
                                // then recursively check
                                let nested_type = if *is_erased {
                                    // Erased field that is a nested sum type — keep as ref
                                    JvmType::StructRef(self.get_pattern_class_index(sub_pat)?)
                                } else {
                                    *field_jvm_type
                                };
                                let nested_slot = self.next_local;
                                self.next_local += 1;
                                self.emit(Instruction::Astore(nested_slot as u8));
                                self.frame.pop_type(); // pop the field value (object ref)
                                self.frame.local_types.push(VerificationType::Object {
                                    cpool_index: match nested_type {
                                        JvmType::StructRef(idx) => idx,
                                        _ => self.refs.string_class,
                                    },
                                });
                                // Recursively compile the nested pattern check
                                // but share the same ifeq target (next arm)
                                self.compile_nested_pattern(
                                    sub_pat,
                                    nested_slot,
                                    nested_type,
                                    ifeq_idx,
                                )?;
                            }
                            TypedPattern::Wildcard { .. } => {
                                // Already handled above, but just in case
                                self.frame.pop_type();
                                self.emit(Instruction::Pop);
                            }
                            _ => {}
                        }
                    }
                }

                Ok(Some(ifeq_idx))
            }
            TypedPattern::Wildcard { .. } => {
                // Always matches, no check needed
                Ok(None)
            }
            TypedPattern::Var { name, .. } => {
                // Always matches, bind the scrutinee
                self.emit(Instruction::Aload(scrutinee_slot as u8));
                self.push_jvm_type(scrutinee_type);
                let var_slot = self.next_local;
                self.next_local += 1;
                self.emit(Instruction::Astore(var_slot as u8));
                self.pop_jvm_type(scrutinee_type);
                let vtypes = self.jvm_type_to_vtypes(scrutinee_type);
                self.frame.local_types.extend(vtypes);
                self.locals.insert(name.clone(), (var_slot, scrutinee_type));
                Ok(None)
            }
            TypedPattern::Tuple { elements, .. } => {
                // Tuples are irrefutable — instanceof check then bind fields
                let elem_types = match scrutinee_tc_type {
                    Type::Tuple(elems) => elems,
                    _ => {
                        return Err(CodegenError::TypeError(
                            "expected tuple type for tuple pattern".into(),
                        ))
                    }
                };
                let arity = elements.len();
                let tuple_info = self.types.tuple_info.get(&arity).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown tuple arity: {arity}"))
                })?;
                let tuple_class = tuple_info.class_index;
                let field_refs: Vec<u16> = tuple_info.field_refs.clone();

                // instanceof check
                self.emit(Instruction::Aload(scrutinee_slot as u8));
                self.push_jvm_type(scrutinee_type);
                self.emit(Instruction::Instanceof(tuple_class));
                self.pop_jvm_type(scrutinee_type);
                self.frame.push_type(VerificationType::Integer);

                let ifeq_idx = self.code.len();
                self.emit(Instruction::Ifeq(0));
                self.frame.pop_type();

                // Extract and bind fields
                for (i, sub_pat) in elements.iter().enumerate() {
                    if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                        continue;
                    }
                    let field_ref = field_refs[i];
                    let elem_ty = &elem_types[i];
                    let elem_jvm_type = self.type_to_jvm(elem_ty)?;

                    self.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: tuple_class,
                    });
                    self.emit(Instruction::Getfield(field_ref));
                    self.frame.pop_type();
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: self.refs.object_class,
                    });
                    self.unbox_if_needed(elem_jvm_type);

                    if let TypedPattern::Var { name: var_name, .. } = sub_pat {
                        let var_slot = self.next_local;
                        let slot_size: u16 = match elem_jvm_type {
                            JvmType::Long | JvmType::Double => 2,
                            _ => 1,
                        };
                        self.next_local += slot_size;
                        let store = match elem_jvm_type {
                            JvmType::Long => Instruction::Lstore(var_slot as u8),
                            JvmType::Double => Instruction::Dstore(var_slot as u8),
                            JvmType::Int => Instruction::Istore(var_slot as u8),
                            JvmType::Ref | JvmType::StructRef(_) => {
                                Instruction::Astore(var_slot as u8)
                            }
                        };
                        self.emit(store);
                        self.pop_jvm_type(elem_jvm_type);
                        let vtypes = self.jvm_type_to_vtypes(elem_jvm_type);
                        self.frame.local_types.extend(vtypes);
                        self.locals
                            .insert(var_name.clone(), (var_slot, elem_jvm_type));
                    }
                }

                Ok(Some(ifeq_idx))
            }
            _ => Err(CodegenError::UnsupportedExpr(format!(
                "unsupported pattern in check: {pattern:?}"
            ))),
        }
    }

    /// Bind pattern variables without emitting checks (for last arm / wildcard).
    fn compile_pattern_bind(
        &mut self,
        pattern: &TypedPattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
        scrutinee_tc_type: &Type,
    ) -> Result<(), CodegenError> {
        match pattern {
            TypedPattern::Wildcard { .. } => Ok(()),
            TypedPattern::Var { name, .. } => {
                self.emit(Instruction::Aload(scrutinee_slot as u8));
                self.push_jvm_type(scrutinee_type);
                let var_slot = self.next_local;
                self.next_local += 1;
                self.emit(Instruction::Astore(var_slot as u8));
                self.pop_jvm_type(scrutinee_type);
                let vtypes = self.jvm_type_to_vtypes(scrutinee_type);
                self.frame.local_types.extend(vtypes);
                self.locals.insert(name.clone(), (var_slot, scrutinee_type));
                Ok(())
            }
            TypedPattern::Constructor { name, args, .. } => {
                // Last arm constructor — still need to extract fields
                let sum_name = self
                    .types
                    .variant_to_sum
                    .get(name)
                    .cloned()
                    .ok_or_else(|| CodegenError::TypeError(format!("unknown variant: {name}")))?;
                let sum_info = &self.types.sum_type_info[&sum_name];
                let vi = &sum_info.variants[name];
                let variant_class_index = vi.class_index;
                let fields = vi.fields.clone();
                let field_refs = vi.field_refs.clone();

                if !args.is_empty() {
                    self.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.push_jvm_type(scrutinee_type);
                    self.emit(Instruction::Checkcast(variant_class_index));
                    self.pop_jvm_type(scrutinee_type);
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    let cast_slot = self.next_local;
                    self.next_local += 1;
                    self.emit(Instruction::Astore(cast_slot as u8));
                    self.frame.pop_type();
                    self.frame.local_types.push(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    for (j, sub_pat) in args.iter().enumerate() {
                        if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                            continue;
                        }
                        let (_fname, field_jvm_type, is_erased) = &fields[j];
                        let field_ref = field_refs[j];

                        self.emit(Instruction::Aload(cast_slot as u8));
                        self.frame.push_type(VerificationType::Object {
                            cpool_index: variant_class_index,
                        });
                        self.emit(Instruction::Getfield(field_ref));
                        self.frame.pop_type();
                        if *is_erased {
                            self.frame.push_type(VerificationType::Object {
                                cpool_index: self.refs.string_class,
                            });
                        } else {
                            self.push_jvm_type(*field_jvm_type);
                        }

                        if let TypedPattern::Var {
                            name: var_name,
                            ty: var_tc_type,
                            ..
                        } = sub_pat
                        {
                            // For erased (generic) fields, resolve the actual JVM type
                            // from the typechecker type on the pattern variable.
                            let actual_type = if *is_erased {
                                self.type_to_jvm(var_tc_type)
                                    .unwrap_or(JvmType::StructRef(self.refs.object_class))
                            } else {
                                *field_jvm_type
                            };

                            // If the field was erased, cast/unbox from Object to the actual type.
                            if *is_erased {
                                match actual_type {
                                    JvmType::StructRef(class_idx)
                                        if class_idx != self.refs.object_class =>
                                    {
                                        // Cast Object to the correct struct class.
                                        self.frame.pop_type();
                                        self.frame.push_type(VerificationType::Object {
                                            cpool_index: self.refs.object_class,
                                        });
                                        self.emit(Instruction::Checkcast(class_idx));
                                        self.frame.pop_type();
                                        self.frame.push_type(VerificationType::Object {
                                            cpool_index: class_idx,
                                        });
                                    }
                                    JvmType::Long | JvmType::Double | JvmType::Int => {
                                        // Unbox Object to primitive.
                                        self.frame.pop_type();
                                        self.frame.push_type(VerificationType::Object {
                                            cpool_index: self.refs.object_class,
                                        });
                                        self.unbox_if_needed(actual_type);
                                    }
                                    _ => {}
                                }
                            }

                            let var_slot = self.next_local;
                            let slot_size = match actual_type {
                                JvmType::Long | JvmType::Double => 2,
                                _ => 1,
                            };
                            self.next_local += slot_size;
                            let store = match actual_type {
                                JvmType::Long => Instruction::Lstore(var_slot as u8),
                                JvmType::Double => Instruction::Dstore(var_slot as u8),
                                JvmType::Int => Instruction::Istore(var_slot as u8),
                                JvmType::Ref | JvmType::StructRef(_) => {
                                    Instruction::Astore(var_slot as u8)
                                }
                            };
                            self.emit(store);
                            self.pop_jvm_type(actual_type);
                            let vtypes = self.jvm_type_to_vtypes(actual_type);
                            self.frame.local_types.extend(vtypes);
                            self.locals
                                .insert(var_name.clone(), (var_slot, actual_type));
                        }
                    }
                }
                Ok(())
            }
            TypedPattern::Tuple { elements, .. } => {
                let elem_types = match scrutinee_tc_type {
                    Type::Tuple(elems) => elems,
                    _ => {
                        return Err(CodegenError::TypeError(
                            "expected tuple type for tuple pattern".into(),
                        ))
                    }
                };
                let arity = elements.len();
                let tuple_info = self.types.tuple_info.get(&arity).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown tuple arity: {arity}"))
                })?;
                let tuple_class = tuple_info.class_index;
                let field_refs: Vec<u16> = tuple_info.field_refs.clone();

                for (i, sub_pat) in elements.iter().enumerate() {
                    if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                        continue;
                    }
                    let field_ref = field_refs[i];
                    let elem_ty = &elem_types[i];
                    let elem_jvm_type = self.type_to_jvm(elem_ty)?;

                    self.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: tuple_class,
                    });
                    self.emit(Instruction::Getfield(field_ref));
                    self.frame.pop_type();
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: self.refs.object_class,
                    });
                    self.unbox_if_needed(elem_jvm_type);

                    if let TypedPattern::Var { name: var_name, .. } = sub_pat {
                        let var_slot = self.next_local;
                        let slot_size: u16 = match elem_jvm_type {
                            JvmType::Long | JvmType::Double => 2,
                            _ => 1,
                        };
                        self.next_local += slot_size;
                        let store = match elem_jvm_type {
                            JvmType::Long => Instruction::Lstore(var_slot as u8),
                            JvmType::Double => Instruction::Dstore(var_slot as u8),
                            JvmType::Int => Instruction::Istore(var_slot as u8),
                            JvmType::Ref | JvmType::StructRef(_) => {
                                Instruction::Astore(var_slot as u8)
                            }
                        };
                        self.emit(store);
                        self.pop_jvm_type(elem_jvm_type);
                        let vtypes = self.jvm_type_to_vtypes(elem_jvm_type);
                        self.frame.local_types.extend(vtypes);
                        self.locals
                            .insert(var_name.clone(), (var_slot, elem_jvm_type));
                    }
                }
                Ok(())
            }
            _ => Err(CodegenError::UnsupportedExpr(format!(
                "unsupported pattern in bind: {pattern:?}"
            ))),
        }
    }

    /// Get the class index for a constructor pattern's variant type's parent interface.
    fn get_pattern_class_index(&self, pattern: &TypedPattern) -> Result<u16, CodegenError> {
        match pattern {
            TypedPattern::Constructor { name, .. } => {
                let sum_name =
                    self.types.variant_to_sum.get(name).ok_or_else(|| {
                        CodegenError::TypeError(format!("unknown variant: {name}"))
                    })?;
                let sum_info = &self.types.sum_type_info[sum_name];
                Ok(sum_info.interface_class_index)
            }
            _ => Err(CodegenError::TypeError(
                "expected constructor pattern".to_string(),
            )),
        }
    }

    /// Compile a nested constructor pattern within an already-matched outer pattern.
    fn compile_nested_pattern(
        &mut self,
        pattern: &TypedPattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
        _outer_ifeq_idx: usize,
    ) -> Result<(), CodegenError> {
        if let TypedPattern::Constructor { name, args, .. } = pattern {
            let sum_name = self
                .types
                .variant_to_sum
                .get(name)
                .cloned()
                .ok_or_else(|| CodegenError::TypeError(format!("unknown variant: {name}")))?;
            let sum_info = &self.types.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            let variant_class_index = vi.class_index;
            let fields = vi.fields.clone();
            let field_refs = vi.field_refs.clone();

            // instanceof check
            self.emit(Instruction::Aload(scrutinee_slot as u8));
            self.frame.push_type(VerificationType::Object {
                cpool_index: match scrutinee_type {
                    JvmType::StructRef(idx) => idx,
                    _ => self.refs.string_class,
                },
            });
            self.emit(Instruction::Instanceof(variant_class_index));
            self.frame.pop_type();
            self.frame.push_type(VerificationType::Integer);

            // ifeq → same outer target (we'll add a new ifeq that also jumps to next arm)
            let nested_ifeq_idx = self.code.len();
            self.emit(Instruction::Ifeq(0)); // placeholder — will share target with outer
            self.frame.pop_type();

            // Extract fields if needed
            if !args.is_empty() {
                self.emit(Instruction::Aload(scrutinee_slot as u8));
                self.frame.push_type(VerificationType::Object {
                    cpool_index: match scrutinee_type {
                        JvmType::StructRef(idx) => idx,
                        _ => self.refs.string_class,
                    },
                });
                self.emit(Instruction::Checkcast(variant_class_index));
                self.frame.pop_type();
                self.frame.push_type(VerificationType::Object {
                    cpool_index: variant_class_index,
                });

                let cast_slot = self.next_local;
                self.next_local += 1;
                self.emit(Instruction::Astore(cast_slot as u8));
                self.frame.pop_type();
                self.frame.local_types.push(VerificationType::Object {
                    cpool_index: variant_class_index,
                });

                for (j, sub_pat) in args.iter().enumerate() {
                    if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                        continue;
                    }
                    let (_fname, field_jvm_type, is_erased) = &fields[j];
                    let field_ref = field_refs[j];

                    self.emit(Instruction::Aload(cast_slot as u8));
                    self.frame.push_type(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });
                    self.emit(Instruction::Getfield(field_ref));
                    self.frame.pop_type();
                    if *is_erased {
                        self.frame.push_type(VerificationType::Object {
                            cpool_index: self.refs.string_class,
                        });
                    } else {
                        self.push_jvm_type(*field_jvm_type);
                    }

                    match sub_pat {
                        TypedPattern::Var { name: var_name, .. } => {
                            let actual_type = if *is_erased {
                                JvmType::StructRef(self.refs.object_class)
                            } else {
                                *field_jvm_type
                            };
                            let var_slot = self.next_local;
                            let slot_size = match actual_type {
                                JvmType::Long | JvmType::Double => 2,
                                _ => 1,
                            };
                            self.next_local += slot_size;
                            let store = match actual_type {
                                JvmType::Long => Instruction::Lstore(var_slot as u8),
                                JvmType::Double => Instruction::Dstore(var_slot as u8),
                                JvmType::Int => Instruction::Istore(var_slot as u8),
                                JvmType::Ref | JvmType::StructRef(_) => {
                                    Instruction::Astore(var_slot as u8)
                                }
                            };
                            self.emit(store);
                            self.pop_jvm_type(actual_type);
                            let vtypes = self.jvm_type_to_vtypes(actual_type);
                            self.frame.local_types.extend(vtypes);
                            self.locals
                                .insert(var_name.clone(), (var_slot, actual_type));
                        }
                        TypedPattern::Constructor { .. } => {
                            // Deeper nesting
                            let nested_type = if *is_erased {
                                JvmType::StructRef(self.get_pattern_class_index(sub_pat)?)
                            } else {
                                *field_jvm_type
                            };
                            let nested_slot = self.next_local;
                            self.next_local += 1;
                            self.emit(Instruction::Astore(nested_slot as u8));
                            self.frame.pop_type();
                            self.frame.local_types.push(VerificationType::Object {
                                cpool_index: match nested_type {
                                    JvmType::StructRef(idx) => idx,
                                    _ => self.refs.string_class,
                                },
                            });
                            self.compile_nested_pattern(
                                sub_pat,
                                nested_slot,
                                nested_type,
                                _outer_ifeq_idx,
                            )?;
                        }
                        _ => {}
                    }
                }
            }

            // The nested ifeq needs to jump to the same target as the outer one.
            // We'll store the nested index and patch it along with the outer.
            // Actually, we need to store these for patching later.
            // For now, let's use a simpler approach: store nested ifeq indices
            // and patch them all to the same target.
            // We'll store them in temporary storage on the Compiler.
            // Actually, the simplest approach: the caller (compile_match) will
            // patch the outer ifeq. We need to also patch nested ones.
            // Let's patch nested ifeq to point to a shared location.
            // We'll track these via a vec stored temporarily.
            // For simplicity, we store the patch index in the outer_ifeq slot
            // by making the nested check share the same branch target.
            // We'll record the nested_ifeq_idx for the caller to patch.
            self.nested_ifeq_patches.push(nested_ifeq_idx);

            Ok(())
        } else {
            Ok(())
        }
    }

    fn compile_do(&mut self, exprs: &[TypedExpr], in_tail: bool) -> Result<JvmType, CodegenError> {
        let mut last_type = JvmType::Int;
        for (i, expr) in exprs.iter().enumerate() {
            let is_last = i == exprs.len() - 1;
            let expr_tail = in_tail && is_last;
            let ty = self.compile_expr(expr, expr_tail)?;

            if !is_last {
                // Pop the value — it's not used
                match ty {
                    JvmType::Long | JvmType::Double => {
                        self.emit(Instruction::Pop2);
                        self.frame.pop_type_n(2);
                    }
                    _ => {
                        self.emit(Instruction::Pop);
                        self.frame.pop_type();
                    }
                }
            }
            last_type = ty;
        }
        Ok(last_type)
    }

    /// Emit a close() call for an auto-close binding via the Resource trait dispatch.
    fn emit_auto_close(
        &mut self,
        binding: &krypton_typechecker::typed_ast::AutoCloseBinding,
    ) -> Result<(), CodegenError> {
        let key = ("Resource".to_string(), binding.type_name.clone());
        let singleton = self.traits.instance_singletons.get(&key).ok_or_else(|| {
            CodegenError::TypeError(format!("no Resource instance for {}", binding.type_name))
        })?;
        let instance_field_ref = singleton.instance_field_ref;
        let dispatch =
            self.traits.trait_dispatch.get("Resource").ok_or_else(|| {
                CodegenError::TypeError("Resource trait dispatch not found".into())
            })?;
        let interface_class = dispatch.interface_class;
        let method_ref = *dispatch
            .method_refs
            .get("close")
            .ok_or_else(|| CodegenError::TypeError("close method ref not found".into()))?;

        // getstatic Resource$Type.INSTANCE
        self.emit(Instruction::Getstatic(instance_field_ref));
        self.frame.push_type(VerificationType::Object {
            cpool_index: interface_class,
        });

        // aload <resource_local>
        let (slot, _) = self
            .locals
            .get(&binding.name)
            .copied()
            .ok_or_else(|| CodegenError::UndefinedVariable(binding.name.clone()))?;
        self.emit(Instruction::Aload(slot as u8));
        self.frame.push_type(VerificationType::Object {
            cpool_index: self.refs.object_class,
        });

        // invokeinterface Resource.close, 2
        self.emit(Instruction::Invokeinterface(method_ref, 2));
        self.frame.pop_type();
        self.frame.pop_type(); // pop receiver + arg
        self.frame.push_type(VerificationType::Object {
            cpool_index: self.refs.object_class,
        });

        // pop Unit return
        self.emit(Instruction::Pop);
        self.frame.pop_type();
        Ok(())
    }

    /// Compile a function declaration into a JVM Method.
    pub(super) fn compile_function(&mut self, decl: &TypedFnDecl) -> Result<Method, CodegenError> {
        self.reset_method_state();

        // Look up the function's type info
        let info = self
            .types
            .functions
            .get(&decl.name)
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
            let slot = self.next_local;
            let jvm_ty = JvmType::StructRef(self.refs.object_class);
            self.traits
                .dict_locals
                .insert(requirement.trait_name().to_string(), slot);
            fn_params.push((slot, jvm_ty));
            self.next_local += 1;
            self.frame.local_types.push(VerificationType::Object {
                cpool_index: self.refs.object_class,
            });
        }

        // Register user parameters as locals and save fn_params for recur
        for (i, (param_name, &jvm_ty)) in decl
            .params
            .iter()
            .zip(param_types[num_dict_params..].iter())
            .enumerate()
        {
            let slot = self.next_local;
            let slot_size: u16 = match jvm_ty {
                JvmType::Long | JvmType::Double => 2,
                _ => 1,
            };
            self.locals.insert(param_name.clone(), (slot, jvm_ty));
            fn_params.push((slot, jvm_ty));
            self.next_local += slot_size;

            // Track local verification types
            let vtypes = self.jvm_type_to_vtypes(jvm_ty);
            self.frame.local_types.extend(vtypes);

            // If this param is function-typed, register in local_fn_info
            if let Some((ref tc_param_types, _)) = tc_types {
                if let Type::Fn(inner_params, inner_ret) = &tc_param_types[i] {
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
                    self.local_fn_info
                        .insert(param_name.clone(), (inner_param_jvm, inner_ret_jvm));
                }
            }
        }
        self.fn_params = fn_params;
        self.fn_return_type = Some(return_type);

        // Emit Nop as recur back-edge target at instruction 0.
        // Recur uses Goto(1) to jump to instruction 1 (after Nop), but we
        // actually target the Nop itself — no, we target instruction 1.
        // The Nop ensures the recur target (instruction 1) has byte offset > 0,
        // avoiding conflict with the implicit initial StackMapTable frame.
        self.emit(Instruction::Nop);

        // Compile function body
        let body_type = self.compile_expr(&decl.body, true)?;

        // If body type is Object but return type is primitive, unbox
        if matches!(body_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
            && !matches!(return_type, JvmType::StructRef(_) | JvmType::Ref)
        {
            self.unbox_if_needed(return_type);
        }
        // If body type is primitive but return type is Object, box
        else if matches!(return_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
            && !matches!(body_type, JvmType::StructRef(_) | JvmType::Ref)
        {
            self.box_if_needed(body_type);
        }
        // If body type is Object but return type is a specific reference type, checkcast
        else if matches!(body_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
            && matches!(return_type, JvmType::Ref | JvmType::StructRef(_))
            && !matches!(return_type, JvmType::StructRef(idx) if idx == self.refs.object_class)
        {
            let cast_class = match return_type {
                JvmType::Ref => self.refs.string_class,
                JvmType::StructRef(idx) => idx,
                _ => unreachable!(),
            };
            self.emit(Instruction::Checkcast(cast_class));
            self.frame.pop_type();
            self.frame.push_type(VerificationType::Object {
                cpool_index: cast_class,
            });
        }

        // Auto-close live resources at function exit
        if let Some(bindings) = self.auto_close.fn_exits.get(&decl.name).cloned() {
            // Save return value to temp
            let ret_slot = self.next_local;
            let ret_slot_size = match return_type {
                JvmType::Long | JvmType::Double => 2,
                _ => 1,
            };
            self.next_local += ret_slot_size;
            let ret_store = match return_type {
                JvmType::Long => Instruction::Lstore(ret_slot as u8),
                JvmType::Double => Instruction::Dstore(ret_slot as u8),
                JvmType::Int => Instruction::Istore(ret_slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Astore(ret_slot as u8),
            };
            self.emit(ret_store);
            self.pop_jvm_type(return_type);
            let vtypes = self.jvm_type_to_vtypes(return_type);
            self.frame.local_types.extend(vtypes);

            for binding in &bindings {
                self.emit_auto_close(binding)?;
            }

            // Reload return value
            let ret_load = match return_type {
                JvmType::Long => Instruction::Lload(ret_slot as u8),
                JvmType::Double => Instruction::Dload(ret_slot as u8),
                JvmType::Int => Instruction::Iload(ret_slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(ret_slot as u8),
            };
            self.emit(ret_load);
            self.push_jvm_type(return_type);
        }

        // Emit typed return
        let ret_instr = match return_type {
            JvmType::Long => Instruction::Lreturn,
            JvmType::Double => Instruction::Dreturn,
            JvmType::Int => Instruction::Ireturn,
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Areturn,
        };
        self.emit(ret_instr);

        // Build the method descriptor string for the constant pool
        let descriptor = self.types.build_descriptor(&param_types, return_type);
        let name_idx = self.cp.add_utf8(&decl.name)?;
        let desc_idx = self.cp.add_utf8(&descriptor)?;

        // Build StackMapTable
        let stack_map_frames = self.frame.build_stack_map_frames();
        let code_attributes = if stack_map_frames.is_empty() {
            vec![]
        } else {
            vec![Attribute::StackMapTable {
                name_index: self.refs.smt_name,
                frames: stack_map_frames,
            }]
        };

        Ok(Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![Attribute::Code {
                name_index: self.refs.code_utf8,
                max_stack: self.frame.max_stack(),
                max_locals: self.next_local,
                code: std::mem::take(&mut self.code),
                exception_table: vec![],
                attributes: code_attributes,
            }],
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
            name_index: self.refs.init_name,
            descriptor_index: self.refs.init_desc,
            attributes: vec![Attribute::Code {
                name_index: self.refs.code_utf8,
                max_stack: 1,
                max_locals: 1,
                code: vec![
                    Instruction::Aload_0,
                    Instruction::Invokespecial(self.refs.object_init),
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

            // Build StackMapTable if we have frames
            let stack_map_frames = self.frame.build_stack_map_frames();
            let code_attributes = if stack_map_frames.is_empty() {
                vec![]
            } else {
                vec![Attribute::StackMapTable {
                    name_index: self.refs.smt_name,
                    frames: stack_map_frames,
                }]
            };

            let main_method = Method {
                access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
                name_index: main_name,
                descriptor_index: main_desc,
                attributes: vec![Attribute::Code {
                    name_index: self.refs.code_utf8,
                    max_stack: self.frame.max_stack(),
                    max_locals: self.next_local,
                    code: std::mem::take(&mut self.code),
                    exception_table: vec![],
                    attributes: code_attributes,
                }],
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
