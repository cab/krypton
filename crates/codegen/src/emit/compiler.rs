use std::collections::{BTreeMap, HashMap};

use krypton_parser::ast::{BinOp, Lit, Pattern, UnaryOp};
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm};
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{Attribute, BootstrapMethod, Instruction, StackFrame, VerificationType};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Method,
    MethodAccessFlags, ReferenceKind,
};

use super::{JAVA_21, type_to_name, type_to_jvm_basic, jvm_type_to_field_descriptor, is_intrinsic};

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
}

/// Info about a sum type (sealed interface).
pub(super) struct SumTypeInfo {
    pub(super) interface_class_index: u16,
    pub(super) variants: HashMap<String, VariantInfo>,
}

/// Well-known constant pool indices, set once in `new()`, read-only after.
pub(super) struct CpoolRefs {
    pub(super) code_utf8: u16,
    pub(super) object_init: u16,
    pub(super) init_name: u16,
    pub(super) init_desc: u16,
    pub(super) system_out: u16,
    pub(super) println_long: u16,
    pub(super) println_string: u16,
    pub(super) println_double: u16,
    pub(super) println_bool: u16,
    pub(super) println_object: u16,
    pub(super) print_long: u16,
    pub(super) print_string: u16,
    pub(super) print_double: u16,
    pub(super) print_bool: u16,
    pub(super) print_object: u16,
    pub(super) smt_name: u16,
    pub(super) string_class: u16,
    pub(super) ps_class: u16,
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
    pub(super) string_valueof_long: u16,
    pub(super) string_valueof_double: u16,
    pub(super) string_length_ref: u16,
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
            JvmType::StructRef(idx) => vec![VerificationType::Object {
                cpool_index: idx,
            }],
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

/// Type registry for codegen (structs, sum types, functions).
pub(super) struct CodegenTypeInfo {
    pub(super) struct_info: HashMap<String, StructInfo>,
    pub(super) class_descriptors: HashMap<u16, String>,
    pub(super) sum_type_info: HashMap<String, SumTypeInfo>,
    pub(super) variant_to_sum: HashMap<String, String>,
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
    pub(super) interface_class: u16,       // class index of the trait interface in main cpool
    pub(super) method_refs: HashMap<String, u16>, // method_name → interface method_ref
}

/// Info about a trait instance singleton.
pub(super) struct InstanceSingletonInfo {
    pub(super) instance_field_ref: u16,    // field_ref for INSTANCE field (for getstatic)
}

/// Trait dispatch state for codegen.
pub(super) struct TraitState {
    pub(super) trait_dispatch: HashMap<String, TraitDispatchInfo>,
    pub(super) instance_singletons: HashMap<(String, String), InstanceSingletonInfo>,
    pub(super) trait_method_map: HashMap<String, String>,
    pub(super) fn_constraints: HashMap<String, Vec<String>>,
    pub(super) dict_locals: HashMap<String, u16>,
    pub(super) parameterized_instances: HashMap<(String, String), Vec<(String, usize)>>,
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
}

impl Compiler {
    pub(super) fn new(class_name: &str) -> Result<(Self, u16, u16), CodegenError> {
        let mut cp = ConstantPool::default();

        let this_class = cp.add_class(class_name)?;
        let object_class = cp.add_class("java/lang/Object")?;
        let code_utf8 = cp.add_utf8("Code")?;
        let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
        let init_name = cp.add_utf8("<init>")?;
        let init_desc = cp.add_utf8("()V")?;

        // System.out field ref
        let system_class = cp.add_class("java/lang/System")?;
        let system_out =
            cp.add_field_ref(system_class, "out", "Ljava/io/PrintStream;")?;

        // PrintStream.println overloads
        let ps_class = cp.add_class("java/io/PrintStream")?;
        let println_long = cp.add_method_ref(ps_class, "println", "(J)V")?;
        let println_string =
            cp.add_method_ref(ps_class, "println", "(Ljava/lang/String;)V")?;
        let println_double = cp.add_method_ref(ps_class, "println", "(D)V")?;
        let println_bool = cp.add_method_ref(ps_class, "println", "(Z)V")?;
        let println_object =
            cp.add_method_ref(ps_class, "println", "(Ljava/lang/Object;)V")?;

        // PrintStream.print overloads (no newline)
        let print_long = cp.add_method_ref(ps_class, "print", "(J)V")?;
        let print_string =
            cp.add_method_ref(ps_class, "print", "(Ljava/lang/String;)V")?;
        let print_double = cp.add_method_ref(ps_class, "print", "(D)V")?;
        let print_bool = cp.add_method_ref(ps_class, "print", "(Z)V")?;
        let print_object =
            cp.add_method_ref(ps_class, "print", "(Ljava/lang/Object;)V")?;

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
        let long_unbox =
            cp.add_method_ref(long_box_class, "longValue", "()J")?;
        let double_unbox =
            cp.add_method_ref(double_box_class, "doubleValue", "()D")?;
        let bool_unbox =
            cp.add_method_ref(bool_box_class, "booleanValue", "()Z")?;

        // String operations
        let string_concat =
            cp.add_method_ref(string_class, "concat", "(Ljava/lang/String;)Ljava/lang/String;")?;
        let string_equals =
            cp.add_method_ref(string_class, "equals", "(Ljava/lang/Object;)Z")?;

        // Intrinsic support
        let runtime_exception_class = cp.add_class("java/lang/RuntimeException")?;
        let runtime_exception_init =
            cp.add_method_ref(runtime_exception_class, "<init>", "(Ljava/lang/String;)V")?;
        let string_valueof_long =
            cp.add_method_ref(string_class, "valueOf", "(J)Ljava/lang/String;")?;
        let string_valueof_double =
            cp.add_method_ref(string_class, "valueOf", "(D)Ljava/lang/String;")?;
        let string_length_ref =
            cp.add_method_ref(string_class, "length", "()I")?;

        let compiler = Compiler {
            cp,
            this_class,
            refs: CpoolRefs {
                code_utf8,
                object_init,
                init_name,
                init_desc,
                system_out,
                println_long,
                println_string,
                println_double,
                println_bool,
                println_object,
                print_long,
                print_string,
                print_double,
                print_bool,
                print_object,
                smt_name,
                string_class,
                ps_class,
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
                string_valueof_long,
                string_valueof_double,
                string_length_ref,
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
                dict_locals: HashMap::new(),
                parameterized_instances: HashMap::new(),
            },
        };

        Ok((compiler, this_class, object_class))
    }

    /// Map a typechecker Type to a JvmType, using struct_info/sum_type_info for Named types.
    pub(super) fn type_to_jvm(&self, ty: &Type) -> Result<JvmType, CodegenError> {
        match ty {
            Type::Named(name, _) => {
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
            Type::Own(inner) => self.type_to_jvm(inner),
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

    pub(super) fn compile_expr(&mut self, expr: &TypedExpr, in_tail: bool) -> Result<JvmType, CodegenError> {
        match &expr.kind {
            TypedExprKind::Lit(value) => self.compile_lit(value),
            TypedExprKind::BinaryOp { op, lhs, rhs } => self.compile_binop(op, lhs, rhs),
            TypedExprKind::If { cond, then_, else_ } => self.compile_if(cond, then_, else_, in_tail),
            TypedExprKind::Let { name, value, body } => self.compile_let(name, value, body, in_tail),
            TypedExprKind::Var(name) => self.compile_var(name),
            TypedExprKind::Do(exprs) => self.compile_do(exprs, in_tail),
            TypedExprKind::App { func, args } => self.compile_app(func, args, &expr.ty),
            TypedExprKind::Recur(args) => self.compile_recur(args, in_tail),
            TypedExprKind::FieldAccess { expr: target, field } => self.compile_field_access(target, field),
            TypedExprKind::LetPattern { .. } => Err(CodegenError::UnsupportedExpr("let-pattern destructuring".into())),
            TypedExprKind::StructUpdate { base, fields } => self.compile_struct_update(base, fields),
            TypedExprKind::Match { scrutinee, arms } => self.compile_match(scrutinee, arms, in_tail),
            TypedExprKind::UnaryOp { op, operand } => self.compile_unaryop(op, operand),
            TypedExprKind::Lambda { params, body } => self.compile_lambda(params, body, &expr.ty),
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
                            BinOp::Add => ("Add", "add"),
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

        let dispatch = self.traits.trait_dispatch.get(trait_name)
            .ok_or_else(|| CodegenError::UndefinedVariable(format!("no trait dispatch for {trait_name}")))?;
        let iface_method_ref = *dispatch.method_refs.get(method_name)
            .ok_or_else(|| CodegenError::UndefinedVariable(format!("no method {method_name} in {trait_name}")))?;
        let iface_class = dispatch.interface_class;

        let singleton = self.traits.instance_singletons.get(&(trait_name.to_string(), type_name.clone()))
            .ok_or_else(|| CodegenError::UndefinedVariable(format!("no instance of {trait_name} for {type_name}")))?;
        let field_ref = singleton.instance_field_ref;

        // Load singleton instance
        self.emit(Instruction::Getstatic(field_ref));
        self.frame.push_type(VerificationType::Object { cpool_index: iface_class });

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
        self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });

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

        let dispatch = self.traits.trait_dispatch.get(trait_name)
            .ok_or_else(|| CodegenError::UndefinedVariable(format!("no trait dispatch for {trait_name}")))?;
        let iface_method_ref = *dispatch.method_refs.get(method_name)
            .ok_or_else(|| CodegenError::UndefinedVariable(format!("no method {method_name} in {trait_name}")))?;
        let iface_class = dispatch.interface_class;

        let singleton = self.traits.instance_singletons.get(&(trait_name.to_string(), type_name.clone()))
            .ok_or_else(|| CodegenError::UndefinedVariable(format!("no instance of {trait_name} for {type_name}")))?;
        let field_ref = singleton.instance_field_ref;

        // Load singleton instance
        self.emit(Instruction::Getstatic(field_ref));
        self.frame.push_type(VerificationType::Object { cpool_index: iface_class });

        // Compile and box operand
        let op_jvm = self.compile_expr(operand, false)?;
        self.box_if_needed(op_jvm);

        // invokeinterface (receiver + 1 arg = 2)
        self.emit(Instruction::Invokeinterface(iface_method_ref, 2));
        self.frame.pop_type(); // operand
        self.frame.pop_type(); // receiver
        self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });

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
                BinOp::Eq  => ("Eq",  "eq", false, false),
                BinOp::Neq => ("Eq",  "eq", false, true),
                BinOp::Lt  => ("Ord", "lt", false, false),
                BinOp::Gt  => ("Ord", "lt", true,  false),
                BinOp::Le  => ("Ord", "lt", true,  true),
                BinOp::Ge  => ("Ord", "lt", false, true),
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
                _ => {
                    self.compile_trait_unaryop("Neg", "neg", operand, operand_jvm)
                }
            },
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

        // Compile then branch
        let then_type = self.compile_expr(then_, in_tail)?;
        let stack_after_then = self.frame.stack_types.clone();

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
    ) -> Result<JvmType, CodegenError> {
        // Check if the value is a lambda — record its type info for higher-order calls
        let is_lambda = matches!(value.kind, TypedExprKind::Lambda { .. });

        let ty = self.compile_expr(value, false)?;
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

        // If the value was a lambda, record local_fn_info from the TypedExpr's type
        if is_lambda {
            let fn_type = match &value.ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            if let Type::Fn(param_types, ret_type) = fn_type {
                let param_jvm: Result<Vec<JvmType>, _> = param_types.iter().map(|t| self.type_to_jvm(t)).collect();
                if let Ok(param_jvm) = param_jvm {
                    if let Ok(ret_jvm) = self.type_to_jvm(ret_type) {
                        self.local_fn_info.insert(name.to_string(), (param_jvm, ret_jvm));
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
            Ok(JvmType::Int)
        }
    }

    fn compile_var(&mut self, name: &str) -> Result<JvmType, CodegenError> {
        // Check if this is a nullary variant constructor
        if let Some(sum_name) = self.types.variant_to_sum.get(name).cloned() {
            let sum_info = &self.types.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            if vi.fields.is_empty() {
                let class_index = vi.class_index;
                let constructor_ref = vi.constructor_ref;
                let interface_class_index = sum_info.interface_class_index;
                self.emit(Instruction::New(class_index));
                self.frame.push_type(VerificationType::UninitializedThis);
                self.emit(Instruction::Dup);
                self.frame.push_type(VerificationType::UninitializedThis);
                self.emit(Instruction::Invokespecial(constructor_ref));
                self.frame.pop_type(); // dup'd uninit
                self.frame.pop_type(); // original uninit
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

    fn compile_print_intrinsic(&mut self, args: &[TypedExpr], use_println: bool) -> Result<JvmType, CodegenError> {
        // getstatic System.out
        self.emit(Instruction::Getstatic(self.refs.system_out));
        self.frame.push_type(VerificationType::Object { cpool_index: self.refs.ps_class });

        // Compile the single argument
        let arg_type = self.compile_expr(&args[0], false)?;

        // Select the right print/println overload
        let method_ref = if use_println {
            match arg_type {
                JvmType::Long => self.refs.println_long,
                JvmType::Double => self.refs.println_double,
                JvmType::Ref => self.refs.println_string,
                JvmType::Int => self.refs.println_bool,
                JvmType::StructRef(_) => self.refs.println_object,
            }
        } else {
            match arg_type {
                JvmType::Long => self.refs.print_long,
                JvmType::Double => self.refs.print_double,
                JvmType::Ref => self.refs.print_string,
                JvmType::Int => self.refs.print_bool,
                JvmType::StructRef(_) => self.refs.print_object,
            }
        };

        self.emit(Instruction::Invokevirtual(method_ref));
        self.pop_jvm_type(arg_type); // pop the argument
        self.frame.pop_type(); // pop PrintStream

        // Unit = iconst_0 (bool false)
        self.emit(Instruction::Iconst_0);
        self.frame.push_type(VerificationType::Integer);
        Ok(JvmType::Int)
    }

    fn compile_intrinsic(&mut self, name: &str, args: &[TypedExpr], result_ty: &Type) -> Result<JvmType, CodegenError> {
        match name {
            "println" => self.compile_print_intrinsic(args, true),
            "print" => self.compile_print_intrinsic(args, false),
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
            "to_float" => {
                self.compile_expr(&args[0], false)?;
                self.emit(Instruction::L2d);
                self.frame.pop_type_n(2); // Long + Top
                self.frame.push_double_type();
                Ok(JvmType::Double)
            }
            "to_int" => {
                self.compile_expr(&args[0], false)?;
                self.emit(Instruction::D2l);
                self.frame.pop_type_n(2); // Double + Top
                self.frame.push_long_type();
                Ok(JvmType::Long)
            }
            "int_to_string" => {
                self.compile_expr(&args[0], false)?;
                let ref_idx = self.refs.string_valueof_long;
                self.emit(Instruction::Invokestatic(ref_idx));
                self.frame.pop_type_n(2); // Long + Top
                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.string_class });
                Ok(JvmType::Ref)
            }
            "float_to_string" => {
                self.compile_expr(&args[0], false)?;
                let ref_idx = self.refs.string_valueof_double;
                self.emit(Instruction::Invokestatic(ref_idx));
                self.frame.pop_type_n(2); // Double + Top
                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.string_class });
                Ok(JvmType::Ref)
            }
            "string_concat" => {
                // First string (receiver)
                self.compile_expr(&args[0], false)?;
                // Second string (argument)
                self.compile_expr(&args[1], false)?;
                let concat_ref = self.refs.string_concat;
                self.emit(Instruction::Invokevirtual(concat_ref));
                self.frame.pop_type(); // second string
                self.frame.pop_type(); // first string (receiver)
                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.string_class });
                Ok(JvmType::Ref)
            }
            "string_length" => {
                self.compile_expr(&args[0], false)?;
                let len_ref = self.refs.string_length_ref;
                self.emit(Instruction::Invokevirtual(len_ref));
                self.frame.pop_type(); // string
                self.frame.push_type(VerificationType::Integer);
                // Convert int to long (Krypton Int = JVM long)
                self.emit(Instruction::I2l);
                self.frame.pop_type(); // int
                self.frame.push_long_type();
                Ok(JvmType::Long)
            }
            _ => Err(CodegenError::UnsupportedExpr(format!("unknown intrinsic: {name}"))),
        }
    }

    fn compile_app(&mut self, func: &TypedExpr, args: &[TypedExpr], result_ty: &Type) -> Result<JvmType, CodegenError> {
        let name = match &func.kind {
            TypedExprKind::Var(name) => name.as_str(),
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
                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });
                // Unbox if needed
                self.unbox_if_needed(ho_ret_type);
                // Checkcast Object → specific ref type if needed
                match ho_ret_type {
                    JvmType::Ref => {
                        self.emit(Instruction::Checkcast(self.refs.string_class));
                        self.frame.pop_type();
                        self.frame.push_type(VerificationType::Object { cpool_index: self.refs.string_class });
                    }
                    JvmType::StructRef(idx) if idx != self.refs.object_class => {
                        self.emit(Instruction::Checkcast(idx));
                        self.frame.pop_type();
                        self.frame.push_type(VerificationType::Object { cpool_index: idx });
                    }
                    _ => {}
                }
                return Ok(ho_ret_type);
            }
        }

        // Check if this is a trait method call
        if let Some(trait_name) = self.traits.trait_method_map.get(name).cloned() {
            if let Some(dispatch) = self.traits.trait_dispatch.get(&trait_name) {
                let iface_method_ref = dispatch.method_refs[name];
                let iface_class = dispatch.interface_class;

                // Determine the concrete type from the first arg's type in the typechecker
                let first_arg_ty = &args[0].ty;
                let is_type_var = matches!(first_arg_ty, Type::Var(_));

                // Load the dictionary (trait interface reference)
                if is_type_var {
                    // Load dict from local variable (constrained function's dict param)
                    if let Some(&dict_slot) = self.traits.dict_locals.get(&trait_name) {
                        self.emit(Instruction::Aload(dict_slot as u8));
                        self.frame.push_type(VerificationType::Object { cpool_index: iface_class });
                    } else {
                        return Err(CodegenError::UndefinedVariable(
                            format!("no dict local for trait {trait_name}"),
                        ));
                    }
                } else {
                    // Concrete type — getstatic Instance.INSTANCE or construct parameterized
                    let type_name = type_to_name(first_arg_ty);
                    if let Some(singleton) = self.traits.instance_singletons.get(&(trait_name.clone(), type_name.clone())) {
                        let field_ref = singleton.instance_field_ref;
                        self.emit(Instruction::Getstatic(field_ref));
                        self.frame.push_type(VerificationType::Object { cpool_index: iface_class });
                    } else if let Some(subdict_traits) = self.traits.parameterized_instances.get(&(trait_name.clone(), type_name.clone())).cloned() {
                        // Construct parameterized instance on the fly
                        let instance_class_name = format!("{}${}", trait_name, type_name);
                        let inst_class = self.cp.add_class(&instance_class_name)?;
                        // Constructor descriptor: (Object * subdict_count)V
                        let mut init_desc = String::from("(");
                        for _ in &subdict_traits {
                            init_desc.push_str("Ljava/lang/Object;");
                        }
                        init_desc.push_str(")V");
                        let init_ref = self.cp.add_method_ref(inst_class, "<init>", &init_desc)?;
                        self.emit(Instruction::New(inst_class));
                        self.frame.push_type(VerificationType::Object { cpool_index: inst_class });
                        self.emit(Instruction::Dup);
                        self.frame.push_type(VerificationType::Object { cpool_index: inst_class });
                        // Push subdictionaries
                        for (subdict_trait, param_idx) in &subdict_traits {
                            // Resolve the type arg at param_idx
                            let type_arg = match first_arg_ty {
                                Type::Named(_, type_args) => &type_args[*param_idx],
                                Type::Own(inner) => {
                                    if let Type::Named(_, type_args) = inner.as_ref() { &type_args[*param_idx] } else { first_arg_ty }
                                }
                                _ => first_arg_ty,
                            };
                            let sub_type_name = type_to_name(type_arg);
                            if let Some(singleton) = self.traits.instance_singletons.get(&(subdict_trait.clone(), sub_type_name.clone())) {
                                let field_ref = singleton.instance_field_ref;
                                self.emit(Instruction::Getstatic(field_ref));
                                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });
                            } else {
                                return Err(CodegenError::UndefinedVariable(
                                    format!("no instance of {subdict_trait} for {sub_type_name}"),
                                ));
                            }
                        }
                        self.emit(Instruction::Invokespecial(init_ref));
                        // Pop subdict args + dup from stack, leave one instance ref
                        for _ in &subdict_traits {
                            self.frame.pop_type();
                        }
                        self.frame.pop_type(); // dup
                    } else {
                        return Err(CodegenError::UndefinedVariable(
                            format!("no instance of {trait_name} for {type_name}"),
                        ));
                    }
                }

                // Compile and box all arguments
                let arity = args.len();
                for arg in args {
                    let arg_type = self.compile_expr(arg, false)?;
                    self.box_if_needed(arg_type);
                }

                // invokeinterface
                self.emit(Instruction::Invokeinterface(iface_method_ref, (arity + 1) as u8));

                // Pop args + receiver from stack tracker
                for _ in 0..arity {
                    self.frame.pop_type(); // each boxed arg
                }
                self.frame.pop_type(); // receiver (dict)

                // Push Object result
                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });

                // Determine expected return type from the interface method
                // The return type is always Object from the interface — need to unbox
                // based on expected result type. Look at the expr's type.
                let result_jvm = self.type_to_jvm(&func.ty).unwrap_or(JvmType::StructRef(self.refs.object_class));
                let expected_ret = if let Type::Fn(_, ret) = &func.ty {
                    self.type_to_jvm(ret).unwrap_or(JvmType::StructRef(self.refs.object_class))
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
                        self.frame.push_type(VerificationType::Object { cpool_index: self.refs.string_class });
                    }
                    JvmType::StructRef(idx) if idx != self.refs.object_class => {
                        self.emit(Instruction::Checkcast(idx));
                        self.frame.pop_type();
                        self.frame.push_type(VerificationType::Object { cpool_index: idx });
                    }
                    _ => {}
                }

                return Ok(expected_ret);
            }
        }

        // Check if calling a constrained function — need to prepend dict args
        let constraint_traits = self.traits.fn_constraints.get(name).cloned().unwrap_or_default();

        // Look up function info (need to clone out to avoid borrow conflict)
        let info = self.types
            .functions
            .get(name)
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;
        let method_ref = info.method_ref;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;
        let is_void = info.is_void;

        // Push dict args first for constrained functions
        if !constraint_traits.is_empty() {
            for trait_name in &constraint_traits {
                // Determine concrete type from the first user arg
                // (same logic as trait method dispatch)
                if !args.is_empty() {
                    let first_arg_ty = &args[0].ty;
                    let is_type_var = matches!(first_arg_ty, Type::Var(_));
                    if is_type_var {
                        // Forward our own dict local
                        if let Some(&dict_slot) = self.traits.dict_locals.get(trait_name) {
                            self.emit(Instruction::Aload(dict_slot as u8));
                            self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });
                        }
                    } else {
                        let type_name = type_to_name(first_arg_ty);
                        if let Some(singleton) = self.traits.instance_singletons.get(&(trait_name.clone(), type_name)) {
                            let field_ref = singleton.instance_field_ref;
                            self.emit(Instruction::Getstatic(field_ref));
                            self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });
                        }
                    }
                }
            }
        }

        // Compile each argument, boxing if needed for erased type params
        let dict_offset = constraint_traits.len();
        for (i, arg) in args.iter().enumerate() {
            let arg_type = self.compile_expr(arg, false)?;
            if let JvmType::StructRef(idx) = param_types[i + dict_offset] {
                if idx == self.refs.object_class && !matches!(arg_type, JvmType::StructRef(_) | JvmType::Ref) {
                    self.box_if_needed(arg_type);
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
        let (_struct_name, accessor_ref, field_type) = {
            let si = self.types
                .struct_info
                .values()
                .find(|s| s.class_index == class_idx)
                .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
            let accessor_ref = *si.accessor_refs.get(field).ok_or_else(|| {
                CodegenError::TypeError(format!("unknown field: {field}"))
            })?;
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
        let si = self.types
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

    fn compile_recur(
        &mut self,
        args: &[TypedExpr],
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        if !in_tail {
            return Err(CodegenError::RecurNotInTailPosition);
        }
        let return_type = self.fn_return_type.ok_or_else(|| {
            CodegenError::UnsupportedExpr("recur outside function".to_string())
        })?;
        let fn_params = self.fn_params.clone();

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
        self.frame.frames.insert(1, (
            initial_locals.iter().filter(|vt| !matches!(vt, VerificationType::Top)).cloned().collect(),
            vec![],
        ));

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
            Type::Fn(param_types, _) => {
                param_types.iter().map(|t| self.type_to_jvm(t)).collect::<Result<Vec<_>, _>>()?
            }
            _ => return Err(CodegenError::TypeError("lambda has non-function type".to_string())),
        };

        // Ensure FunN interface exists
        self.lambda.ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
        let fun_class_idx = self.lambda.fun_classes[&arity];

        // Find captured variables: scan body for Var names that are in self.locals but not lambda params
        let param_names: std::collections::HashSet<&str> = params.iter().map(|s| s.as_str()).collect();
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
            self.frame.local_types.push(VerificationType::Object { cpool_index: self.refs.object_class });
            self.next_local += 1;
        }

        // Register lambda params (all as Object, will unbox)
        let mut lambda_param_slots = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let slot = self.next_local;
            // Store as Object initially
            self.locals.insert(p.clone(), (slot, JvmType::StructRef(self.refs.object_class)));
            self.frame.local_types.push(VerificationType::Object { cpool_index: self.refs.object_class });
            lambda_param_slots.push((slot, param_jvm_types[i]));
            self.next_local += 1;
        }

        // Unbox params from Object to actual types
        for (i, p) in params.iter().enumerate() {
            let actual_type = param_jvm_types[i];
            if matches!(actual_type, JvmType::Long | JvmType::Double | JvmType::Int) {
                let slot = lambda_param_slots[i].0;
                // Load the Object param
                self.emit(Instruction::Aload(slot as u8));
                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });
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

        // Also unbox captured vars if they are primitive types
        for (cap_name, _, cap_type) in &captures {
            let actual_type = *cap_type;
            if matches!(actual_type, JvmType::Long | JvmType::Double | JvmType::Int) {
                let (slot, _) = self.locals[cap_name];
                self.emit(Instruction::Aload(slot as u8));
                self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });
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
                self.locals.insert(cap_name.clone(), (new_slot, actual_type));
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
            access_flags: MethodAccessFlags::PRIVATE | MethodAccessFlags::STATIC | MethodAccessFlags::SYNTHETIC,
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
        let lambda_impl_ref = self.cp.add_method_ref(this_class, &lambda_name, &lambda_desc)?;
        let lambda_impl_handle = self.cp.add_method_handle(ReferenceKind::InvokeStatic, lambda_impl_ref)?;

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

        let indy_idx = self.cp.add_invoke_dynamic(bsm_index, "apply", &callsite_desc)?;

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
        match &expr.kind {
            TypedExprKind::Var(name) => {
                if !param_names.contains(name.as_str()) {
                    if let Some(&(slot, ty)) = self.locals.get(name) {
                        captures.push((name.clone(), slot, ty));
                    }
                }
            }
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                self.collect_captures(lhs, param_names, captures);
                self.collect_captures(rhs, param_names, captures);
            }
            TypedExprKind::UnaryOp { operand, .. } => {
                self.collect_captures(operand, param_names, captures);
            }
            TypedExprKind::If { cond, then_, else_ } => {
                self.collect_captures(cond, param_names, captures);
                self.collect_captures(then_, param_names, captures);
                self.collect_captures(else_, param_names, captures);
            }
            TypedExprKind::Let { value, body, .. } | TypedExprKind::LetPattern { value, body, .. } => {
                self.collect_captures(value, param_names, captures);
                if let Some(body) = body {
                    self.collect_captures(body, param_names, captures);
                }
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs {
                    self.collect_captures(e, param_names, captures);
                }
            }
            TypedExprKind::App { func, args } => {
                self.collect_captures(func, param_names, captures);
                for a in args {
                    self.collect_captures(a, param_names, captures);
                }
            }
            TypedExprKind::Lambda { body, params } => {
                let mut inner_params = param_names.clone();
                for p in params {
                    inner_params.insert(p.as_str());
                }
                self.collect_captures(body, &inner_params, captures);
            }
            TypedExprKind::Match { scrutinee, arms } => {
                self.collect_captures(scrutinee, param_names, captures);
                for arm in arms {
                    self.collect_captures(&arm.body, param_names, captures);
                }
            }
            TypedExprKind::FieldAccess { expr, .. } => {
                self.collect_captures(expr, param_names, captures);
            }
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    self.collect_captures(e, param_names, captures);
                }
            }
            TypedExprKind::StructUpdate { base, fields } => {
                self.collect_captures(base, param_names, captures);
                for (_, e) in fields {
                    self.collect_captures(e, param_names, captures);
                }
            }
            TypedExprKind::Tuple(elems) => {
                for e in elems {
                    self.collect_captures(e, param_names, captures);
                }
            }
            TypedExprKind::Recur(args) => {
                for a in args {
                    self.collect_captures(a, param_names, captures);
                }
            }
            TypedExprKind::Lit(_) => {}
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
                self.compile_pattern_check(&arm.pattern, scrutinee_slot, scrutinee_type)?
            } else {
                // Last arm: bind pattern variables but no branch check
                self.compile_pattern_bind(&arm.pattern, scrutinee_slot, scrutinee_type)?;
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
                self.frame.push_type(VerificationType::Object { cpool_index: cast_class });
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
        pattern: &Pattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
    ) -> Result<Option<usize>, CodegenError> {
        match pattern {
            Pattern::Constructor { name, args, .. } => {
                // Look up variant info
                let sum_name = self.types.variant_to_sum.get(name).cloned().ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown variant: {name}"))
                })?;
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
                        if matches!(sub_pat, Pattern::Wildcard { .. }) {
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
                            Pattern::Var { name: var_name, .. } => {
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
                            Pattern::Constructor { .. } => {
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
                            Pattern::Wildcard { .. } => {
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
            Pattern::Wildcard { .. } => {
                // Always matches, no check needed
                Ok(None)
            }
            Pattern::Var { name, .. } => {
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
            _ => Err(CodegenError::UnsupportedExpr(format!(
                "unsupported pattern in check: {pattern:?}"
            ))),
        }
    }

    /// Bind pattern variables without emitting checks (for last arm / wildcard).
    fn compile_pattern_bind(
        &mut self,
        pattern: &Pattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
    ) -> Result<(), CodegenError> {
        match pattern {
            Pattern::Wildcard { .. } => Ok(()),
            Pattern::Var { name, .. } => {
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
            Pattern::Constructor { name, args, .. } => {
                // Last arm constructor — still need to extract fields
                let sum_name = self.types.variant_to_sum.get(name).cloned().ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown variant: {name}"))
                })?;
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
                        if matches!(sub_pat, Pattern::Wildcard { .. }) {
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

                        if let Pattern::Var { name: var_name, .. } = sub_pat {
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
                            self.locals.insert(var_name.clone(), (var_slot, actual_type));
                        }
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
    fn get_pattern_class_index(&self, pattern: &Pattern) -> Result<u16, CodegenError> {
        match pattern {
            Pattern::Constructor { name, .. } => {
                let sum_name = self.types.variant_to_sum.get(name).ok_or_else(|| {
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
        pattern: &Pattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
        _outer_ifeq_idx: usize,
    ) -> Result<(), CodegenError> {
        if let Pattern::Constructor { name, args, .. } = pattern {
            let sum_name = self.types.variant_to_sum.get(name).cloned().ok_or_else(|| {
                CodegenError::TypeError(format!("unknown variant: {name}"))
            })?;
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
                    if matches!(sub_pat, Pattern::Wildcard { .. }) {
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
                        Pattern::Var { name: var_name, .. } => {
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
                            self.locals.insert(var_name.clone(), (var_slot, actual_type));
                        }
                        Pattern::Constructor { .. } => {
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
            let is_let_stmt =
                matches!(expr.kind, TypedExprKind::Let { body: None, .. } | TypedExprKind::LetPattern { body: None, .. });

            let expr_tail = in_tail && is_last;
            let ty = self.compile_expr(expr, expr_tail)?;

            if !is_last && !is_let_stmt {
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

    /// Compile a function declaration into a JVM Method.
    pub(super) fn compile_function(&mut self, decl: &TypedFnDecl) -> Result<Method, CodegenError> {
        self.reset_method_state();

        // Look up the function's type info
        let info = self.types.functions.get(&decl.name).ok_or_else(|| {
            CodegenError::UndefinedVariable(decl.name.clone())
        })?;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;

        // Get typechecker types for this function's params (for detecting Fn-typed params)
        let tc_types = self.types.fn_tc_types.get(&decl.name).cloned();

        // Register dict params for constrained functions (leading params before user params)
        let constraint_traits = self.traits.fn_constraints.get(&decl.name).cloned().unwrap_or_default();
        let num_dict_params = constraint_traits.len();
        let mut fn_params = Vec::new();
        for trait_name in &constraint_traits {
            let slot = self.next_local;
            let jvm_ty = JvmType::StructRef(self.refs.object_class);
            self.traits.dict_locals.insert(trait_name.clone(), slot);
            fn_params.push((slot, jvm_ty));
            self.next_local += 1;
            self.frame.local_types.push(VerificationType::Object { cpool_index: self.refs.object_class });
        }

        // Register user parameters as locals and save fn_params for recur
        for (i, (param_name, &jvm_ty)) in decl.params.iter().zip(param_types[num_dict_params..].iter()).enumerate() {
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
                    self.lambda.ensure_fun_interface(arity, &mut self.cp, &mut self.types.class_descriptors)?;
                    self.local_fn_info.insert(param_name.clone(), (inner_param_jvm, inner_ret_jvm));
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
            self.frame.push_type(VerificationType::Object { cpool_index: cast_class });
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
    ) -> Result<Vec<u8>, CodegenError> {
        let main_name = self.cp.add_utf8("main")?;
        let main_desc = self.cp.add_utf8("([Ljava/lang/String;)V")?;

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

        let mut methods = vec![constructor];
        methods.extend(extra_methods);
        // Add lambda methods
        methods.extend(std::mem::take(&mut self.lambda.lambda_methods));
        methods.push(main_method);

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
