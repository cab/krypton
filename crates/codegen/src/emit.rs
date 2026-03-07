use std::collections::{BTreeMap, HashMap};

use krypton_parser::ast::{BinOp, Decl, Lit, Module, Pattern, TypeDeclKind, TypeExpr, UnaryOp};
use krypton_typechecker::infer::infer_module;
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm};
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{Attribute, BootstrapMethod, Instruction, StackFrame, VerificationType};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Field, FieldAccessFlags, FieldType, Method,
    MethodAccessFlags, ReferenceKind, Version,
};

/// Java 21 class file version (major 65).
const JAVA_21: Version = Version::Java21 { minor: 0 };

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
struct FunctionInfo {
    method_ref: u16,
    param_types: Vec<JvmType>,
    return_type: JvmType,
}

/// Info about a struct type for codegen.
struct StructInfo {
    class_index: u16,
    class_name: String,
    fields: Vec<(String, JvmType)>,
    constructor_ref: u16,
    accessor_refs: HashMap<String, u16>,
}

/// Info about a single variant of a sum type.
struct VariantInfo {
    class_index: u16,
    class_name: String,
    fields: Vec<(String, JvmType, bool)>, // (name, jvm_type, is_erased)
    constructor_ref: u16,
    field_refs: Vec<u16>, // field ref indices in main cpool
}

/// Info about a sum type (sealed interface).
struct SumTypeInfo {
    interface_class_index: u16,
    variants: HashMap<String, VariantInfo>,
}

/// Extract the type name from a Type for instance lookup.
fn type_to_name(ty: &Type) -> String {
    match ty {
        Type::Named(name, _) => name.clone(),
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Own(inner) => type_to_name(inner),
        other => format!("{other:?}"),
    }
}

fn type_to_jvm_basic(ty: &Type) -> Result<JvmType, CodegenError> {
    match ty {
        Type::Int => Ok(JvmType::Long),
        Type::Float => Ok(JvmType::Double),
        Type::Bool => Ok(JvmType::Int),
        Type::String => Ok(JvmType::Ref),
        Type::Unit => Ok(JvmType::Int),
        other => Err(CodegenError::TypeError(format!(
            "cannot map type to JVM: {other:?}"
        ))),
    }
}

fn jvm_type_to_field_descriptor(ty: JvmType) -> String {
    match ty {
        JvmType::Long => "J".to_string(),
        JvmType::Double => "D".to_string(),
        JvmType::Int => "Z".to_string(),
        JvmType::Ref => "Ljava/lang/String;".to_string(),
        JvmType::StructRef(_) => unreachable!("StructRef descriptor handled by caller"),
    }
}

fn jvm_type_to_base_field_type(ty: JvmType) -> FieldType {
    match ty {
        JvmType::Long => FieldType::Base(ristretto_classfile::BaseType::Long),
        JvmType::Double => FieldType::Base(ristretto_classfile::BaseType::Double),
        JvmType::Int => FieldType::Base(ristretto_classfile::BaseType::Boolean),
        JvmType::Ref => FieldType::Object("java/lang/String".to_string()),
        JvmType::StructRef(_) => unreachable!("StructRef field type handled by caller"),
    }
}

/// Well-known constant pool indices, set once in `new()`, read-only after.
struct CpoolRefs {
    code_utf8: u16,
    object_init: u16,
    init_name: u16,
    init_desc: u16,
    system_out: u16,
    println_long: u16,
    println_string: u16,
    println_double: u16,
    println_bool: u16,
    println_object: u16,
    smt_name: u16,
    string_class: u16,
    ps_class: u16,
    long_box_valueof: u16,
    double_box_valueof: u16,
    bool_box_valueof: u16,
    long_box_class: u16,
    long_unbox: u16,
    double_box_class: u16,
    double_unbox: u16,
    bool_box_class: u16,
    bool_unbox: u16,
    object_class: u16,
}

/// StackMapTable / verification type tracking.
struct FrameState {
    stack_types: Vec<VerificationType>,
    local_types: Vec<VerificationType>,
    frames: BTreeMap<u16, (Vec<VerificationType>, Vec<VerificationType>)>,
}

impl FrameState {
    fn push_type(&mut self, vt: VerificationType) {
        self.stack_types.push(vt);
    }

    fn push_long_type(&mut self) {
        self.stack_types.push(VerificationType::Long);
        self.stack_types.push(VerificationType::Top);
    }

    fn push_double_type(&mut self) {
        self.stack_types.push(VerificationType::Double);
        self.stack_types.push(VerificationType::Top);
    }

    fn pop_type(&mut self) {
        self.stack_types.pop();
    }

    fn pop_type_n(&mut self, n: usize) {
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
    }
}

/// Lambda/closure compilation state.
struct LambdaState {
    lambda_counter: u16,
    lambda_methods: Vec<Method>,
    bootstrap_methods: Vec<BootstrapMethod>,
    metafactory_handle: Option<u16>,
    fun_classes: HashMap<u8, u16>,
    fun_apply_refs: HashMap<u8, u16>,
}

impl LambdaState {
    fn ensure_fun_interface(
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
struct CodegenTypeInfo {
    struct_info: HashMap<String, StructInfo>,
    class_descriptors: HashMap<u16, String>,
    sum_type_info: HashMap<String, SumTypeInfo>,
    variant_to_sum: HashMap<String, String>,
    functions: HashMap<String, FunctionInfo>,
    fn_tc_types: HashMap<String, (Vec<Type>, Type)>,
}

impl CodegenTypeInfo {
    fn jvm_type_descriptor(&self, ty: JvmType) -> String {
        match ty {
            JvmType::StructRef(idx) => self.class_descriptors[&idx].clone(),
            other => jvm_type_to_field_descriptor(other),
        }
    }

    fn build_descriptor(&self, params: &[JvmType], ret: JvmType) -> String {
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
struct TraitDispatchInfo {
    interface_class: u16,       // class index of the trait interface in main cpool
    method_refs: HashMap<String, u16>, // method_name → interface method_ref
}

/// Info about a trait instance singleton.
struct InstanceSingletonInfo {
    instance_field_ref: u16,    // field_ref for INSTANCE field (for getstatic)
}

struct Compiler {
    cp: ConstantPool,
    this_class: u16,
    refs: CpoolRefs,
    frame: FrameState,
    lambda: LambdaState,
    types: CodegenTypeInfo,
    code: Vec<Instruction>,
    locals: HashMap<String, (u16, JvmType)>,
    next_local: u16,
    fn_params: Vec<(u16, JvmType)>,
    fn_return_type: Option<JvmType>,
    nested_ifeq_patches: Vec<usize>,
    local_fn_info: HashMap<String, (Vec<JvmType>, JvmType)>,
    // Trait dispatch info
    trait_dispatch: HashMap<String, TraitDispatchInfo>,           // trait_name → dispatch info
    instance_singletons: HashMap<(String, String), InstanceSingletonInfo>, // (trait, type) → singleton
    trait_method_map: HashMap<String, String>,                    // method_name → trait_name
    fn_constraints: HashMap<String, Vec<String>>,                 // fn_name → [trait_names]
    dict_locals: HashMap<String, u16>,                            // trait_name → local slot (per-method)
}

impl Compiler {
    fn new(class_name: &str) -> Result<(Self, u16, u16), CodegenError> {
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
            },
            frame: FrameState {
                stack_types: Vec::new(),
                local_types: vec![VerificationType::Object {
                    cpool_index: string_arr_class,
                }],
                frames: BTreeMap::new(),
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
            trait_dispatch: HashMap::new(),
            instance_singletons: HashMap::new(),
            trait_method_map: HashMap::new(),
            fn_constraints: HashMap::new(),
            dict_locals: HashMap::new(),
        };

        Ok((compiler, this_class, object_class))
    }

    /// Map a typechecker Type to a JvmType, using struct_info/sum_type_info for Named types.
    fn type_to_jvm(&self, ty: &Type) -> Result<JvmType, CodegenError> {
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
    fn reset_method_state(&mut self) {
        self.code.clear();
        self.locals.clear();
        self.next_local = 0;
        self.frame.reset();
        self.fn_params.clear();
        self.fn_return_type = None;
        self.local_fn_info.clear();
        self.dict_locals.clear();
    }

    fn emit(&mut self, instr: Instruction) {
        self.code.push(instr);
    }

    // Convenience delegators to FrameState (avoid passing string_class everywhere)
    fn push_jvm_type(&mut self, ty: JvmType) {
        self.frame.push_jvm_type(ty, self.refs.string_class);
    }

    fn pop_jvm_type(&mut self, ty: JvmType) {
        self.frame.pop_jvm_type(ty);
    }

    fn jvm_type_to_vtypes(&self, ty: JvmType) -> Vec<VerificationType> {
        self.frame.jvm_type_to_vtypes(ty, self.refs.string_class)
    }

    fn compile_expr(&mut self, expr: &TypedExpr, in_tail: bool) -> Result<JvmType, CodegenError> {
        match &expr.kind {
            TypedExprKind::Lit(value) => self.compile_lit(value),
            TypedExprKind::BinaryOp { op, lhs, rhs } => self.compile_binop(op, lhs, rhs),
            TypedExprKind::If { cond, then_, else_ } => self.compile_if(cond, then_, else_, in_tail),
            TypedExprKind::Let { name, value, body } => self.compile_let(name, value, body, in_tail),
            TypedExprKind::Var(name) => self.compile_var(name),
            TypedExprKind::Do(exprs) => self.compile_do(exprs, in_tail),
            TypedExprKind::App { func, args } => self.compile_app(func, args),
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
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                let lhs_ty = self.compile_expr(lhs, false)?;
                self.compile_expr(rhs, false)?;
                match lhs_ty {
                    JvmType::Long => {
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
                    _ => Err(CodegenError::UnsupportedExpr("arithmetic on non-numeric type".into())),
                }
            }
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.compile_comparison(op, lhs, rhs)
            }
        }
    }

    fn compile_comparison(
        &mut self,
        op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
    ) -> Result<JvmType, CodegenError> {
        let lhs_ty = self.compile_expr(lhs, false)?;
        self.compile_expr(rhs, false)?;

        let cmp_instr = match lhs_ty {
            JvmType::Long => Instruction::Lcmp,
            JvmType::Double => Instruction::Dcmpl,
            _ => return Err(CodegenError::UnsupportedExpr("comparison of non-numeric type".into())),
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
        let operand_ty = self.compile_expr(operand, false)?;
        match op {
            UnaryOp::Neg => match operand_ty {
                JvmType::Long => {
                    self.emit(Instruction::Lneg);
                    Ok(JvmType::Long)
                }
                JvmType::Double => {
                    self.emit(Instruction::Dneg);
                    Ok(JvmType::Double)
                }
                _ => Err(CodegenError::UnsupportedExpr("negation of non-numeric type".into())),
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

    fn compile_app(&mut self, func: &TypedExpr, args: &[TypedExpr]) -> Result<JvmType, CodegenError> {
        let name = match &func.kind {
            TypedExprKind::Var(name) => name.as_str(),
            other => {
                return Err(CodegenError::UnsupportedExpr(format!(
                    "non-variable function call: {other:?}"
                )))
            }
        };

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
        if let Some(trait_name) = self.trait_method_map.get(name).cloned() {
            if let Some(dispatch) = self.trait_dispatch.get(&trait_name) {
                let iface_method_ref = dispatch.method_refs[name];
                let iface_class = dispatch.interface_class;

                // Determine the concrete type from the first arg's type in the typechecker
                let first_arg_ty = &args[0].ty;
                let is_type_var = matches!(first_arg_ty, Type::Var(_));

                // Load the dictionary (trait interface reference)
                if is_type_var {
                    // Load dict from local variable (constrained function's dict param)
                    if let Some(&dict_slot) = self.dict_locals.get(&trait_name) {
                        self.emit(Instruction::Aload(dict_slot as u8));
                        self.frame.push_type(VerificationType::Object { cpool_index: iface_class });
                    } else {
                        return Err(CodegenError::UndefinedVariable(
                            format!("no dict local for trait {trait_name}"),
                        ));
                    }
                } else {
                    // Concrete type — getstatic Instance.INSTANCE
                    let type_name = type_to_name(first_arg_ty);
                    if let Some(singleton) = self.instance_singletons.get(&(trait_name.clone(), type_name.clone())) {
                        let field_ref = singleton.instance_field_ref;
                        self.emit(Instruction::Getstatic(field_ref));
                        self.frame.push_type(VerificationType::Object { cpool_index: iface_class });
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
        let constraint_traits = self.fn_constraints.get(name).cloned().unwrap_or_default();

        // Look up function info (need to clone out to avoid borrow conflict)
        let info = self.types
            .functions
            .get(name)
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;
        let method_ref = info.method_ref;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;

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
                        if let Some(&dict_slot) = self.dict_locals.get(trait_name) {
                            self.emit(Instruction::Aload(dict_slot as u8));
                            self.frame.push_type(VerificationType::Object { cpool_index: self.refs.object_class });
                        }
                    } else {
                        let type_name = type_to_name(first_arg_ty);
                        if let Some(singleton) = self.instance_singletons.get(&(trait_name.clone(), type_name)) {
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

        // Push return type
        self.push_jvm_type(return_type);

        Ok(return_type)
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
    fn box_if_needed(&mut self, actual_type: JvmType) -> JvmType {
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
                max_stack: 20,
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

        // after_match: record frame
        let after_match = self.code.len() as u16;
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
    fn compile_function(&mut self, decl: &TypedFnDecl) -> Result<Method, CodegenError> {
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
        let constraint_traits = self.fn_constraints.get(&decl.name).cloned().unwrap_or_default();
        let num_dict_params = constraint_traits.len();
        let mut fn_params = Vec::new();
        for trait_name in &constraint_traits {
            let slot = self.next_local;
            let jvm_ty = JvmType::StructRef(self.refs.object_class);
            self.dict_locals.insert(trait_name.clone(), slot);
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
                max_stack: 20, // conservative estimate
                max_locals: self.next_local,
                code: std::mem::take(&mut self.code),
                exception_table: vec![],
                attributes: code_attributes,
            }],
        })
    }

    /// Calculate max stack depth needed (conservative estimate).
    fn estimate_max_stack(&self) -> u16 {
        20
    }

    fn build_class(
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
                max_stack: self.estimate_max_stack(),
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

/// Map a TypeExpr to a JvmType (for struct field declarations in AST).
fn type_expr_to_jvm(texpr: &TypeExpr) -> Result<JvmType, CodegenError> {
    match texpr {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => match name.as_str() {
            "Int" => Ok(JvmType::Long),
            "Float" => Ok(JvmType::Double),
            "Bool" => Ok(JvmType::Int),
            "String" => Ok(JvmType::Ref),
            "Unit" => Ok(JvmType::Int),
            _ => Err(CodegenError::TypeError(format!(
                "cannot map type expr to JVM: {name}"
            ))),
        },
        _ => Err(CodegenError::TypeError(format!(
            "unsupported type expr in struct field: {texpr:?}"
        ))),
    }
}

/// Generate a standalone class file for a struct type.
fn generate_struct_class(
    name: &str,
    fields: &[(String, JvmType)],
    class_descriptors: &HashMap<u16, String>,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;

    // Build constructor descriptor
    let mut ctor_desc = String::from("(");
    for (_, jt) in fields {
        let desc = match jt {
            JvmType::StructRef(idx) => class_descriptors[idx].clone(),
            other => jvm_type_to_field_descriptor(*other),
        };
        ctor_desc.push_str(&desc);
    }
    ctor_desc.push_str(")V");
    let init_desc = cp.add_utf8(&ctor_desc)?;

    // Build field refs for putfield/getfield
    let mut field_refs = Vec::new();
    let mut jvm_fields = Vec::new();
    for (fname, jt) in fields {
        let fdesc = match jt {
            JvmType::StructRef(idx) => class_descriptors[idx].clone(),
            other => jvm_type_to_field_descriptor(*other),
        };
        let field_ref = cp.add_field_ref(this_class, fname, &fdesc)?;
        field_refs.push(field_ref);

        let name_idx = cp.add_utf8(fname)?;
        let desc_idx = cp.add_utf8(&fdesc)?;
        let field_type = match jt {
            JvmType::StructRef(_) => {
                // fdesc is "LClassName;" — extract "ClassName"
                FieldType::Object(fdesc[1..fdesc.len()-1].to_string())
            }
            other => jvm_type_to_base_field_type(*other),
        };
        jvm_fields.push(Field {
            access_flags: FieldAccessFlags::PRIVATE | FieldAccessFlags::FINAL,
            name_index: name_idx,
            descriptor_index: desc_idx,
            field_type,
            attributes: vec![],
        });
    }

    // Constructor code: aload_0, invokespecial Object.<init>, then store each field
    let mut ctor_code = vec![
        Instruction::Aload_0,
        Instruction::Invokespecial(object_init),
    ];

    let mut param_slot: u16 = 1; // slot 0 = this
    for (i, (_, jt)) in fields.iter().enumerate() {
        ctor_code.push(Instruction::Aload_0);
        let load = match jt {
            JvmType::Long => Instruction::Lload(param_slot as u8),
            JvmType::Double => Instruction::Dload(param_slot as u8),
            JvmType::Int => Instruction::Iload(param_slot as u8),
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(param_slot as u8),
        };
        ctor_code.push(load);
        ctor_code.push(Instruction::Putfield(field_refs[i]));
        param_slot += match jt {
            JvmType::Long | JvmType::Double => 2,
            _ => 1,
        };
    }
    ctor_code.push(Instruction::Return);

    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 20,
            max_locals: param_slot,
            code: ctor_code,
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    // Accessor methods
    let mut methods = vec![constructor];
    for (i, (fname, jt)) in fields.iter().enumerate() {
        let ret_desc = match jt {
            JvmType::StructRef(idx) => class_descriptors[idx].clone(),
            other => jvm_type_to_field_descriptor(*other),
        };
        let method_desc = format!("(){ret_desc}");
        let method_name_idx = cp.add_utf8(fname)?;
        let method_desc_idx = cp.add_utf8(&method_desc)?;

        let ret_instr = match jt {
            JvmType::Long => Instruction::Lreturn,
            JvmType::Double => Instruction::Dreturn,
            JvmType::Int => Instruction::Ireturn,
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Areturn,
        };

        methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: method_name_idx,
            descriptor_index: method_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: 4,
                max_locals: 1,
                code: vec![
                    Instruction::Aload_0,
                    Instruction::Getfield(field_refs[i]),
                    ret_instr,
                ],
                exception_table: vec![],
                attributes: vec![],
            }],
        });
    }

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        fields: jvm_fields,
        methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a sealed interface class file for a sum type.
fn generate_sealed_interface_class(
    name: &str,
    variant_class_names: &[&str],
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    // Add class refs for each variant (for PermittedSubclasses)
    let mut variant_class_indexes = Vec::new();
    for vname in variant_class_names {
        let idx = cp.add_class(vname)?;
        variant_class_indexes.push(idx);
    }

    let permitted_name = cp.add_utf8("PermittedSubclasses")?;

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC
            | ClassAccessFlags::INTERFACE
            | ClassAccessFlags::ABSTRACT,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        attributes: vec![Attribute::PermittedSubclasses {
            name_index: permitted_name,
            class_indexes: variant_class_indexes,
        }],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a variant class file that implements a sealed interface.
fn generate_variant_class(
    variant_name: &str,
    interface_name: &str,
    display_name: &str,
    fields: &[(String, JvmType, bool)], // (name, jvm_type, is_erased)
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(variant_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(interface_name)?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;

    // Build constructor descriptor — erased fields use Ljava/lang/Object;
    let mut ctor_desc = String::from("(");
    for (_, jt, is_erased) in fields {
        if *is_erased {
            ctor_desc.push_str("Ljava/lang/Object;");
        } else {
            ctor_desc.push_str(&jvm_type_to_field_descriptor(*jt));
        }
    }
    ctor_desc.push_str(")V");
    let init_desc = cp.add_utf8(&ctor_desc)?;

    // Build fields and field refs
    let mut field_refs = Vec::new();
    let mut jvm_fields = Vec::new();
    for (i, (fname, jt, is_erased)) in fields.iter().enumerate() {
        let fdesc = if *is_erased {
            "Ljava/lang/Object;".to_string()
        } else {
            jvm_type_to_field_descriptor(*jt)
        };
        let field_ref = cp.add_field_ref(this_class, fname, &fdesc)?;
        field_refs.push(field_ref);

        let name_idx = cp.add_utf8(fname)?;
        let desc_idx = cp.add_utf8(&fdesc)?;
        let field_type = if *is_erased {
            FieldType::Object("java/lang/Object".to_string())
        } else {
            jvm_type_to_base_field_type(*jt)
        };
        jvm_fields.push(Field {
            access_flags: FieldAccessFlags::PUBLIC | FieldAccessFlags::FINAL,
            name_index: name_idx,
            descriptor_index: desc_idx,
            field_type,
            attributes: vec![],
        });
        let _ = i; // suppress unused
    }

    // Constructor code
    let mut ctor_code = vec![
        Instruction::Aload_0,
        Instruction::Invokespecial(object_init),
    ];

    let mut param_slot: u16 = 1;
    for (i, (_, jt, is_erased)) in fields.iter().enumerate() {
        ctor_code.push(Instruction::Aload_0);
        if *is_erased {
            ctor_code.push(Instruction::Aload(param_slot as u8));
            param_slot += 1;
        } else {
            let load = match jt {
                JvmType::Long => Instruction::Lload(param_slot as u8),
                JvmType::Double => Instruction::Dload(param_slot as u8),
                JvmType::Int => Instruction::Iload(param_slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(param_slot as u8),
            };
            ctor_code.push(load);
            param_slot += match jt {
                JvmType::Long | JvmType::Double => 2,
                _ => 1,
            };
        }
        ctor_code.push(Instruction::Putfield(field_refs[i]));
    }
    ctor_code.push(Instruction::Return);

    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 20,
            max_locals: param_slot,
            code: ctor_code,
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let mut methods = vec![constructor];

    // toString() method returning the variant name
    let tostring_name = cp.add_utf8("toString")?;
    let tostring_desc = cp.add_utf8("()Ljava/lang/String;")?;
    let variant_str = cp.add_string(display_name)?;
    let ldc = if variant_str <= 255 {
        Instruction::Ldc(variant_str as u8)
    } else {
        Instruction::Ldc_w(variant_str)
    };
    methods.push(Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: tostring_name,
        descriptor_index: tostring_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 1,
            max_locals: 1,
            code: vec![ldc, Instruction::Areturn],
            exception_table: vec![],
            attributes: vec![],
        }],
    });

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER | ClassAccessFlags::FINAL,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        interfaces: vec![interface_class],
        fields: jvm_fields,
        methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Check if a type expression references any of the given type parameters (directly or in App args).
fn type_expr_uses_type_params(texpr: &TypeExpr, type_params: &[String]) -> bool {
    match texpr {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => {
            type_params.contains(name)
        }
        TypeExpr::App { args, .. } => {
            args.iter().any(|a| type_expr_uses_type_params(a, type_params))
        }
        _ => false,
    }
}

/// Compile a module to JVM bytecode. Returns a list of (class_name, bytes) pairs.
pub fn compile_module(
    module: &Module,
    class_name: &str,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    // Find the main function
    let _main_fn = module
        .decls
        .iter()
        .find_map(|decl| match decl {
            Decl::DefFn(f) if f.name == "main" => Some(f),
            _ => None,
        })
        .ok_or(CodegenError::NoMainFunction)?;

    let (mut compiler, this_class, object_class) = Compiler::new(class_name)?;

    // Register java/lang/Object in class_descriptors for erased type variables
    compiler.types
        .class_descriptors
        .insert(object_class, "Ljava/lang/Object;".to_string());

    // Run the typechecker to get typed module with function types and typed bodies
    let typed_module = infer_module(module).map_err(|e| {
        CodegenError::TypeError(format!("{e:?}"))
    })?;
    let type_info = &typed_module.fn_types;

    // Collect struct declarations from AST
    let struct_decls: Vec<_> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::DefType(td) => match &td.kind {
                TypeDeclKind::Record { fields } => Some((td.name.clone(), fields.clone())),
                _ => None,
            },
            _ => None,
        })
        .collect();

    // Process struct types: register in compiler, generate class files
    let mut result_classes: Vec<(String, Vec<u8>)> = Vec::new();
    for (struct_name, ast_fields) in &struct_decls {
        // Resolve field types to JvmTypes
        let jvm_fields: Vec<(String, JvmType)> = ast_fields
            .iter()
            .map(|(fname, texpr)| {
                // For struct-typed fields, we need to check if it refers to a known struct
                let jt = match texpr {
                    TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => {
                        if let Some(si) = compiler.types.struct_info.get(name.as_str()) {
                            JvmType::StructRef(si.class_index)
                        } else {
                            type_expr_to_jvm(texpr)?
                        }
                    }
                    _ => type_expr_to_jvm(texpr)?,
                };
                Ok((fname.clone(), jt))
            })
            .collect::<Result<_, CodegenError>>()?;

        // Register the struct class in main class's constant pool
        let class_index = compiler.cp.add_class(struct_name)?;
        let class_desc = format!("L{struct_name};");
        compiler.types
            .class_descriptors
            .insert(class_index, class_desc.clone());

        // Add constructor methodref in main class's cpool
        let mut ctor_desc = String::from("(");
        for (_, jt) in &jvm_fields {
            ctor_desc.push_str(&compiler.types.jvm_type_descriptor(*jt));
        }
        ctor_desc.push_str(")V");
        let constructor_ref =
            compiler
                .cp
                .add_method_ref(class_index, "<init>", &ctor_desc)?;

        // Add accessor methodrefs in main class's cpool
        let mut accessor_refs = HashMap::new();
        for (fname, jt) in &jvm_fields {
            let ret_desc = compiler.types.jvm_type_descriptor(*jt);
            let method_desc = format!("(){ret_desc}");
            let accessor_ref =
                compiler
                    .cp
                    .add_method_ref(class_index, fname, &method_desc)?;
            accessor_refs.insert(fname.clone(), accessor_ref);
        }

        compiler.types.struct_info.insert(
            struct_name.clone(),
            StructInfo {
                class_index,
                class_name: struct_name.clone(),
                fields: jvm_fields.clone(),
                constructor_ref,
                accessor_refs,
            },
        );

        // Generate the struct class file
        let struct_bytes =
            generate_struct_class(struct_name, &jvm_fields, &compiler.types.class_descriptors)?;
        result_classes.push((struct_name.clone(), struct_bytes));
    }

    // Collect sum type declarations from AST
    let sum_decls: Vec<_> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::DefType(td) => match &td.kind {
                TypeDeclKind::Sum { variants } => {
                    Some((td.name.clone(), td.type_params.clone(), variants.clone()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect();

    // Process sum types: generate sealed interface + variant classes
    for (sum_name, type_params, variants) in &sum_decls {
        // Register interface class in main cpool
        let interface_class_index = compiler.cp.add_class(sum_name)?;
        let interface_desc = format!("L{sum_name};");
        compiler.types
            .class_descriptors
            .insert(interface_class_index, interface_desc);

        let mut variant_infos = HashMap::new();
        let variant_names: Vec<String> = variants.iter().map(|v| format!("{}${}", sum_name, v.name)).collect();

        for variant in variants {
            // Resolve fields: type params are erased to Object
            let fields: Vec<(String, JvmType, bool)> = variant
                .fields
                .iter()
                .enumerate()
                .map(|(i, texpr)| {
                    let field_name = format!("field{i}");
                    let is_erased = type_expr_uses_type_params(texpr, type_params);
                    let jt = if is_erased {
                        JvmType::Ref // erased to Object
                    } else {
                        type_expr_to_jvm(texpr)?
                    };
                    Ok((field_name, jt, is_erased))
                })
                .collect::<Result<_, CodegenError>>()?;

            // Register variant class in main cpool
            let qualified_name = format!("{}${}", sum_name, variant.name);
            let variant_class_index = compiler.cp.add_class(&qualified_name)?;
            let variant_desc = format!("L{qualified_name};");
            compiler.types
                .class_descriptors
                .insert(variant_class_index, variant_desc);

            // Build constructor descriptor — erased fields use Ljava/lang/Object;
            let mut ctor_desc = String::from("(");
            for (_, jt, is_erased) in &fields {
                if *is_erased {
                    ctor_desc.push_str("Ljava/lang/Object;");
                } else {
                    ctor_desc.push_str(&jvm_type_to_field_descriptor(*jt));
                }
            }
            ctor_desc.push_str(")V");

            let constructor_ref = compiler.cp.add_method_ref(
                variant_class_index,
                "<init>",
                &ctor_desc,
            )?;

            // Add field refs to main cpool for pattern matching getfield
            let mut main_field_refs = Vec::new();
            for (fname, jt, is_erased) in &fields {
                let fdesc = if *is_erased {
                    "Ljava/lang/Object;".to_string()
                } else {
                    jvm_type_to_field_descriptor(*jt)
                };
                let fr = compiler.cp.add_field_ref(variant_class_index, fname, &fdesc)?;
                main_field_refs.push(fr);
            }

            compiler.types
                .variant_to_sum
                .insert(variant.name.clone(), sum_name.clone());

            variant_infos.insert(
                variant.name.clone(),
                VariantInfo {
                    class_index: variant_class_index,
                    class_name: qualified_name.clone(),
                    fields: fields.clone(),
                    constructor_ref,
                    field_refs: main_field_refs,
                },
            );

            // Generate variant class file
            let variant_bytes =
                generate_variant_class(&qualified_name, sum_name, &variant.name, &fields)?;
            result_classes.push((qualified_name.clone(), variant_bytes));
        }

        compiler.types.sum_type_info.insert(
            sum_name.clone(),
            SumTypeInfo {
                interface_class_index,
                variants: variant_infos,
            },
        );

        // Generate sealed interface class file
        let variant_name_refs: Vec<&str> = variant_names.iter().map(|s| s.as_str()).collect();
        let interface_bytes = generate_sealed_interface_class(sum_name, &variant_name_refs)?;
        result_classes.push((sum_name.clone(), interface_bytes));
    }

    // Pre-scan for function-typed params so we can register FunN interfaces first
    for (name, scheme) in type_info.iter() {
        if let Type::Fn(param_tys, _) = &scheme.ty {
            if compiler.types.struct_info.contains_key(name)
                || compiler.types.variant_to_sum.contains_key(name)
            {
                continue;
            }
            for pt in param_tys {
                if let Type::Fn(inner_params, _) = pt {
                    let arity = inner_params.len() as u8;
                    compiler.lambda.ensure_fun_interface(arity, &mut compiler.cp, &mut compiler.types.class_descriptors)?;
                }
            }
        }
    }

    // Process trait definitions: generate interface classes
    compiler.trait_method_map = typed_module.trait_method_map.clone();
    compiler.fn_constraints = typed_module.fn_constraints.clone();

    for trait_def in &typed_module.trait_defs {
        let interface_bytes = generate_trait_interface_class(&trait_def.name, &trait_def.methods)?;
        result_classes.push((trait_def.name.clone(), interface_bytes));

        // Register interface class in main cpool
        let iface_class = compiler.cp.add_class(&trait_def.name)?;
        compiler.types.class_descriptors.insert(iface_class, format!("L{};", trait_def.name));

        // Register interface method refs in main cpool
        let mut method_refs = HashMap::new();
        for (method_name, param_count) in &trait_def.methods {
            let mut desc = String::from("(");
            for _ in 0..*param_count {
                desc.push_str("Ljava/lang/Object;");
            }
            desc.push_str(")Ljava/lang/Object;");
            let mref = compiler.cp.add_interface_method_ref(iface_class, method_name, &desc)?;
            method_refs.insert(method_name.clone(), mref);
        }

        compiler.trait_dispatch.insert(trait_def.name.clone(), TraitDispatchInfo {
            interface_class: iface_class,
            method_refs,
        });
    }

    // Process instance definitions: generate singleton classes
    for instance_def in &typed_module.instance_defs {
        let instance_class_name = format!("{}${}", instance_def.trait_name, instance_def.target_type_name);

        // Collect method info for the instance class
        let mut method_info = Vec::new();
        let mut param_jvm_types_map: HashMap<String, Vec<JvmType>> = HashMap::new();
        let mut return_jvm_types_map: HashMap<String, JvmType> = HashMap::new();
        let mut param_class_names_map: HashMap<String, Vec<Option<String>>> = HashMap::new();

        for (method_name, qualified_name) in &instance_def.qualified_method_names {
            // Look up the qualified method's type from fn_types
            if let Some((_, scheme)) = typed_module.fn_types.iter().find(|(n, _)| n == qualified_name) {
                if let Type::Fn(param_tys, ret_ty) = &scheme.ty {
                    let param_jvm: Vec<JvmType> = param_tys.iter()
                        .map(|t| compiler.type_to_jvm(t))
                        .collect::<Result<_, _>>()?;
                    let ret_jvm = compiler.type_to_jvm(ret_ty)?;
                    // Build the static method descriptor using string descriptors
                    let static_desc = compiler.types.build_descriptor(&param_jvm, ret_jvm);
                    // Collect class names for checkcast in bridge methods
                    let class_names: Vec<Option<String>> = param_tys.iter().map(|t| {
                        match t {
                            Type::Named(name, _) => Some(name.clone()),
                            _ => None,
                        }
                    }).collect();
                    param_class_names_map.insert(method_name.clone(), class_names);
                    param_jvm_types_map.insert(method_name.clone(), param_jvm);
                    return_jvm_types_map.insert(method_name.clone(), ret_jvm);
                    method_info.push((method_name.clone(), qualified_name.clone(), param_tys.len(), static_desc));
                }
            }
        }

        let instance_bytes = generate_instance_class(
            &instance_class_name,
            &instance_def.trait_name,
            class_name,
            &method_info,
            &param_jvm_types_map,
            &return_jvm_types_map,
            &param_class_names_map,
        )?;
        result_classes.push((instance_class_name.clone(), instance_bytes));

        // Register INSTANCE field ref in main cpool
        let inst_class_idx = compiler.cp.add_class(&instance_class_name)?;
        let inst_desc = format!("L{instance_class_name};");
        compiler.types.class_descriptors.insert(inst_class_idx, inst_desc.clone());
        let instance_field_ref = compiler.cp.add_field_ref(inst_class_idx, "INSTANCE", &inst_desc)?;

        compiler.instance_singletons.insert(
            (instance_def.trait_name.clone(), instance_def.target_type_name.clone()),
            InstanceSingletonInfo { instance_field_ref },
        );
    }

    // Register all functions (including main) in the function registry.
    // Skip constructor entries (they're handled as struct/variant constructors).
    for (name, scheme) in type_info.iter() {
        if let Type::Fn(param_tys, ret_ty) = &scheme.ty {
            // Skip if this is a struct constructor or variant constructor
            if compiler.types.struct_info.contains_key(name)
                || compiler.types.variant_to_sum.contains_key(name)
            {
                continue;
            }
            // For constrained functions, prepend dict params (one Object per trait constraint)
            let constraint_traits = compiler.fn_constraints.get(name).cloned().unwrap_or_default();
            let mut all_param_types: Vec<JvmType> = Vec::new();
            for _ in &constraint_traits {
                all_param_types.push(JvmType::StructRef(compiler.refs.object_class));
            }
            let user_param_types: Vec<JvmType> = param_tys
                .iter()
                .map(|t| compiler.type_to_jvm(t))
                .collect::<Result<_, _>>()?;
            all_param_types.extend(user_param_types);
            let return_type = compiler.type_to_jvm(ret_ty)?;
            let jvm_name = if name == "main" {
                "krypton_main"
            } else {
                name.as_str()
            };
            let descriptor = compiler.types.build_descriptor(&all_param_types, return_type);
            let method_ref =
                compiler.cp.add_method_ref(this_class, jvm_name, &descriptor)?;
            compiler.types.functions.insert(
                name.clone(),
                FunctionInfo {
                    method_ref,
                    param_types: all_param_types,
                    return_type,
                },
            );
            // Store TC types for detecting Fn-typed params in compile_function
            compiler.types.fn_tc_types.insert(
                name.clone(),
                (param_tys.clone(), (**ret_ty).clone()),
            );
        }
    }

    // Compile all functions (including main) as static methods using typed bodies
    let mut extra_methods = Vec::new();
    for typed_fn in &typed_module.functions {
        let mut method = compiler.compile_function(typed_fn)?;
        // Rename main → krypton_main in the method
        if typed_fn.name == "main" {
            let name_idx = compiler.cp.add_utf8("krypton_main")?;
            method.name_index = name_idx;
        }
        extra_methods.push(method);
    }

    // Build JVM main(String[])V — calls krypton_main and prints the result
    let main_info = compiler.types.functions.get("main").ok_or(CodegenError::NoMainFunction)?;
    let krypton_main_ref = main_info.method_ref;
    let main_return_type = main_info.return_type;

    compiler.reset_method_state();
    compiler.next_local = 1; // slot 0 = String[] args
    let string_arr_class = compiler.cp.add_class("[Ljava/lang/String;")?;
    compiler.frame.local_types = vec![VerificationType::Object {
        cpool_index: string_arr_class,
    }];

    // Emit: getstatic System.out
    let system_out = compiler.refs.system_out;
    compiler.emit(Instruction::Getstatic(system_out));
    compiler.frame.push_type(VerificationType::Object {
        cpool_index: compiler.refs.ps_class,
    });

    // Call krypton_main
    compiler.emit(Instruction::Invokestatic(krypton_main_ref));
    compiler.push_jvm_type(main_return_type);

    // Emit the appropriate println call
    let println_ref = match main_return_type {
        JvmType::Long => compiler.refs.println_long,
        JvmType::Double => compiler.refs.println_double,
        JvmType::Ref => compiler.refs.println_string,
        JvmType::Int => compiler.refs.println_bool,
        JvmType::StructRef(_) => compiler.refs.println_object,
    };
    compiler.emit(Instruction::Invokevirtual(println_ref));

    // Pop println args + PrintStream from stack tracker
    compiler.pop_jvm_type(main_return_type);
    compiler.frame.pop_type(); // PrintStream

    compiler.emit(Instruction::Return);

    // Generate FunN interface class files
    let fun_arities: Vec<u8> = compiler.lambda.fun_classes.keys().copied().collect();
    for arity in fun_arities {
        let fun_bytes = generate_fun_interface(arity)?;
        result_classes.push((format!("Fun{arity}"), fun_bytes));
    }

    let main_bytes = compiler.build_class(this_class, object_class, extra_methods)?;
    result_classes.push((class_name.to_string(), main_bytes));

    Ok(result_classes)
}

/// Generate a functional interface class file: `public interface FunN { Object apply(Object, ...); }`
fn generate_fun_interface(arity: u8) -> Result<Vec<u8>, CodegenError> {
    let class_name = format!("Fun{arity}");
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(&class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    // Build apply method descriptor: (Object, ..., Object)Object
    let mut apply_desc = String::from("(");
    for _ in 0..arity {
        apply_desc.push_str("Ljava/lang/Object;");
    }
    apply_desc.push_str(")Ljava/lang/Object;");

    let apply_name = cp.add_utf8("apply")?;
    let apply_desc_idx = cp.add_utf8(&apply_desc)?;

    let apply_method = Method {
        access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::ABSTRACT,
        name_index: apply_name,
        descriptor_index: apply_desc_idx,
        attributes: vec![],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC
            | ClassAccessFlags::INTERFACE
            | ClassAccessFlags::ABSTRACT,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        methods: vec![apply_method],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a trait interface class file (e.g., `Eq.class`).
/// All methods take and return Object (type erasure).
fn generate_trait_interface_class(
    name: &str,
    methods: &[(String, usize)], // (method_name, param_count)
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    let mut jvm_methods = Vec::new();
    for (method_name, param_count) in methods {
        let mut desc = String::from("(");
        for _ in 0..*param_count {
            desc.push_str("Ljava/lang/Object;");
        }
        desc.push_str(")Ljava/lang/Object;");

        let name_idx = cp.add_utf8(method_name)?;
        let desc_idx = cp.add_utf8(&desc)?;

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::ABSTRACT,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![],
        });
    }

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC
            | ClassAccessFlags::INTERFACE
            | ClassAccessFlags::ABSTRACT,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        methods: jvm_methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate an instance singleton class (e.g., `Eq$Point.class`).
/// Implements the trait interface, delegates to static methods on the main class.
fn generate_instance_class(
    class_name: &str,
    trait_interface_name: &str,
    main_class_name: &str,
    methods: &[(String, String, usize, String)], // (iface_method_name, static_method_name, param_count, static_descriptor)
    param_jvm_types: &HashMap<String, Vec<JvmType>>,
    return_jvm_types: &HashMap<String, JvmType>,
    param_class_names: &HashMap<String, Vec<Option<String>>>, // method_name → per-param class names for checkcast
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(trait_interface_name)?;
    let main_class = cp.add_class(main_class_name)?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8("()V")?;

    // INSTANCE field
    let self_desc = format!("L{class_name};");
    let instance_name = cp.add_utf8("INSTANCE")?;
    let instance_desc = cp.add_utf8(&self_desc)?;
    let instance_field_ref = cp.add_field_ref(this_class, "INSTANCE", &self_desc)?;
    let self_init = cp.add_method_ref(this_class, "<init>", "()V")?;

    // Boxing/unboxing refs
    let long_box_class = cp.add_class("java/lang/Long")?;
    let long_valueof = cp.add_method_ref(long_box_class, "valueOf", "(J)Ljava/lang/Long;")?;
    let long_unbox = cp.add_method_ref(long_box_class, "longValue", "()J")?;
    let double_box_class = cp.add_class("java/lang/Double")?;
    let double_valueof = cp.add_method_ref(double_box_class, "valueOf", "(D)Ljava/lang/Double;")?;
    let _double_unbox = cp.add_method_ref(double_box_class, "doubleValue", "()D")?;
    let bool_box_class = cp.add_class("java/lang/Boolean")?;
    let bool_valueof = cp.add_method_ref(bool_box_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
    let _bool_unbox = cp.add_method_ref(bool_box_class, "booleanValue", "()Z")?;

    // Constructor
    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 2,
            max_locals: 1,
            code: vec![
                Instruction::Aload_0,
                Instruction::Invokespecial(object_init),
                Instruction::Return,
            ],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    // <clinit> — static initializer
    let clinit_name = cp.add_utf8("<clinit>")?;
    let clinit_desc = cp.add_utf8("()V")?;
    let clinit = Method {
        access_flags: MethodAccessFlags::STATIC,
        name_index: clinit_name,
        descriptor_index: clinit_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 2,
            max_locals: 0,
            code: vec![
                Instruction::New(this_class),
                Instruction::Dup,
                Instruction::Invokespecial(self_init),
                Instruction::Putstatic(instance_field_ref),
                Instruction::Return,
            ],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let mut jvm_methods = vec![constructor, clinit];

    // Bridge methods: implement interface methods delegating to static impls
    for (iface_method_name, static_method_name, param_count, static_desc) in methods {
        // Interface method descriptor: all Object
        let mut iface_desc = String::from("(");
        for _ in 0..*param_count {
            iface_desc.push_str("Ljava/lang/Object;");
        }
        iface_desc.push_str(")Ljava/lang/Object;");

        let concrete_params = param_jvm_types.get(iface_method_name)
            .cloned()
            .unwrap_or_default();
        let concrete_ret = return_jvm_types.get(iface_method_name)
            .copied()
            .unwrap_or(JvmType::Int);

        let static_ref = cp.add_method_ref(main_class, static_method_name, static_desc)?;

        let method_name_idx = cp.add_utf8(iface_method_name)?;
        let method_desc_idx = cp.add_utf8(&iface_desc)?;

        // Build bridge code: unbox params → invokestatic → box result
        let mut bridge_code: Vec<Instruction> = Vec::new();
        let mut slot: u8 = 1; // slot 0 = this

        let class_names_for_method = param_class_names.get(iface_method_name)
            .cloned()
            .unwrap_or_default();

        for (param_idx, pt) in concrete_params.iter().enumerate() {
            bridge_code.push(Instruction::Aload(slot));
            match pt {
                JvmType::Long => {
                    bridge_code.push(Instruction::Checkcast(long_box_class));
                    bridge_code.push(Instruction::Invokevirtual(long_unbox));
                }
                JvmType::Double => {
                    bridge_code.push(Instruction::Checkcast(double_box_class));
                    bridge_code.push(Instruction::Invokevirtual(_double_unbox));
                }
                JvmType::Int => {
                    bridge_code.push(Instruction::Checkcast(bool_box_class));
                    bridge_code.push(Instruction::Invokevirtual(_bool_unbox));
                }
                JvmType::StructRef(_) => {
                    // Checkcast Object → concrete struct type if we know the class name
                    if let Some(Some(cn)) = class_names_for_method.get(param_idx) {
                        let cast_class = cp.add_class(cn)?;
                        bridge_code.push(Instruction::Checkcast(cast_class));
                    }
                }
                _ => {}
            }
            slot += 1;
        }

        bridge_code.push(Instruction::Invokestatic(static_ref));

        // Box the result back to Object
        match concrete_ret {
            JvmType::Long => {
                bridge_code.push(Instruction::Invokestatic(long_valueof));
            }
            JvmType::Double => {
                bridge_code.push(Instruction::Invokestatic(double_valueof));
            }
            JvmType::Int => {
                bridge_code.push(Instruction::Invokestatic(bool_valueof));
            }
            _ => {}
        }
        bridge_code.push(Instruction::Areturn);

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: method_name_idx,
            descriptor_index: method_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: 20,
                max_locals: (1 + *param_count) as u16,
                code: bridge_code,
                exception_table: vec![],
                attributes: vec![],
            }],
        });
    }

    // INSTANCE field declaration
    let field = Field {
        access_flags: FieldAccessFlags::PUBLIC | FieldAccessFlags::STATIC | FieldAccessFlags::FINAL,
        name_index: instance_name,
        descriptor_index: instance_desc,
        field_type: FieldType::Object(class_name.to_string()),
        attributes: vec![],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER | ClassAccessFlags::FINAL,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        interfaces: vec![interface_class],
        fields: vec![field],
        methods: jvm_methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a minimal valid `.class` file containing a no-op
/// `public static void main(String[])` method.
pub fn generate_empty_main(class_name: &str) -> Result<Vec<u8>, ristretto_classfile::Error> {
    let mut cp = ConstantPool::default();

    // Class refs
    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    // "Code" attribute name must be in the constant pool
    let code_utf8 = cp.add_utf8("Code")?;

    // Method ref for super constructor call
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;

    // Method name/descriptor UTF-8 entries
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8("()V")?;
    let main_name = cp.add_utf8("main")?;
    let main_desc = cp.add_utf8("([Ljava/lang/String;)V")?;

    // Default constructor: calls super.<init>()
    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 1,
            max_locals: 1,
            code: vec![
                Instruction::Aload_0,
                Instruction::Invokespecial(object_init),
                Instruction::Return,
            ],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    // main method: just returns
    let main_method = Method {
        access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
        name_index: main_name,
        descriptor_index: main_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 0,
            max_locals: 1,
            code: vec![Instruction::Return],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        methods: vec![constructor, main_method],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}
