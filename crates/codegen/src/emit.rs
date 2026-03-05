use std::collections::{BTreeMap, HashMap};

use krypton_parser::ast::{BinOp, Decl, Expr, FnDecl, Lit, MatchArm, Module, Pattern, Span, TypeDeclKind, TypeExpr};
use krypton_typechecker::infer::infer_module;
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

struct Compiler {
    cp: ConstantPool,
    code: Vec<Instruction>,
    locals: HashMap<String, (u16, JvmType)>,
    next_local: u16,
    code_utf8: u16,
    object_init: u16,
    init_name: u16,
    init_desc: u16,
    system_out: u16,
    println_long: u16,
    println_string: u16,
    println_double: u16,
    println_bool: u16,
    // StackMapTable support
    stack_types: Vec<VerificationType>,
    local_types: Vec<VerificationType>,
    frames: BTreeMap<u16, (Vec<VerificationType>, Vec<VerificationType>)>,
    smt_name: u16,
    string_class: u16,
    ps_class: u16,
    println_object: u16,
    // Function codegen support
    this_class: u16,
    functions: HashMap<String, FunctionInfo>,
    // Struct codegen support
    struct_info: HashMap<String, StructInfo>,
    class_descriptors: HashMap<u16, String>, // class_idx -> "LClassName;"
    // Sum type codegen support
    sum_type_info: HashMap<String, SumTypeInfo>,
    variant_to_sum: HashMap<String, String>, // variant_name -> sum_type_name
    // Boxing support
    long_box_valueof: u16,
    double_box_valueof: u16,
    bool_box_valueof: u16,
    // Unboxing support
    long_box_class: u16,
    long_unbox: u16,
    double_box_class: u16,
    double_unbox: u16,
    bool_box_class: u16,
    bool_unbox: u16,
    // Recur support: parameter slots and return type for current function
    fn_params: Vec<(u16, JvmType)>,
    fn_return_type: Option<JvmType>,
    // Pattern match: nested ifeq patches for nested constructor patterns
    nested_ifeq_patches: Vec<usize>,
    // Object class index for erased type variables
    object_class: u16,
    // Lambda / closure support
    lambda_counter: u16,
    lambda_methods: Vec<Method>,
    bootstrap_methods: Vec<BootstrapMethod>,
    lambda_types: HashMap<Span, (Vec<JvmType>, JvmType)>,
    /// For let-bound lambdas: var name -> (param_jvm_types, return_jvm_type)
    local_fn_info: HashMap<String, (Vec<JvmType>, JvmType)>,
    /// Lazily initialized cpool index for LambdaMetafactory.metafactory MethodHandle
    metafactory_handle: Option<u16>,
    /// FunN interface class indices by arity
    fun_classes: HashMap<u8, u16>,
    /// FunN.apply interface method refs by arity
    fun_apply_refs: HashMap<u8, u16>,
    /// Original typechecker types for top-level functions, for inspecting Fn-typed params
    fn_tc_types: HashMap<String, (Vec<Type>, Type)>,
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
            code: Vec::new(),
            locals: HashMap::new(),
            next_local: 1, // slot 0 = String[] args for main
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
            stack_types: Vec::new(),
            local_types: vec![VerificationType::Object {
                cpool_index: string_arr_class,
            }],
            frames: BTreeMap::new(),
            smt_name,
            string_class,
            ps_class,
            this_class,
            functions: HashMap::new(),
            struct_info: HashMap::new(),
            class_descriptors: HashMap::new(),
            sum_type_info: HashMap::new(),
            variant_to_sum: HashMap::new(),
            long_box_valueof,
            double_box_valueof,
            bool_box_valueof,
            long_box_class,
            long_unbox,
            double_box_class,
            double_unbox,
            bool_box_class,
            bool_unbox,
            fn_params: Vec::new(),
            fn_return_type: None,
            nested_ifeq_patches: Vec::new(),
            object_class,
            lambda_counter: 0,
            lambda_methods: Vec::new(),
            bootstrap_methods: Vec::new(),
            lambda_types: HashMap::new(),
            local_fn_info: HashMap::new(),
            metafactory_handle: None,
            fun_classes: HashMap::new(),
            fun_apply_refs: HashMap::new(),
            fn_tc_types: HashMap::new(),
        };

        Ok((compiler, this_class, object_class))
    }

    /// Map a typechecker Type to a JvmType, using struct_info/sum_type_info for Named types.
    fn type_to_jvm(&self, ty: &Type) -> Result<JvmType, CodegenError> {
        match ty {
            Type::Named(name, _) => {
                if let Some(info) = self.struct_info.get(name) {
                    Ok(JvmType::StructRef(info.class_index))
                } else if let Some(info) = self.sum_type_info.get(name) {
                    Ok(JvmType::StructRef(info.interface_class_index))
                } else {
                    Err(CodegenError::TypeError(format!(
                        "unknown named type: {name}"
                    )))
                }
            }
            Type::Var(_) => Ok(JvmType::StructRef(self.object_class)), // erased type variable → Object
            Type::Fn(params, _) => {
                let arity = params.len() as u8;
                // Return FunN interface ref if registered, else Object
                if let Some(&class_idx) = self.fun_classes.get(&arity) {
                    Ok(JvmType::StructRef(class_idx))
                } else {
                    Ok(JvmType::StructRef(self.object_class))
                }
            }
            other => type_to_jvm_basic(other),
        }
    }

    /// Get the JVM type descriptor for a JvmType.
    fn jvm_type_descriptor(&self, ty: JvmType) -> String {
        match ty {
            JvmType::StructRef(idx) => self.class_descriptors[&idx].clone(),
            other => jvm_type_to_field_descriptor(other),
        }
    }

    /// Build a method descriptor from param and return JvmTypes.
    fn build_descriptor(&self, params: &[JvmType], ret: JvmType) -> String {
        let mut desc = String::from("(");
        for p in params {
            desc.push_str(&self.jvm_type_descriptor(*p));
        }
        desc.push(')');
        desc.push_str(&self.jvm_type_descriptor(ret));
        desc
    }

    /// Reset per-method compilation state.
    fn reset_method_state(&mut self) {
        self.code.clear();
        self.locals.clear();
        self.next_local = 0;
        self.stack_types.clear();
        self.local_types.clear();
        self.frames.clear();
        self.fn_params.clear();
        self.fn_return_type = None;
        self.local_fn_info.clear();
    }

    fn emit(&mut self, instr: Instruction) {
        self.code.push(instr);
    }

    // Stack type tracking helpers
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
        // StackMapTable FullFrame format does not include Top entries after
        // Long/Double — those second slots are implicit.
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

    fn jvm_type_to_vtypes(&self, ty: JvmType) -> Vec<VerificationType> {
        match ty {
            JvmType::Long => vec![VerificationType::Long, VerificationType::Top],
            JvmType::Double => vec![VerificationType::Double, VerificationType::Top],
            JvmType::Int => vec![VerificationType::Integer],
            JvmType::Ref => vec![VerificationType::Object {
                cpool_index: self.string_class,
            }],
            JvmType::StructRef(idx) => vec![VerificationType::Object {
                cpool_index: idx,
            }],
        }
    }

    fn push_jvm_type(&mut self, ty: JvmType) {
        for vt in self.jvm_type_to_vtypes(ty) {
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

    fn compile_expr(&mut self, expr: &Expr, in_tail: bool) -> Result<JvmType, CodegenError> {
        match expr {
            Expr::Lit { value, .. } => self.compile_lit(value),
            Expr::BinaryOp {
                op, lhs, rhs, ..
            } => self.compile_binop(op, lhs, rhs),
            Expr::If {
                cond,
                then_,
                else_,
                ..
            } => self.compile_if(cond, then_, else_, in_tail),
            Expr::Let {
                name, value, body, ..
            } => self.compile_let(name, value, body, in_tail),
            Expr::Var { name, .. } => self.compile_var(name),
            Expr::Do { exprs, .. } => self.compile_do(exprs, in_tail),
            Expr::App { func, args, .. } => self.compile_app(func, args),
            Expr::Recur { args, .. } => self.compile_recur(args, in_tail),
            Expr::FieldAccess { expr, field, .. } => self.compile_field_access(expr, field),
            Expr::StructUpdate { base, fields, .. } => self.compile_struct_update(base, fields),
            Expr::Match {
                scrutinee, arms, ..
            } => self.compile_match(scrutinee, arms, in_tail),
            Expr::Lambda {
                params, body, span, ..
            } => self.compile_lambda(params, body, span),
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
                self.push_long_type();
                Ok(JvmType::Long)
            }
            Lit::Float(f) => {
                let idx = self.cp.add_double(*f)?;
                self.emit(Instruction::Ldc2_w(idx));
                self.push_double_type();
                Ok(JvmType::Double)
            }
            Lit::Bool(b) => {
                self.emit(if *b {
                    Instruction::Iconst_1
                } else {
                    Instruction::Iconst_0
                });
                self.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            Lit::String(s) => {
                let idx = self.cp.add_string(s)?;
                if idx <= 255 {
                    self.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.emit(Instruction::Ldc_w(idx));
                }
                self.push_type(VerificationType::Object {
                    cpool_index: self.string_class,
                });
                Ok(JvmType::Ref)
            }
            Lit::Unit => {
                // Push nothing; return Int as a placeholder
                Ok(JvmType::Int)
            }
        }
    }

    fn compile_binop(
        &mut self,
        op: &BinOp,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<JvmType, CodegenError> {
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
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
                // Pop two longs, push one long
                self.pop_type_n(4);
                self.push_long_type();
                Ok(JvmType::Long)
            }
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.compile_comparison(op, lhs, rhs)
            }
        }
    }

    fn compile_comparison(
        &mut self,
        op: &BinOp,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<JvmType, CodegenError> {
        self.compile_expr(lhs, false)?;
        self.compile_expr(rhs, false)?;
        self.emit(Instruction::Lcmp);

        // Lcmp: pop two longs (4 slots), push int
        self.pop_type_n(4);
        self.push_type(VerificationType::Integer);

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
        self.pop_type();

        // Record frame at false_target (stack state after Ifxx consumes int)
        let stack_at_false = self.stack_types.clone();
        self.record_frame(false_target);

        // True path: push 1
        self.emit(Instruction::Iconst_1);
        self.push_type(VerificationType::Integer);

        // Record frame at after_target (stack has Integer on top)
        self.record_frame(after_target);
        let stack_after = self.stack_types.clone();

        self.emit(Instruction::Goto(after_target));

        // False path: restore stack to state at false_target
        self.stack_types = stack_at_false;
        self.emit(Instruction::Iconst_0);
        self.push_type(VerificationType::Integer);

        // After both paths merge, stack should match
        debug_assert_eq!(self.stack_types, stack_after);

        Ok(JvmType::Int)
    }

    fn compile_if(
        &mut self,
        cond: &Expr,
        then_: &Expr,
        else_: &Expr,
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // Compile condition (produces Int 0/1 on stack)
        self.compile_expr(cond, false)?;

        // Ifeq consumes the int
        self.pop_type();

        // Emit Ifeq with placeholder — will be patched with instruction index
        let ifeq_idx = self.code.len();
        self.emit(Instruction::Ifeq(0)); // placeholder

        // Save stack state at branch point (after consuming condition)
        let stack_at_branch = self.stack_types.clone();

        // Compile then branch
        let then_type = self.compile_expr(then_, in_tail)?;
        let stack_after_then = self.stack_types.clone();

        // Emit Goto with placeholder
        let goto_idx = self.code.len();
        self.emit(Instruction::Goto(0)); // placeholder

        // else starts at this instruction index
        let else_start = self.code.len() as u16;

        // Record frame at else_start with stack state from branch point
        self.stack_types = stack_at_branch;
        self.record_frame(else_start);

        // Compile else branch
        let _else_type = self.compile_expr(else_, in_tail)?;

        let after_else = self.code.len() as u16;

        // Record frame at after_else
        self.record_frame(after_else);

        debug_assert_eq!(self.stack_types, stack_after_then);

        // Patch: Ifeq should jump to else_start instruction index
        self.code[ifeq_idx] = Instruction::Ifeq(else_start);
        // Patch: Goto should jump past else
        self.code[goto_idx] = Instruction::Goto(after_else);

        Ok(then_type)
    }

    fn compile_let(
        &mut self,
        name: &str,
        value: &Expr,
        body: &Option<Box<Expr>>,
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // Check if the value is a lambda — record its type info for higher-order calls
        let is_lambda = matches!(value, Expr::Lambda { .. });
        let lambda_span = if let Expr::Lambda { span, .. } = value {
            Some(*span)
        } else {
            None
        };

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

        // If the value was a lambda, record local_fn_info for higher-order calls
        if is_lambda {
            if let Some(span) = lambda_span {
                if let Some((param_types, ret_type)) = self.lambda_types.get(&span).cloned() {
                    self.local_fn_info.insert(name.to_string(), (param_types, ret_type));
                }
            }
        }

        // Pop value from stack tracker
        self.pop_jvm_type(ty);

        // Extend local_types with verification type(s)
        let vtypes = self.jvm_type_to_vtypes(ty);
        self.local_types.extend(vtypes);

        if let Some(body) = body {
            self.compile_expr(body, in_tail)
        } else {
            // In a do-block, let without body is a statement — no value on stack
            // We return Int as a placeholder type (no value actually pushed)
            Ok(JvmType::Int)
        }
    }

    fn compile_var(&mut self, name: &str) -> Result<JvmType, CodegenError> {
        // Check if this is a nullary variant constructor
        if let Some(sum_name) = self.variant_to_sum.get(name).cloned() {
            let sum_info = &self.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            if vi.fields.is_empty() {
                let class_index = vi.class_index;
                let constructor_ref = vi.constructor_ref;
                let interface_class_index = sum_info.interface_class_index;
                self.emit(Instruction::New(class_index));
                self.push_type(VerificationType::UninitializedThis);
                self.emit(Instruction::Dup);
                self.push_type(VerificationType::UninitializedThis);
                self.emit(Instruction::Invokespecial(constructor_ref));
                self.pop_type(); // dup'd uninit
                self.pop_type(); // original uninit
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

    fn compile_app(&mut self, func: &Expr, args: &[Expr]) -> Result<JvmType, CodegenError> {
        let name = match func {
            Expr::Var { name, .. } => name.as_str(),
            other => {
                return Err(CodegenError::UnsupportedExpr(format!(
                    "non-variable function call: {other:?}"
                )))
            }
        };

        // Check if this is a struct constructor call
        if let Some(si) = self.struct_info.get(name) {
            let class_index = si.class_index;
            let constructor_ref = si.constructor_ref;
            let result_type = JvmType::StructRef(class_index);

            self.emit(Instruction::New(class_index));
            self.push_type(VerificationType::UninitializedThis);
            self.emit(Instruction::Dup);
            self.push_type(VerificationType::UninitializedThis);

            for arg in args {
                self.compile_expr(arg, false)?;
            }

            // Pop args + 2 uninit refs, push one StructRef
            let fields = self.struct_info[name].fields.clone();
            for (_, ft) in &fields {
                self.pop_jvm_type(*ft);
            }
            self.pop_type(); // dup'd uninit
            self.pop_type(); // original uninit

            self.emit(Instruction::Invokespecial(constructor_ref));
            self.push_jvm_type(result_type);

            return Ok(result_type);
        }

        // Check if this is a variant constructor call
        if let Some(sum_name) = self.variant_to_sum.get(name).cloned() {
            let sum_info = &self.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            let class_index = vi.class_index;
            let constructor_ref = vi.constructor_ref;
            let interface_class_index = sum_info.interface_class_index;
            let fields: Vec<(String, JvmType, bool)> = vi.fields.clone();
            let result_type = JvmType::StructRef(interface_class_index);

            self.emit(Instruction::New(class_index));
            self.push_type(VerificationType::UninitializedThis);
            self.emit(Instruction::Dup);
            self.push_type(VerificationType::UninitializedThis);

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
                    self.pop_type(); // Object ref
                } else {
                    self.pop_jvm_type(*ft);
                }
            }
            self.pop_type(); // dup'd uninit
            self.pop_type(); // original uninit

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
                let apply_ref = self.fun_apply_refs[&arity];
                self.emit(Instruction::Invokeinterface(apply_ref, arity + 1));
                // Pop args + receiver
                for _ in 0..arity {
                    self.pop_type(); // each boxed arg
                }
                self.pop_jvm_type(jvm_ty); // receiver
                // Push Object result
                self.push_type(VerificationType::Object { cpool_index: self.object_class });
                // Unbox if needed
                self.unbox_if_needed(ho_ret_type);
                return Ok(ho_ret_type);
            }
        }

        // Look up function info (need to clone out to avoid borrow conflict)
        let info = self
            .functions
            .get(name)
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;
        let method_ref = info.method_ref;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;

        // Compile each argument, boxing if needed for erased type params
        for (i, arg) in args.iter().enumerate() {
            let arg_type = self.compile_expr(arg, false)?;
            if let JvmType::StructRef(idx) = param_types[i] {
                if idx == self.object_class && !matches!(arg_type, JvmType::StructRef(_) | JvmType::Ref) {
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
        expr: &Expr,
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
            let si = self
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
        base: &Expr,
        updates: &[(String, Expr)],
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
        self.local_types.extend(vtypes);

        // Look up struct info
        let si = self
            .struct_info
            .values()
            .find(|s| s.class_index == class_idx)
            .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
        let constructor_ref = si.constructor_ref;
        let fields = si.fields.clone();
        let accessor_refs = si.accessor_refs.clone();

        self.emit(Instruction::New(class_idx));
        self.push_type(VerificationType::UninitializedThis);
        self.emit(Instruction::Dup);
        self.push_type(VerificationType::UninitializedThis);

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
        self.pop_type(); // dup'd uninit
        self.pop_type(); // original uninit

        self.emit(Instruction::Invokespecial(constructor_ref));
        self.push_jvm_type(base_type);

        Ok(base_type)
    }

    fn compile_recur(
        &mut self,
        args: &[Expr],
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
        self.frames.insert(1, (
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
                self.pop_type_n(2); // Long + Top
                self.emit(Instruction::Invokestatic(self.long_box_valueof));
                self.push_type(VerificationType::Object {
                    cpool_index: self.long_box_class,
                });
                JvmType::Ref
            }
            JvmType::Double => {
                self.pop_type_n(2); // Double + Top
                self.emit(Instruction::Invokestatic(self.double_box_valueof));
                self.push_type(VerificationType::Object {
                    cpool_index: self.double_box_class,
                });
                JvmType::Ref
            }
            JvmType::Int => {
                self.pop_type(); // Integer
                self.emit(Instruction::Invokestatic(self.bool_box_valueof));
                self.push_type(VerificationType::Object {
                    cpool_index: self.bool_box_class,
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
                self.emit(Instruction::Checkcast(self.long_box_class));
                self.pop_type();
                self.push_type(VerificationType::Object {
                    cpool_index: self.long_box_class,
                });
                self.emit(Instruction::Invokevirtual(self.long_unbox));
                self.pop_type();
                self.push_long_type();
            }
            JvmType::Double => {
                self.emit(Instruction::Checkcast(self.double_box_class));
                self.pop_type();
                self.push_type(VerificationType::Object {
                    cpool_index: self.double_box_class,
                });
                self.emit(Instruction::Invokevirtual(self.double_unbox));
                self.pop_type();
                self.push_double_type();
            }
            JvmType::Int => {
                self.emit(Instruction::Checkcast(self.bool_box_class));
                self.pop_type();
                self.push_type(VerificationType::Object {
                    cpool_index: self.bool_box_class,
                });
                self.emit(Instruction::Invokevirtual(self.bool_unbox));
                self.pop_type();
                self.push_type(VerificationType::Integer);
            }
            _ => {} // already a reference type, no unboxing needed
        }
    }

    /// Ensure a FunN interface is registered in the constant pool.
    fn ensure_fun_interface(&mut self, arity: u8) -> Result<(), CodegenError> {
        if self.fun_classes.contains_key(&arity) {
            return Ok(());
        }
        let class_name = format!("Fun{arity}");
        let class_idx = self.cp.add_class(&class_name)?;
        let class_desc = format!("L{class_name};");
        self.class_descriptors.insert(class_idx, class_desc);

        // Build apply descriptor: (Object, ..., Object)Object
        let mut apply_desc = String::from("(");
        for _ in 0..arity {
            apply_desc.push_str("Ljava/lang/Object;");
        }
        apply_desc.push_str(")Ljava/lang/Object;");

        let apply_ref = self.cp.add_interface_method_ref(class_idx, "apply", &apply_desc)?;
        self.fun_classes.insert(arity, class_idx);
        self.fun_apply_refs.insert(arity, apply_ref);
        Ok(())
    }

    /// Initialize the LambdaMetafactory bootstrap method handle (lazy, once).
    fn ensure_metafactory(&mut self) -> Result<u16, CodegenError> {
        if let Some(handle) = self.metafactory_handle {
            return Ok(handle);
        }
        let lmf_class = self.cp.add_class("java/lang/invoke/LambdaMetafactory")?;
        let metafactory_ref = self.cp.add_method_ref(
            lmf_class,
            "metafactory",
            "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;",
        )?;
        let handle = self.cp.add_method_handle(ReferenceKind::InvokeStatic, metafactory_ref)?;
        self.metafactory_handle = Some(handle);
        Ok(handle)
    }

    /// Compile a lambda expression.
    fn compile_lambda(
        &mut self,
        params: &[krypton_parser::ast::Param],
        body: &Expr,
        span: &Span,
    ) -> Result<JvmType, CodegenError> {
        let arity = params.len() as u8;

        // Look up lambda types from typechecker
        let (param_jvm_types, _return_jvm_type) = self.lambda_types.get(span).cloned()
            .ok_or_else(|| CodegenError::TypeError("lambda type info not found".to_string()))?;

        // Ensure FunN interface exists
        self.ensure_fun_interface(arity)?;
        let fun_class_idx = self.fun_classes[&arity];

        // Find captured variables: scan body for Var names that are in self.locals but not lambda params
        let param_names: std::collections::HashSet<&str> = params.iter().map(|p| p.name.as_str()).collect();
        let mut captures: Vec<(String, u16, JvmType)> = Vec::new();
        self.collect_captures(body, &param_names, &mut captures);
        // Deduplicate
        let mut seen = std::collections::HashSet::new();
        captures.retain(|(name, _, _)| seen.insert(name.clone()));

        // Save compiler state for the outer method
        let saved_code = std::mem::take(&mut self.code);
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_local_types = std::mem::take(&mut self.local_types);
        let saved_next_local = self.next_local;
        let saved_stack_types = std::mem::take(&mut self.stack_types);
        let saved_frames = std::mem::take(&mut self.frames);
        let saved_fn_params = std::mem::take(&mut self.fn_params);
        let saved_fn_return_type = self.fn_return_type.take();
        let saved_local_fn_info = std::mem::take(&mut self.local_fn_info);

        // Reset for lambda body compilation
        self.code.clear();
        self.locals.clear();
        self.local_types.clear();
        self.next_local = 0;
        self.stack_types.clear();
        self.frames.clear();
        self.fn_params.clear();
        self.fn_return_type = None;

        // Register captured vars as first params (all boxed to Object)
        for (cap_name, _, cap_type) in &captures {
            let slot = self.next_local;
            self.locals.insert(cap_name.clone(), (slot, *cap_type));
            self.local_types.push(VerificationType::Object { cpool_index: self.object_class });
            self.next_local += 1;
        }

        // Register lambda params (all as Object, will unbox)
        let mut lambda_param_slots = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let slot = self.next_local;
            // Store as Object initially
            self.locals.insert(p.name.clone(), (slot, JvmType::StructRef(self.object_class)));
            self.local_types.push(VerificationType::Object { cpool_index: self.object_class });
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
                self.push_type(VerificationType::Object { cpool_index: self.object_class });
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
                self.local_types.extend(vtypes);
                self.locals.insert(p.name.clone(), (new_slot, actual_type));
            }
        }

        // Also unbox captured vars if they are primitive types
        for (cap_name, _, cap_type) in &captures {
            let actual_type = *cap_type;
            if matches!(actual_type, JvmType::Long | JvmType::Double | JvmType::Int) {
                let (slot, _) = self.locals[cap_name];
                self.emit(Instruction::Aload(slot as u8));
                self.push_type(VerificationType::Object { cpool_index: self.object_class });
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
                self.local_types.extend(vtypes);
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
        let lambda_name = format!("lambda${}", self.lambda_counter);
        self.lambda_counter += 1;

        // Descriptor: all Object params (captures + lambda params) -> Object
        let total_params = captures.len() + params.len();
        let mut lambda_desc = String::from("(");
        for _ in 0..total_params {
            lambda_desc.push_str("Ljava/lang/Object;");
        }
        lambda_desc.push_str(")Ljava/lang/Object;");

        let lambda_name_idx = self.cp.add_utf8(&lambda_name)?;
        let lambda_desc_idx = self.cp.add_utf8(&lambda_desc)?;

        let stack_map_frames = self.build_stack_map_frames();
        let code_attributes = if stack_map_frames.is_empty() {
            vec![]
        } else {
            vec![Attribute::StackMapTable {
                name_index: self.smt_name,
                frames: stack_map_frames,
            }]
        };

        let lambda_method = Method {
            access_flags: MethodAccessFlags::PRIVATE | MethodAccessFlags::STATIC | MethodAccessFlags::SYNTHETIC,
            name_index: lambda_name_idx,
            descriptor_index: lambda_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: self.code_utf8,
                max_stack: 20,
                max_locals: self.next_local,
                code: std::mem::take(&mut self.code),
                exception_table: vec![],
                attributes: code_attributes,
            }],
        };

        self.lambda_methods.push(lambda_method);

        // Restore compiler state
        self.code = saved_code;
        self.locals = saved_locals;
        self.local_types = saved_local_types;
        self.next_local = saved_next_local;
        self.stack_types = saved_stack_types;
        self.frames = saved_frames;
        self.fn_params = saved_fn_params;
        self.fn_return_type = saved_fn_return_type;
        self.local_fn_info = saved_local_fn_info;

        // Now set up invokedynamic in the outer method

        // 1. Ensure metafactory bootstrap handle
        let bsm_handle = self.ensure_metafactory()?;

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
        let bsm_index = self.bootstrap_methods.len() as u16;
        self.bootstrap_methods.push(BootstrapMethod {
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
            self.pop_type(); // each boxed capture is a single Object ref
        }

        // Push result type
        let result_type = JvmType::StructRef(fun_class_idx);
        self.push_jvm_type(result_type);

        Ok(result_type)
    }

    /// Collect captured variables from an expression.
    fn collect_captures(
        &self,
        expr: &Expr,
        param_names: &std::collections::HashSet<&str>,
        captures: &mut Vec<(String, u16, JvmType)>,
    ) {
        match expr {
            Expr::Var { name, .. } => {
                if !param_names.contains(name.as_str()) {
                    if let Some(&(slot, ty)) = self.locals.get(name) {
                        captures.push((name.clone(), slot, ty));
                    }
                }
            }
            Expr::BinaryOp { lhs, rhs, .. } => {
                self.collect_captures(lhs, param_names, captures);
                self.collect_captures(rhs, param_names, captures);
            }
            Expr::UnaryOp { operand, .. } => {
                self.collect_captures(operand, param_names, captures);
            }
            Expr::If { cond, then_, else_, .. } => {
                self.collect_captures(cond, param_names, captures);
                self.collect_captures(then_, param_names, captures);
                self.collect_captures(else_, param_names, captures);
            }
            Expr::Let { value, body, .. } => {
                self.collect_captures(value, param_names, captures);
                if let Some(body) = body {
                    self.collect_captures(body, param_names, captures);
                }
            }
            Expr::Do { exprs, .. } => {
                for e in exprs {
                    self.collect_captures(e, param_names, captures);
                }
            }
            Expr::App { func, args, .. } => {
                self.collect_captures(func, param_names, captures);
                for a in args {
                    self.collect_captures(a, param_names, captures);
                }
            }
            Expr::Lambda { body, params, .. } => {
                // For nested lambdas, the inner params shadow
                let mut inner_params = param_names.clone();
                for p in params {
                    inner_params.insert(&p.name);
                }
                self.collect_captures(body, &inner_params, captures);
            }
            _ => {}
        }
    }

    fn compile_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // 1. Compile scrutinee and store in temp local
        let scrutinee_type = self.compile_expr(scrutinee, false)?;
        let scrutinee_slot = self.next_local;
        self.next_local += 1;
        self.emit(Instruction::Astore(scrutinee_slot as u8));
        self.pop_jvm_type(scrutinee_type);
        let vtypes = self.jvm_type_to_vtypes(scrutinee_type);
        self.local_types.extend(vtypes);

        let stack_at_match = self.stack_types.clone();
        let locals_at_match = self.locals.clone();
        let local_types_at_match = self.local_types.clone();
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
            self.stack_types = stack_at_match.clone();
            self.locals = locals_at_match.clone();
            self.local_types = local_types_at_match.clone();
            self.next_local = next_local_at_match;

            // Record frame at this arm's start (branch target) — except first arm
            if i > 0 {
                let arm_start = self.code.len() as u16;
                self.record_frame(arm_start);
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
            if matches!(target_type, JvmType::StructRef(idx) if idx == self.object_class)
                && !matches!(arm_type, JvmType::StructRef(_) | JvmType::Ref)
            {
                self.box_if_needed(arm_type);
                // Fix stack type to match target (Object)
                self.pop_type();
                self.push_type(VerificationType::Object {
                    cpool_index: self.object_class,
                });
            }
            // Unbox Object to primitive if needed
            else if !matches!(target_type, JvmType::StructRef(_) | JvmType::Ref)
                && matches!(arm_type, JvmType::StructRef(idx) if idx == self.object_class)
            {
                self.unbox_if_needed(target_type);
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
        self.record_frame(after_match);

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
                let sum_name = self.variant_to_sum.get(name).cloned().ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown variant: {name}"))
                })?;
                let sum_info = &self.sum_type_info[&sum_name];
                let vi = &sum_info.variants[name];
                let variant_class_index = vi.class_index;
                let fields = vi.fields.clone();
                let field_refs = vi.field_refs.clone();

                // instanceof check
                self.emit(Instruction::Aload(scrutinee_slot as u8));
                self.push_jvm_type(scrutinee_type);
                self.emit(Instruction::Instanceof(variant_class_index));
                self.pop_jvm_type(scrutinee_type);
                self.push_type(VerificationType::Integer);

                // ifeq placeholder → next arm
                let ifeq_idx = self.code.len();
                self.emit(Instruction::Ifeq(0)); // placeholder
                self.pop_type(); // consume int from instanceof

                // If has sub-patterns, checkcast and extract fields
                if !args.is_empty() {
                    // checkcast and store cast ref in a local
                    self.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.push_jvm_type(scrutinee_type);
                    self.emit(Instruction::Checkcast(variant_class_index));
                    self.pop_jvm_type(scrutinee_type);
                    self.push_type(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    let cast_slot = self.next_local;
                    self.next_local += 1;
                    self.emit(Instruction::Astore(cast_slot as u8));
                    self.pop_type();
                    self.local_types.push(VerificationType::Object {
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
                        self.push_type(VerificationType::Object {
                            cpool_index: variant_class_index,
                        });
                        self.emit(Instruction::Getfield(field_ref));
                        self.pop_type(); // pop cast ref
                        if *is_erased {
                            self.push_type(VerificationType::Object {
                                cpool_index: self.string_class,
                            });
                        } else {
                            self.push_jvm_type(*field_jvm_type);
                        }

                        match sub_pat {
                            Pattern::Var { name: var_name, .. } => {
                                // Erased fields stay as Object refs — no unboxing here.
                                // Unboxing happens at monomorphic call sites.
                                let actual_type = if *is_erased {
                                    JvmType::StructRef(self.object_class)
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
                                self.local_types.extend(vtypes);
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
                                self.pop_type(); // pop the field value (object ref)
                                self.local_types.push(VerificationType::Object {
                                    cpool_index: match nested_type {
                                        JvmType::StructRef(idx) => idx,
                                        _ => self.string_class,
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
                                self.pop_type();
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
                self.local_types.extend(vtypes);
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
                self.local_types.extend(vtypes);
                self.locals.insert(name.clone(), (var_slot, scrutinee_type));
                Ok(())
            }
            Pattern::Constructor { name, args, .. } => {
                // Last arm constructor — still need to extract fields
                let sum_name = self.variant_to_sum.get(name).cloned().ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown variant: {name}"))
                })?;
                let sum_info = &self.sum_type_info[&sum_name];
                let vi = &sum_info.variants[name];
                let variant_class_index = vi.class_index;
                let fields = vi.fields.clone();
                let field_refs = vi.field_refs.clone();

                if !args.is_empty() {
                    self.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.push_jvm_type(scrutinee_type);
                    self.emit(Instruction::Checkcast(variant_class_index));
                    self.pop_jvm_type(scrutinee_type);
                    self.push_type(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    let cast_slot = self.next_local;
                    self.next_local += 1;
                    self.emit(Instruction::Astore(cast_slot as u8));
                    self.pop_type();
                    self.local_types.push(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    for (j, sub_pat) in args.iter().enumerate() {
                        if matches!(sub_pat, Pattern::Wildcard { .. }) {
                            continue;
                        }
                        let (_fname, field_jvm_type, is_erased) = &fields[j];
                        let field_ref = field_refs[j];

                        self.emit(Instruction::Aload(cast_slot as u8));
                        self.push_type(VerificationType::Object {
                            cpool_index: variant_class_index,
                        });
                        self.emit(Instruction::Getfield(field_ref));
                        self.pop_type();
                        if *is_erased {
                            self.push_type(VerificationType::Object {
                                cpool_index: self.string_class,
                            });
                        } else {
                            self.push_jvm_type(*field_jvm_type);
                        }

                        if let Pattern::Var { name: var_name, .. } = sub_pat {
                            let actual_type = if *is_erased {
                                JvmType::StructRef(self.object_class)
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
                            self.local_types.extend(vtypes);
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
                let sum_name = self.variant_to_sum.get(name).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown variant: {name}"))
                })?;
                let sum_info = &self.sum_type_info[sum_name];
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
            let sum_name = self.variant_to_sum.get(name).cloned().ok_or_else(|| {
                CodegenError::TypeError(format!("unknown variant: {name}"))
            })?;
            let sum_info = &self.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            let variant_class_index = vi.class_index;
            let fields = vi.fields.clone();
            let field_refs = vi.field_refs.clone();

            // instanceof check
            self.emit(Instruction::Aload(scrutinee_slot as u8));
            self.push_type(VerificationType::Object {
                cpool_index: match scrutinee_type {
                    JvmType::StructRef(idx) => idx,
                    _ => self.string_class,
                },
            });
            self.emit(Instruction::Instanceof(variant_class_index));
            self.pop_type();
            self.push_type(VerificationType::Integer);

            // ifeq → same outer target (we'll add a new ifeq that also jumps to next arm)
            let nested_ifeq_idx = self.code.len();
            self.emit(Instruction::Ifeq(0)); // placeholder — will share target with outer
            self.pop_type();

            // Extract fields if needed
            if !args.is_empty() {
                self.emit(Instruction::Aload(scrutinee_slot as u8));
                self.push_type(VerificationType::Object {
                    cpool_index: match scrutinee_type {
                        JvmType::StructRef(idx) => idx,
                        _ => self.string_class,
                    },
                });
                self.emit(Instruction::Checkcast(variant_class_index));
                self.pop_type();
                self.push_type(VerificationType::Object {
                    cpool_index: variant_class_index,
                });

                let cast_slot = self.next_local;
                self.next_local += 1;
                self.emit(Instruction::Astore(cast_slot as u8));
                self.pop_type();
                self.local_types.push(VerificationType::Object {
                    cpool_index: variant_class_index,
                });

                for (j, sub_pat) in args.iter().enumerate() {
                    if matches!(sub_pat, Pattern::Wildcard { .. }) {
                        continue;
                    }
                    let (_fname, field_jvm_type, is_erased) = &fields[j];
                    let field_ref = field_refs[j];

                    self.emit(Instruction::Aload(cast_slot as u8));
                    self.push_type(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });
                    self.emit(Instruction::Getfield(field_ref));
                    self.pop_type();
                    if *is_erased {
                        self.push_type(VerificationType::Object {
                            cpool_index: self.string_class,
                        });
                    } else {
                        self.push_jvm_type(*field_jvm_type);
                    }

                    match sub_pat {
                        Pattern::Var { name: var_name, .. } => {
                            let actual_type = if *is_erased {
                                JvmType::StructRef(self.object_class)
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
                            self.local_types.extend(vtypes);
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
                            self.pop_type();
                            self.local_types.push(VerificationType::Object {
                                cpool_index: match nested_type {
                                    JvmType::StructRef(idx) => idx,
                                    _ => self.string_class,
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

    fn compile_do(&mut self, exprs: &[Expr], in_tail: bool) -> Result<JvmType, CodegenError> {
        let mut last_type = JvmType::Int;
        for (i, expr) in exprs.iter().enumerate() {
            let is_last = i == exprs.len() - 1;
            let is_let_stmt =
                matches!(expr, Expr::Let { body: None, .. });

            let expr_tail = in_tail && is_last;
            let ty = self.compile_expr(expr, expr_tail)?;

            if !is_last && !is_let_stmt {
                // Pop the value — it's not used
                match ty {
                    JvmType::Long | JvmType::Double => {
                        self.emit(Instruction::Pop2);
                        self.pop_type_n(2);
                    }
                    _ => {
                        self.emit(Instruction::Pop);
                        self.pop_type();
                    }
                }
            }
            last_type = ty;
        }
        Ok(last_type)
    }

    /// Compile a function declaration into a JVM Method.
    fn compile_function(&mut self, decl: &FnDecl) -> Result<Method, CodegenError> {
        self.reset_method_state();

        // Look up the function's type info
        let info = self.functions.get(&decl.name).ok_or_else(|| {
            CodegenError::UndefinedVariable(decl.name.clone())
        })?;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;

        // Get typechecker types for this function's params (for detecting Fn-typed params)
        let tc_types = self.fn_tc_types.get(&decl.name).cloned();

        // Register parameters as locals and save fn_params for recur
        let mut fn_params = Vec::new();
        for (i, (param, &jvm_ty)) in decl.params.iter().zip(param_types.iter()).enumerate() {
            let slot = self.next_local;
            let slot_size: u16 = match jvm_ty {
                JvmType::Long | JvmType::Double => 2,
                _ => 1,
            };
            self.locals.insert(param.name.clone(), (slot, jvm_ty));
            fn_params.push((slot, jvm_ty));
            self.next_local += slot_size;

            // Track local verification types
            let vtypes = self.jvm_type_to_vtypes(jvm_ty);
            self.local_types.extend(vtypes);

            // If this param is function-typed, register in local_fn_info
            if let Some((ref tc_param_types, _)) = tc_types {
                if let Type::Fn(inner_params, inner_ret) = &tc_param_types[i] {
                    let inner_param_jvm: Vec<JvmType> = inner_params
                        .iter()
                        .map(|t| self.type_to_jvm(t))
                        .collect::<Result<_, _>>()?;
                    let inner_ret_jvm = self.type_to_jvm(inner_ret)?;
                    let arity = inner_params.len() as u8;
                    self.ensure_fun_interface(arity)?;
                    self.local_fn_info.insert(param.name.clone(), (inner_param_jvm, inner_ret_jvm));
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
        if matches!(body_type, JvmType::StructRef(idx) if idx == self.object_class)
            && !matches!(return_type, JvmType::StructRef(_) | JvmType::Ref)
        {
            self.unbox_if_needed(return_type);
        }
        // If body type is primitive but return type is Object, box
        else if matches!(return_type, JvmType::StructRef(idx) if idx == self.object_class)
            && !matches!(body_type, JvmType::StructRef(_) | JvmType::Ref)
        {
            self.box_if_needed(body_type);
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
        let descriptor = self.build_descriptor(&param_types, return_type);
        let name_idx = self.cp.add_utf8(&decl.name)?;
        let desc_idx = self.cp.add_utf8(&descriptor)?;

        // Build StackMapTable
        let stack_map_frames = self.build_stack_map_frames();
        let code_attributes = if stack_map_frames.is_empty() {
            vec![]
        } else {
            vec![Attribute::StackMapTable {
                name_index: self.smt_name,
                frames: stack_map_frames,
            }]
        };

        Ok(Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![Attribute::Code {
                name_index: self.code_utf8,
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
            name_index: self.init_name,
            descriptor_index: self.init_desc,
            attributes: vec![Attribute::Code {
                name_index: self.code_utf8,
                max_stack: 1,
                max_locals: 1,
                code: vec![
                    Instruction::Aload_0,
                    Instruction::Invokespecial(self.object_init),
                    Instruction::Return,
                ],
                exception_table: vec![],
                attributes: vec![],
            }],
        };

        // Build StackMapTable if we have frames
        let stack_map_frames = self.build_stack_map_frames();
        let code_attributes = if stack_map_frames.is_empty() {
            vec![]
        } else {
            vec![Attribute::StackMapTable {
                name_index: self.smt_name,
                frames: stack_map_frames,
            }]
        };

        let main_method = Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
            name_index: main_name,
            descriptor_index: main_desc,
            attributes: vec![Attribute::Code {
                name_index: self.code_utf8,
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
        methods.extend(std::mem::take(&mut self.lambda_methods));
        methods.push(main_method);

        // Build class attributes (BootstrapMethods if any)
        let mut class_attributes = Vec::new();
        if !self.bootstrap_methods.is_empty() {
            let bsm_name = self.cp.add_utf8("BootstrapMethods")?;
            class_attributes.push(Attribute::BootstrapMethods {
                name_index: bsm_name,
                methods: std::mem::take(&mut self.bootstrap_methods),
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
            JvmType::StructRef(_) => FieldType::Object(name.to_string()),
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
    let variant_str = cp.add_string(variant_name)?;
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
    compiler
        .class_descriptors
        .insert(object_class, "Ljava/lang/Object;".to_string());

    // Run the typechecker to get function types (includes constructors) and lambda types
    let module_type_info = infer_module(module).map_err(|e| {
        CodegenError::TypeError(format!("{e:?}"))
    })?;
    let type_info = module_type_info.fn_types;

    // We'll convert lambda types after struct/sum types are registered
    // (so type_to_jvm can resolve Named types). Store raw lambda types for now.
    let raw_lambda_types = module_type_info.lambda_types;

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
                        if let Some(si) = compiler.struct_info.get(name.as_str()) {
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
        compiler
            .class_descriptors
            .insert(class_index, class_desc.clone());

        // Add constructor methodref in main class's cpool
        let mut ctor_desc = String::from("(");
        for (_, jt) in &jvm_fields {
            ctor_desc.push_str(&compiler.jvm_type_descriptor(*jt));
        }
        ctor_desc.push_str(")V");
        let constructor_ref =
            compiler
                .cp
                .add_method_ref(class_index, "<init>", &ctor_desc)?;

        // Add accessor methodrefs in main class's cpool
        let mut accessor_refs = HashMap::new();
        for (fname, jt) in &jvm_fields {
            let ret_desc = compiler.jvm_type_descriptor(*jt);
            let method_desc = format!("(){ret_desc}");
            let accessor_ref =
                compiler
                    .cp
                    .add_method_ref(class_index, fname, &method_desc)?;
            accessor_refs.insert(fname.clone(), accessor_ref);
        }

        compiler.struct_info.insert(
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
            generate_struct_class(struct_name, &jvm_fields, &compiler.class_descriptors)?;
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
        compiler
            .class_descriptors
            .insert(interface_class_index, interface_desc);

        let mut variant_infos = HashMap::new();
        let variant_names: Vec<&str> = variants.iter().map(|v| v.name.as_str()).collect();

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
            let variant_class_index = compiler.cp.add_class(&variant.name)?;
            let variant_desc = format!("L{};", variant.name);
            compiler
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

            compiler
                .variant_to_sum
                .insert(variant.name.clone(), sum_name.clone());

            variant_infos.insert(
                variant.name.clone(),
                VariantInfo {
                    class_index: variant_class_index,
                    class_name: variant.name.clone(),
                    fields: fields.clone(),
                    constructor_ref,
                    field_refs: main_field_refs,
                },
            );

            // Generate variant class file
            let variant_bytes =
                generate_variant_class(&variant.name, sum_name, &fields)?;
            result_classes.push((variant.name.clone(), variant_bytes));
        }

        compiler.sum_type_info.insert(
            sum_name.clone(),
            SumTypeInfo {
                interface_class_index,
                variants: variant_infos,
            },
        );

        // Generate sealed interface class file
        let interface_bytes = generate_sealed_interface_class(sum_name, &variant_names)?;
        result_classes.push((sum_name.clone(), interface_bytes));
    }

    // Pre-scan for function-typed params so we can register FunN interfaces first
    for (name, scheme) in &type_info {
        if let Type::Fn(param_tys, _) = &scheme.ty {
            if compiler.struct_info.contains_key(name)
                || compiler.variant_to_sum.contains_key(name)
            {
                continue;
            }
            for pt in param_tys {
                if let Type::Fn(inner_params, _) = pt {
                    let arity = inner_params.len() as u8;
                    compiler.ensure_fun_interface(arity)?;
                }
            }
        }
    }

    // Also pre-scan lambda types to register FunN interfaces
    for (_, (param_types, _)) in &raw_lambda_types {
        let arity = param_types.len() as u8;
        compiler.ensure_fun_interface(arity)?;
    }

    // Convert lambda types from Type to JvmType
    for (span, (param_types, ret_type)) in &raw_lambda_types {
        let jvm_params: Vec<JvmType> = param_types
            .iter()
            .map(|t| compiler.type_to_jvm(t))
            .collect::<Result<_, _>>()?;
        let jvm_ret = compiler.type_to_jvm(ret_type)?;
        compiler.lambda_types.insert(*span, (jvm_params, jvm_ret));
    }

    // Register all functions (including main) in the function registry.
    // Skip constructor entries (they're handled as struct/variant constructors).
    for (name, scheme) in &type_info {
        if let Type::Fn(param_tys, ret_ty) = &scheme.ty {
            // Skip if this is a struct constructor or variant constructor
            if compiler.struct_info.contains_key(name)
                || compiler.variant_to_sum.contains_key(name)
            {
                continue;
            }
            let param_types: Vec<JvmType> = param_tys
                .iter()
                .map(|t| compiler.type_to_jvm(t))
                .collect::<Result<_, _>>()?;
            let return_type = compiler.type_to_jvm(ret_ty)?;
            let jvm_name = if name == "main" {
                "krypton_main"
            } else {
                name.as_str()
            };
            let descriptor = compiler.build_descriptor(&param_types, return_type);
            let method_ref =
                compiler.cp.add_method_ref(this_class, jvm_name, &descriptor)?;
            compiler.functions.insert(
                name.clone(),
                FunctionInfo {
                    method_ref,
                    param_types,
                    return_type,
                },
            );
            // Store TC types for detecting Fn-typed params in compile_function
            compiler.fn_tc_types.insert(
                name.clone(),
                (param_tys.clone(), (**ret_ty).clone()),
            );
        }
    }

    // Collect all function declarations
    let fn_decls: Vec<&FnDecl> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Compile all functions (including main) as static methods
    let mut extra_methods = Vec::new();
    for decl in &fn_decls {
        let mut method = compiler.compile_function(decl)?;
        // Rename main → krypton_main in the method
        if decl.name == "main" {
            let name_idx = compiler.cp.add_utf8("krypton_main")?;
            method.name_index = name_idx;
        }
        extra_methods.push(method);
    }

    // Build JVM main(String[])V — calls krypton_main and prints the result
    let main_info = compiler.functions.get("main").ok_or(CodegenError::NoMainFunction)?;
    let krypton_main_ref = main_info.method_ref;
    let main_return_type = main_info.return_type;

    compiler.reset_method_state();
    compiler.next_local = 1; // slot 0 = String[] args
    let string_arr_class = compiler.cp.add_class("[Ljava/lang/String;")?;
    compiler.local_types = vec![VerificationType::Object {
        cpool_index: string_arr_class,
    }];

    // Emit: getstatic System.out
    let system_out = compiler.system_out;
    compiler.emit(Instruction::Getstatic(system_out));
    compiler.push_type(VerificationType::Object {
        cpool_index: compiler.ps_class,
    });

    // Call krypton_main
    compiler.emit(Instruction::Invokestatic(krypton_main_ref));
    compiler.push_jvm_type(main_return_type);

    // Emit the appropriate println call
    let println_ref = match main_return_type {
        JvmType::Long => compiler.println_long,
        JvmType::Double => compiler.println_double,
        JvmType::Ref => compiler.println_string,
        JvmType::Int => compiler.println_bool,
        JvmType::StructRef(_) => compiler.println_object,
    };
    compiler.emit(Instruction::Invokevirtual(println_ref));

    // Pop println args + PrintStream from stack tracker
    compiler.pop_jvm_type(main_return_type);
    compiler.pop_type(); // PrintStream

    compiler.emit(Instruction::Return);

    // Generate FunN interface class files
    let fun_arities: Vec<u8> = compiler.fun_classes.keys().copied().collect();
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
