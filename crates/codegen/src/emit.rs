use std::collections::{BTreeMap, HashMap};

use krypton_parser::ast::{BinOp, Decl, Expr, FnDecl, Lit, Module, TypeDeclKind, TypeExpr};
use krypton_typechecker::infer::infer_module;
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{Attribute, Instruction, StackFrame, VerificationType};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Field, FieldAccessFlags, FieldType, Method,
    MethodAccessFlags, Version,
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
    // Recur support: parameter slots and return type for current function
    fn_params: Vec<(u16, JvmType)>,
    fn_return_type: Option<JvmType>,
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
            fn_params: Vec::new(),
            fn_return_type: None,
        };

        Ok((compiler, this_class, object_class))
    }

    /// Map a typechecker Type to a JvmType, using struct_info for Named types.
    fn type_to_jvm(&self, ty: &Type) -> Result<JvmType, CodegenError> {
        match ty {
            Type::Named(name, _) => {
                let info = self.struct_info.get(name).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown struct type: {name}"))
                })?;
                Ok(JvmType::StructRef(info.class_index))
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

        // Look up function info (need to clone out to avoid borrow conflict)
        let info = self
            .functions
            .get(name)
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;
        let method_ref = info.method_ref;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;

        // Compile each argument
        for arg in args {
            self.compile_expr(arg, false)?;
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

        // Register parameters as locals and save fn_params for recur
        let mut fn_params = Vec::new();
        for (param, &jvm_ty) in decl.params.iter().zip(param_types.iter()) {
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

        // Emit typed return
        let ret_instr = match body_type {
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
        methods.push(main_method);

        let class_file = ClassFile {
            version: JAVA_21,
            access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
            constant_pool: self.cp,
            this_class,
            super_class: object_class,
            methods,
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

    // Run the typechecker to get function types (includes constructors)
    let type_info = infer_module(module).map_err(|e| {
        CodegenError::TypeError(format!("{e:?}"))
    })?;

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

    // Register all functions (including main) in the function registry.
    // Skip constructor entries (they're handled as struct constructors).
    for (name, scheme) in &type_info {
        if let Type::Fn(param_tys, ret_ty) = &scheme.ty {
            // Skip if this is a struct constructor
            if compiler.struct_info.contains_key(name) {
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

    let main_bytes = compiler.build_class(this_class, object_class, extra_methods)?;
    result_classes.push((class_name.to_string(), main_bytes));

    Ok(result_classes)
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
