use std::collections::{BTreeMap, HashMap};

use alang_parser::ast::{BinOp, Decl, Expr, FnDecl, Lit, Module};
use alang_typechecker::infer::infer_module;
use alang_typechecker::types::Type;
use ristretto_classfile::attributes::{Attribute, Instruction, StackFrame, VerificationType};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Method, MethodAccessFlags, Version,
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

fn type_to_jvm(ty: &Type) -> Result<JvmType, CodegenError> {
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

fn jvm_type_to_descriptor(ty: JvmType) -> &'static str {
    match ty {
        JvmType::Long => "J",
        JvmType::Double => "D",
        JvmType::Int => "Z",
        JvmType::Ref => "Ljava/lang/String;",
    }
}

fn build_method_descriptor(params: &[JvmType], ret: JvmType) -> String {
    let mut desc = String::from("(");
    for p in params {
        desc.push_str(jvm_type_to_descriptor(*p));
    }
    desc.push(')');
    desc.push_str(jvm_type_to_descriptor(ret));
    desc
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
    // Function codegen support
    this_class: u16,
    functions: HashMap<String, FunctionInfo>,
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
            fn_params: Vec::new(),
            fn_return_type: None,
        };

        Ok((compiler, this_class, object_class))
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
            JvmType::Int | JvmType::Ref => self.pop_type(),
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
            JvmType::Ref => Instruction::Astore(slot as u8),
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
            JvmType::Ref => Instruction::Aload(slot as u8),
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
                JvmType::Ref => Instruction::Astore(slot as u8),
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
            JvmType::Ref => Instruction::Areturn,
        };
        self.emit(ret_instr);

        // Build the method descriptor string for the constant pool
        let descriptor = build_method_descriptor(&param_types, return_type);
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

/// Compile a module to JVM bytecode.
pub fn compile_module(module: &Module, class_name: &str) -> Result<Vec<u8>, CodegenError> {
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

    // Run the typechecker to get function types
    let type_info = infer_module(module).map_err(|e| {
        CodegenError::TypeError(format!("{e:?}"))
    })?;

    // Register all functions (including main) in the function registry.
    // Main gets a JVM-internal name "alang_main" to avoid clashing with JVM main(String[]).
    for (name, scheme) in &type_info {
        if let Type::Fn(param_tys, ret_ty) = &scheme.ty {
            let param_types: Vec<JvmType> = param_tys
                .iter()
                .map(type_to_jvm)
                .collect::<Result<_, _>>()?;
            let return_type = type_to_jvm(ret_ty)?;
            let jvm_name = if name == "main" {
                "alang_main"
            } else {
                name.as_str()
            };
            let descriptor = build_method_descriptor(&param_types, return_type);
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
        // Rename main → alang_main in the method
        if decl.name == "main" {
            let name_idx = compiler.cp.add_utf8("alang_main")?;
            method.name_index = name_idx;
        }
        extra_methods.push(method);
    }

    // Build JVM main(String[])V — calls alang_main and prints the result
    let main_info = compiler.functions.get("main").ok_or(CodegenError::NoMainFunction)?;
    let alang_main_ref = main_info.method_ref;
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

    // Call alang_main
    compiler.emit(Instruction::Invokestatic(alang_main_ref));
    compiler.push_jvm_type(main_return_type);

    // Emit the appropriate println call
    let println_ref = match main_return_type {
        JvmType::Long => compiler.println_long,
        JvmType::Double => compiler.println_double,
        JvmType::Ref => compiler.println_string,
        JvmType::Int => compiler.println_bool,
    };
    compiler.emit(Instruction::Invokevirtual(println_ref));

    // Pop println args + PrintStream from stack tracker
    compiler.pop_jvm_type(main_return_type);
    compiler.pop_type(); // PrintStream

    compiler.emit(Instruction::Return);

    compiler.build_class(this_class, object_class, extra_methods)
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
