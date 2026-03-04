use std::collections::HashMap;

use alang_parser::ast::{BinOp, Decl, Expr, Lit, Module};
use ristretto_classfile::attributes::{Attribute, Instruction};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Method, MethodAccessFlags, Version,
};

/// Java 21 class file version (major 65).
const JAVA_21: Version = Version::Java21 { minor: 0 };

/// Java 6 class file version (major 50) — no StackMapTable required.
const JAVA_6: Version = Version::Java6 { minor: 0 };

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
        }
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

        let compiler = Compiler {
            cp,
            code: Vec::new(),
            locals: HashMap::new(),
            next_local: 1, // slot 0 = String[] args
            code_utf8,
            object_init,
            init_name,
            init_desc,
            system_out,
            println_long,
            println_string,
            println_double,
            println_bool,
        };

        Ok((compiler, this_class, object_class))
    }

    fn emit(&mut self, instr: Instruction) {
        self.code.push(instr);
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<JvmType, CodegenError> {
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
            } => self.compile_if(cond, then_, else_),
            Expr::Let {
                name, value, body, ..
            } => self.compile_let(name, value, body),
            Expr::Var { name, .. } => self.compile_var(name),
            Expr::Do { exprs, .. } => self.compile_do(exprs),
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
                Ok(JvmType::Long)
            }
            Lit::Float(f) => {
                let idx = self.cp.add_double(*f)?;
                self.emit(Instruction::Ldc2_w(idx));
                Ok(JvmType::Double)
            }
            Lit::Bool(b) => {
                self.emit(if *b {
                    Instruction::Iconst_1
                } else {
                    Instruction::Iconst_0
                });
                Ok(JvmType::Int)
            }
            Lit::String(s) => {
                let idx = self.cp.add_string(s)?;
                if idx <= 255 {
                    self.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.emit(Instruction::Ldc_w(idx));
                }
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
                self.compile_expr(lhs)?;
                self.compile_expr(rhs)?;
                let instr = match op {
                    BinOp::Add => Instruction::Ladd,
                    BinOp::Sub => Instruction::Lsub,
                    BinOp::Mul => Instruction::Lmul,
                    BinOp::Div => Instruction::Ldiv,
                    _ => unreachable!(),
                };
                self.emit(instr);
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
        self.compile_expr(lhs)?;
        self.compile_expr(rhs)?;
        self.emit(Instruction::Lcmp);

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
        self.emit(Instruction::Iconst_1);
        self.emit(Instruction::Goto(after_target));
        self.emit(Instruction::Iconst_0);

        Ok(JvmType::Int)
    }

    fn compile_if(
        &mut self,
        cond: &Expr,
        then_: &Expr,
        else_: &Expr,
    ) -> Result<JvmType, CodegenError> {
        // Compile condition (produces Int 0/1 on stack)
        self.compile_expr(cond)?;

        // Emit Ifeq with placeholder — will be patched with instruction index
        let ifeq_idx = self.code.len();
        self.emit(Instruction::Ifeq(0)); // placeholder

        // Compile then branch
        let then_type = self.compile_expr(then_)?;

        // Emit Goto with placeholder
        let goto_idx = self.code.len();
        self.emit(Instruction::Goto(0)); // placeholder

        // else starts at this instruction index
        let else_start = self.code.len() as u16;

        // Compile else branch
        let _else_type = self.compile_expr(else_)?;

        let after_else = self.code.len() as u16;

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
    ) -> Result<JvmType, CodegenError> {
        let ty = self.compile_expr(value)?;
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

        if let Some(body) = body {
            self.compile_expr(body)
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
        Ok(ty)
    }

    fn compile_do(&mut self, exprs: &[Expr]) -> Result<JvmType, CodegenError> {
        let mut last_type = JvmType::Int;
        for (i, expr) in exprs.iter().enumerate() {
            let is_last = i == exprs.len() - 1;
            let is_let_stmt =
                matches!(expr, Expr::Let { body: None, .. });

            let ty = self.compile_expr(expr)?;

            if !is_last && !is_let_stmt {
                // Pop the value — it's not used
                match ty {
                    JvmType::Long | JvmType::Double => self.emit(Instruction::Pop2),
                    _ => self.emit(Instruction::Pop),
                }
            }
            last_type = ty;
        }
        Ok(last_type)
    }

    /// Calculate max stack depth needed (conservative estimate).
    fn estimate_max_stack(&self) -> u16 {
        // Conservative: count through instructions
        // For simplicity, use a generous fixed estimate
        20
    }

    fn build_class(
        mut self,
        this_class: u16,
        object_class: u16,
        class_name: &str,
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
                attributes: vec![],
            }],
        };

        // Use Java 6 class version to avoid StackMapTable requirement.
        // See: M4-T2.1 ticket for upgrading to Java 21 with StackMapTable generation.
        let class_file = ClassFile {
            version: JAVA_6,
            access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
            constant_pool: self.cp,
            this_class,
            super_class: object_class,
            methods: vec![constructor, main_method],
            ..Default::default()
        };

        let _ = class_name;
        let mut buffer = Vec::new();
        class_file.to_bytes(&mut buffer)?;
        Ok(buffer)
    }
}

/// Compile a module's `main` function to JVM bytecode.
pub fn compile_module(module: &Module, class_name: &str) -> Result<Vec<u8>, CodegenError> {
    // Find the main function
    let main_fn = module
        .decls
        .iter()
        .find_map(|decl| match decl {
            Decl::DefFn(f) if f.name == "main" => Some(f),
            _ => None,
        })
        .ok_or(CodegenError::NoMainFunction)?;

    let (mut compiler, this_class, object_class) = Compiler::new(class_name)?;

    // Emit: getstatic System.out (push PrintStream ref)
    let system_out = compiler.system_out;
    compiler.emit(Instruction::Getstatic(system_out));

    // Compile the body expression
    let result_type = compiler.compile_expr(&main_fn.body)?;

    // Emit the appropriate println call
    let println_ref = match result_type {
        JvmType::Long => compiler.println_long,
        JvmType::Double => compiler.println_double,
        JvmType::Ref => compiler.println_string,
        JvmType::Int => compiler.println_bool,
    };
    compiler.emit(Instruction::Invokevirtual(println_ref));
    compiler.emit(Instruction::Return);

    compiler.build_class(this_class, object_class, class_name)
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
