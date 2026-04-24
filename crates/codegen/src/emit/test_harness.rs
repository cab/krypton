//! Synthesize the `Kr$TestHarness` class for `krypton test`.
//!
//! The harness is a single class with a `public static void main(String[])`
//! method that invokes every discovered `test_*` function, wraps each call in
//! a `try { ... } catch (RuntimeException)` block, prints one line per test,
//! tracks pass/fail counters, and exits 0 (all passed) or 1 (any failure).
//!
//! The harness is built directly against `ristretto_classfile` primitives —
//! it does not use the per-module `Compiler`/`BytecodeBuilder` because it has
//! no Krypton functions of its own. StackMapTable frames are constructed
//! manually for the catch handler and after-catch merge points.

use ristretto_classfile::attributes::{
    Attribute, ExceptionTableEntry, Instruction, StackFrame, VerificationType,
};
use ristretto_classfile::{ClassAccessFlags, ClassFile, ConstantPool, Method, MethodAccessFlags};

use super::compiler::CodegenError;
use super::JAVA_21;

/// One discovered `test_*` function, ordered by the caller in the sequence the
/// harness should invoke them. `class_name` is the JVM-internal name of the
/// class that owns the static method. `method_descriptor` is the full JVM
/// descriptor (e.g. `()Z` for `() -> Unit`, `()Lcore/never/Never;` for tests
/// that always panic) used to look the method up in the constant pool.
#[derive(Debug, Clone)]
pub struct TestHarnessEntry {
    pub class_name: String,
    pub method_name: String,
    pub method_descriptor: String,
    pub qualified_name: String,
}

/// JVM-internal name of the synthetic harness class.
pub const HARNESS_CLASS_NAME: &str = "Kr$TestHarness";

/// Build the `Kr$TestHarness` class file bytes.
pub fn generate_test_harness(entries: &[TestHarnessEntry]) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(HARNESS_CLASS_NAME)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;

    let code_utf8 = cp.add_utf8("Code")?;
    let smt_name = cp.add_utf8("StackMapTable")?;
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8("()V")?;
    let main_name = cp.add_utf8("main")?;
    let main_desc = cp.add_utf8("([Ljava/lang/String;)V")?;

    // Common refs used by the harness body.
    let runtime_class = cp.add_class("krypton/runtime/KryptonRuntime")?;
    let boot_ref = cp.add_method_ref(runtime_class, "boot", "()V")?;
    let await_ref = cp.add_method_ref(runtime_class, "awaitAllActors", "()V")?;

    let system_class = cp.add_class("java/lang/System")?;
    let printstream_class = cp.add_class("java/io/PrintStream")?;
    let system_out_field = cp.add_field_ref(system_class, "out", "Ljava/io/PrintStream;")?;
    let println_string =
        cp.add_method_ref(printstream_class, "println", "(Ljava/lang/String;)V")?;
    let print_string = cp.add_method_ref(printstream_class, "print", "(Ljava/lang/String;)V")?;
    let print_int = cp.add_method_ref(printstream_class, "print", "(I)V")?;

    let exit_ref = cp.add_method_ref(system_class, "exit", "(I)V")?;

    let runtime_exception_class = cp.add_class("java/lang/RuntimeException")?;
    let string_arr_class = cp.add_class("[Ljava/lang/String;")?;

    // Default constructor.
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

    // ----- main body -----
    let mut code: Vec<Instruction> = Vec::new();
    let mut exception_table: Vec<ExceptionTableEntry> = Vec::new();
    let mut frames: Vec<StackFrame> = Vec::new();

    // Locals layout for stack map frames: [String[], int passCount, int failCount].
    let stable_locals = vec![
        VerificationType::Object {
            cpool_index: string_arr_class,
        },
        VerificationType::Integer,
        VerificationType::Integer,
    ];

    // Boot the actor runtime.
    code.push(Instruction::Invokestatic(boot_ref));

    // passCount = 0; failCount = 0;
    code.push(Instruction::Iconst_0);
    code.push(Instruction::Istore_1);
    code.push(Instruction::Iconst_0);
    code.push(Instruction::Istore_2);

    let mut prev_frame_idx: Option<u16> = None;

    for entry in entries {
        let test_class_idx = cp.add_class(&entry.class_name)?;
        // Krypton's lowered `() -> Unit` returns the boolean unit sentinel, so
        // method descriptor is `()Z`.
        let test_method_ref = cp.add_method_ref(
            test_class_idx,
            entry.method_name.as_str(),
            entry.method_descriptor.as_str(),
        )?;

        let ok_msg_idx = cp.add_string(format!("ok {}", entry.qualified_name))?;
        let fail_msg_idx = cp.add_string(format!("FAIL {}", entry.qualified_name))?;

        // tryStart:
        let try_start = code.len() as u16;
        code.push(Instruction::Invokestatic(test_method_ref));
        code.push(Instruction::Pop); // drop the unit sentinel
        code.push(Instruction::Getstatic(system_out_field));
        push_ldc_string(&mut code, ok_msg_idx);
        code.push(Instruction::Invokevirtual(println_string));
        code.push(Instruction::Iinc(1, 1)); // passCount++
        let goto_after = code.len();
        code.push(Instruction::Goto(0)); // patched later
        let try_end = code.len() as u16;

        // handler:
        let handler_idx = code.len() as u16;
        // Frame at handler entry: stack = [RuntimeException], locals stable.
        frames.push(make_full_frame(
            &mut prev_frame_idx,
            handler_idx,
            stable_locals.clone(),
            vec![VerificationType::Object {
                cpool_index: runtime_exception_class,
            }],
        ));
        code.push(Instruction::Astore_3); // stash exception in slot 3
        code.push(Instruction::Getstatic(system_out_field));
        push_ldc_string(&mut code, fail_msg_idx);
        code.push(Instruction::Invokevirtual(println_string));
        code.push(Instruction::Iinc(2, 1)); // failCount++

        // afterCatch:
        let after_catch_idx = code.len() as u16;
        frames.push(make_full_frame(
            &mut prev_frame_idx,
            after_catch_idx,
            stable_locals.clone(),
            vec![],
        ));

        // Patch the Goto in the try body to jump here.
        if let Instruction::Goto(ref mut target) = code[goto_after] {
            *target = after_catch_idx;
        } else {
            unreachable!("ICE: placeholder must be Goto");
        }

        exception_table.push(ExceptionTableEntry {
            range_pc: try_start..try_end,
            handler_pc: handler_idx,
            catch_type: runtime_exception_class,
        });
    }

    // Print the summary line: "<pass> passed, <fail> failed".
    let passed_str_idx = cp.add_string(" passed, ")?;
    let failed_str_idx = cp.add_string(" failed")?;

    // print(passCount)
    code.push(Instruction::Getstatic(system_out_field));
    code.push(Instruction::Iload_1);
    code.push(Instruction::Invokevirtual(print_int));
    // print(" passed, ")
    code.push(Instruction::Getstatic(system_out_field));
    push_ldc_string(&mut code, passed_str_idx);
    code.push(Instruction::Invokevirtual(print_string));
    // print(failCount)
    code.push(Instruction::Getstatic(system_out_field));
    code.push(Instruction::Iload_2);
    code.push(Instruction::Invokevirtual(print_int));
    // println(" failed")
    code.push(Instruction::Getstatic(system_out_field));
    push_ldc_string(&mut code, failed_str_idx);
    code.push(Instruction::Invokevirtual(println_string));

    // Wait for any actors the tests spawned.
    code.push(Instruction::Invokestatic(await_ref));

    // Exit with code 1 if any failure, else 0.
    code.push(Instruction::Iload_2);
    let ifeq_placeholder = code.len();
    code.push(Instruction::Ifeq(0)); // patched to exit_zero_idx
    code.push(Instruction::Iconst_1);
    code.push(Instruction::Invokestatic(exit_ref));
    code.push(Instruction::Return);

    let exit_zero_idx = code.len() as u16;
    frames.push(make_full_frame(
        &mut prev_frame_idx,
        exit_zero_idx,
        stable_locals.clone(),
        vec![],
    ));
    code.push(Instruction::Iconst_0);
    code.push(Instruction::Invokestatic(exit_ref));
    code.push(Instruction::Return);

    if let Instruction::Ifeq(ref mut target) = code[ifeq_placeholder] {
        *target = exit_zero_idx;
    } else {
        unreachable!("ICE: placeholder must be Ifeq");
    }

    let max_stack: u16 = 3; // largest reach: Getstatic + Ldc/Iload + ... = 2-3 wide values
    let max_locals: u16 = 4; // slot 0 args, 1 pass, 2 fail, 3 exception

    let mut code_attributes = Vec::new();
    if !frames.is_empty() {
        code_attributes.push(Attribute::StackMapTable {
            name_index: smt_name,
            frames,
        });
    }

    let main_method = Method {
        access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
        name_index: main_name,
        descriptor_index: main_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack,
            max_locals,
            code,
            exception_table,
            attributes: code_attributes,
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

fn push_ldc_string(code: &mut Vec<Instruction>, idx: u16) {
    if idx <= 255 {
        code.push(Instruction::Ldc(idx as u8));
    } else {
        code.push(Instruction::Ldc_w(idx));
    }
}

/// Build a full StackMapTable frame at `instr_idx`, computing the
/// offset_delta from the previous frame index per JVMS §4.7.4.
fn make_full_frame(
    prev_frame_idx: &mut Option<u16>,
    instr_idx: u16,
    locals: Vec<VerificationType>,
    stack: Vec<VerificationType>,
) -> StackFrame {
    let offset_delta = match *prev_frame_idx {
        None => instr_idx,
        Some(prev) => instr_idx - prev - 1,
    };
    *prev_frame_idx = Some(instr_idx);
    StackFrame::FullFrame {
        frame_type: 255,
        offset_delta,
        locals,
        stack,
    }
}
