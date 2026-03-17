//! Bytecode emission infrastructure (instruction buffer, stack frame tracking, local allocation).

use std::collections::{BTreeMap, HashMap};

use ristretto_classfile::attributes::{Attribute, Instruction, StackFrame, VerificationType};

use super::compiler::JvmType;

/// Well-known constant pool indices, set once in `new()`, read-only after.
#[derive(Clone, Default)]
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
    pub(super) string_arr_class: u16,
    // Intrinsic support
    pub(super) runtime_exception_class: u16,
    pub(super) runtime_exception_init: u16,
}

/// StackMapTable / verification type tracking.
#[derive(Default)]
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

    pub(super) fn push_type(&mut self, vt: VerificationType) {
        self.stack_types.push(vt);
        self.update_max_depth();
    }

    pub(super) fn push_long_type(&mut self) {
        self.stack_types.push(VerificationType::Long);
        self.stack_types.push(VerificationType::Top);
        self.update_max_depth();
    }

    pub(super) fn push_double_type(&mut self) {
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

    pub(super) fn record_frame(&mut self, instr_idx: u16) {
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

/// Per-method bytecode emission state, extracted from Compiler.
pub(super) struct BytecodeBuilder {
    pub(super) refs: CpoolRefs,
    pub(super) code: Vec<Instruction>,
    pub(super) frame: FrameState,
    pub(super) locals: HashMap<String, (u16, JvmType)>,
    pub(super) next_local: u16,
    pub(super) max_locals_hwm: u16,
    pub(super) fn_params: Vec<(u16, JvmType)>,
    pub(super) fn_return_type: Option<JvmType>,
    pub(super) recur_target: u16,
    pub(super) recur_frame_locals: Vec<VerificationType>,
    pub(super) local_fn_info: HashMap<String, (Vec<JvmType>, JvmType)>,
    pub(super) nested_ifeq_patches: Vec<usize>,
}

impl BytecodeBuilder {
    pub(super) fn new(refs: CpoolRefs) -> Self {
        Self {
            refs,
            code: Vec::new(),
            frame: FrameState::default(),
            locals: HashMap::new(),
            next_local: 0,
            max_locals_hwm: 0,
            fn_params: Vec::new(),
            fn_return_type: None,
            recur_target: 1,
            recur_frame_locals: Vec::new(),
            local_fn_info: HashMap::new(),
            nested_ifeq_patches: Vec::new(),
        }
    }

    pub(super) fn emit(&mut self, instr: Instruction) {
        self.code.push(instr);
    }

    pub(super) fn push_jvm_type(&mut self, ty: JvmType) {
        self.frame.push_jvm_type(ty, self.refs.string_class);
    }

    pub(super) fn pop_jvm_type(&mut self, ty: JvmType) {
        self.frame.pop_jvm_type(ty);
    }

    pub(super) fn jvm_type_to_vtypes(&self, ty: JvmType) -> Vec<VerificationType> {
        self.frame.jvm_type_to_vtypes(ty, self.refs.string_class)
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
    pub(super) fn unbox_if_needed(&mut self, target: JvmType) {
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

    /// Emit a typed load instruction and push the type onto the stack.
    pub(super) fn emit_load(&mut self, slot: u16, ty: JvmType) {
        let instr = match ty {
            JvmType::Long => Instruction::Lload(slot as u8),
            JvmType::Double => Instruction::Dload(slot as u8),
            JvmType::Int => Instruction::Iload(slot as u8),
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(slot as u8),
        };
        self.emit(instr);
        self.push_jvm_type(ty);
    }

    /// Emit a typed store instruction and pop the type from the stack.
    pub(super) fn emit_store(&mut self, slot: u16, ty: JvmType) {
        let instr = match ty {
            JvmType::Long => Instruction::Lstore(slot as u8),
            JvmType::Double => Instruction::Dstore(slot as u8),
            JvmType::Int => Instruction::Istore(slot as u8),
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Astore(slot as u8),
        };
        self.emit(instr);
        self.pop_jvm_type(ty);
    }

    /// Allocate a named local variable, returning its slot index.
    /// Updates locals map, next_local, and frame local_types.
    pub(super) fn alloc_local(&mut self, name: String, ty: JvmType) -> u16 {
        let slot = self.next_local;
        let slot_size: u16 = match ty {
            JvmType::Long | JvmType::Double => 2,
            _ => 1,
        };
        self.next_local += slot_size;
        self.locals.insert(name, (slot, ty));
        let vtypes = self.jvm_type_to_vtypes(ty);
        self.frame.local_types.extend(vtypes);
        slot
    }

    /// Allocate an anonymous local variable (no name in locals map), returning its slot.
    pub(super) fn alloc_anonymous_local(&mut self, ty: JvmType) -> u16 {
        let slot = self.next_local;
        let slot_size: u16 = match ty {
            JvmType::Long | JvmType::Double => 2,
            _ => 1,
        };
        self.next_local += slot_size;
        let vtypes = self.jvm_type_to_vtypes(ty);
        self.frame.local_types.extend(vtypes);
        slot
    }

    /// Emit New + Dup for a class, pushing two UninitializedThis entries.
    pub(super) fn emit_new_dup(&mut self, class_index: u16) {
        self.emit(Instruction::New(class_index));
        self.frame.push_type(VerificationType::UninitializedThis);
        self.emit(Instruction::Dup);
        self.frame.push_type(VerificationType::UninitializedThis);
    }

    /// Emit a placeholder instruction (e.g. Goto(0) or Ifeq(0)), returning its index for later patching.
    pub(super) fn emit_placeholder(&mut self, instr: Instruction) -> usize {
        let idx = self.code.len();
        self.emit(instr);
        idx
    }

    /// Patch a previously emitted placeholder instruction at the given index.
    pub(super) fn patch(&mut self, idx: usize, instr: Instruction) {
        self.code[idx] = instr;
    }

    /// Return the current bytecode offset.
    pub(super) fn current_offset(&self) -> u16 {
        self.code.len() as u16
    }

    /// Record a StackMapTable frame at the current bytecode offset.
    pub(super) fn record_frame(&mut self) {
        self.frame.record_frame(self.code.len() as u16);
    }

    /// Record a StackMapTable frame at a specific offset.
    pub(super) fn record_frame_at(&mut self, offset: u16) {
        self.frame.record_frame(offset);
    }

    /// Build StackMapTable code attributes for the current method.
    pub(super) fn build_code_attributes(&self) -> Vec<Attribute> {
        let stack_map_frames = self.frame.build_stack_map_frames();
        if stack_map_frames.is_empty() {
            vec![]
        } else {
            vec![Attribute::StackMapTable {
                name_index: self.refs.smt_name,
                frames: stack_map_frames,
            }]
        }
    }

    /// Build a complete Code attribute, consuming the instruction buffer.
    pub(super) fn finish_method(&mut self) -> Attribute {
        let code_attributes = self.build_code_attributes();
        Attribute::Code {
            name_index: self.refs.code_utf8,
            max_stack: self.frame.max_stack(),
            max_locals: self.max_locals_hwm.max(self.next_local),
            code: std::mem::take(&mut self.code),
            exception_table: vec![],
            attributes: code_attributes,
        }
    }

    /// Reset per-method compilation state.
    pub(super) fn reset(&mut self) {
        self.code.clear();
        self.locals.clear();
        self.next_local = 0;
        self.max_locals_hwm = 0;
        self.frame.reset();
        self.fn_params.clear();
        self.fn_return_type = None;
        self.recur_target = 1;
        self.recur_frame_locals.clear();
        self.local_fn_info.clear();
    }
}
