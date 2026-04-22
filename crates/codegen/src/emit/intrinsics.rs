use std::collections::HashMap;

use krypton_ir::Type;
use ristretto_classfile::attributes::{Instruction, StackFrame, VerificationType};
use ristretto_classfile::ConstantPool;

use super::compiler::CodegenError;

/// JVM primitive type category for an intrinsic operation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PrimitiveJvm {
    Long,
    Double,
    Int,
    Ref,
}

/// Describes the operation performed by an intrinsic.
#[derive(Debug, Clone)]
pub enum IntrinsicOp {
    /// Binary arithmetic: operands and result are same JVM type (e.g. Ladd, Dsub)
    BinaryArith(Instruction),
    /// String.concat
    StringConcat,
    /// Unary arithmetic (e.g. Lneg, Dneg)
    UnaryArith(Instruction),
    /// Numeric equality: Lcmp/Dcmpl + branch → boolean
    NumericEq,
    /// String equality: String.equals → boolean
    StringEq,
    /// Bool equality: Isub-based comparison → boolean
    BoolEq,
    /// Numeric ordering (lt): Lcmp/Dcmpl + Ifge branch → boolean
    NumericOrd,
    /// Show via static method (e.g. String.valueOf(long))
    ShowVia {
        box_class: &'static str,
        unbox_method: &'static str,
        unbox_desc: &'static str,
        valueof_desc: &'static str,
    },
    /// Show identity (String → String)
    ShowIdentity,
    /// Hash via BoxClass.hashCode(primitive) → int → long
    HashVia {
        box_class: &'static str,
        unbox_method: &'static str,
        unbox_desc: &'static str,
        hash_desc: &'static str,
    },
    /// Hash for String: String.hashCode() → int → long
    HashString,
}

/// A single intrinsic entry: maps (trait, type) to an operation.
#[derive(Debug)]
pub struct IntrinsicEntry {
    pub trait_name: &'static str,
    pub type_name: &'static str,
    pub method_name: &'static str,
    pub jvm_type: PrimitiveJvm,
    /// IR-level type for the target (matches `type_name`). Carried alongside
    /// the name so codegen doesn't re-derive it from a hardcoded name→type
    /// map — the registry is the single source of truth for intrinsic types.
    pub ir_type: Type,
    pub op: IntrinsicOp,
}

impl IntrinsicEntry {
    pub fn is_unary(&self) -> bool {
        matches!(
            self.op,
            IntrinsicOp::UnaryArith(_) | IntrinsicOp::HashVia { .. } | IntrinsicOp::HashString
        )
    }

    pub fn is_show(&self) -> bool {
        matches!(
            self.op,
            IntrinsicOp::ShowVia { .. } | IntrinsicOp::ShowIdentity
        )
    }
}

/// Registry of all intrinsic (trait, type) → operation mappings.
pub struct IntrinsicRegistry {
    entries: Vec<IntrinsicEntry>,
    index: HashMap<(&'static str, &'static str), usize>,
}

impl IntrinsicRegistry {
    pub fn new() -> Self {
        let entries = vec![
            // Semigroup Int
            IntrinsicEntry {
                trait_name: "Semigroup",
                type_name: "Int",
                method_name: "combine",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::BinaryArith(Instruction::Ladd),
            },
            // Sub Int
            IntrinsicEntry {
                trait_name: "Sub",
                type_name: "Int",
                method_name: "sub",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::BinaryArith(Instruction::Lsub),
            },
            // Mul Int
            IntrinsicEntry {
                trait_name: "Mul",
                type_name: "Int",
                method_name: "mul",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::BinaryArith(Instruction::Lmul),
            },
            // Div Int
            IntrinsicEntry {
                trait_name: "Div",
                type_name: "Int",
                method_name: "div",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::BinaryArith(Instruction::Ldiv),
            },
            // Neg Int
            IntrinsicEntry {
                trait_name: "Neg",
                type_name: "Int",
                method_name: "neg",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::UnaryArith(Instruction::Lneg),
            },
            // Eq Int
            IntrinsicEntry {
                trait_name: "Eq",
                type_name: "Int",
                method_name: "eq",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::NumericEq,
            },
            // Ord Int
            IntrinsicEntry {
                trait_name: "Ord",
                type_name: "Int",
                method_name: "lt",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::NumericOrd,
            },
            // Semigroup Float
            IntrinsicEntry {
                trait_name: "Semigroup",
                type_name: "Float",
                method_name: "combine",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::BinaryArith(Instruction::Dadd),
            },
            // Sub Float
            IntrinsicEntry {
                trait_name: "Sub",
                type_name: "Float",
                method_name: "sub",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::BinaryArith(Instruction::Dsub),
            },
            // Mul Float
            IntrinsicEntry {
                trait_name: "Mul",
                type_name: "Float",
                method_name: "mul",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::BinaryArith(Instruction::Dmul),
            },
            // Div Float
            IntrinsicEntry {
                trait_name: "Div",
                type_name: "Float",
                method_name: "div",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::BinaryArith(Instruction::Ddiv),
            },
            // Neg Float
            IntrinsicEntry {
                trait_name: "Neg",
                type_name: "Float",
                method_name: "neg",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::UnaryArith(Instruction::Dneg),
            },
            // Eq Float
            IntrinsicEntry {
                trait_name: "Eq",
                type_name: "Float",
                method_name: "eq",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::NumericEq,
            },
            // Ord Float
            IntrinsicEntry {
                trait_name: "Ord",
                type_name: "Float",
                method_name: "lt",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::NumericOrd,
            },
            // Semigroup String
            IntrinsicEntry {
                trait_name: "Semigroup",
                type_name: "String",
                method_name: "combine",
                jvm_type: PrimitiveJvm::Ref,
                ir_type: Type::String,
                op: IntrinsicOp::StringConcat,
            },
            // Eq String
            IntrinsicEntry {
                trait_name: "Eq",
                type_name: "String",
                method_name: "eq",
                jvm_type: PrimitiveJvm::Ref,
                ir_type: Type::String,
                op: IntrinsicOp::StringEq,
            },
            // Eq Bool
            IntrinsicEntry {
                trait_name: "Eq",
                type_name: "Bool",
                method_name: "eq",
                jvm_type: PrimitiveJvm::Int,
                ir_type: Type::Bool,
                op: IntrinsicOp::BoolEq,
            },
            // Show Int
            IntrinsicEntry {
                trait_name: "Show",
                type_name: "Int",
                method_name: "show",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::ShowVia {
                    box_class: "java/lang/Long",
                    unbox_method: "longValue",
                    unbox_desc: "()J",
                    valueof_desc: "(J)Ljava/lang/String;",
                },
            },
            // Show Float
            IntrinsicEntry {
                trait_name: "Show",
                type_name: "Float",
                method_name: "show",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::ShowVia {
                    box_class: "java/lang/Double",
                    unbox_method: "doubleValue",
                    unbox_desc: "()D",
                    valueof_desc: "(D)Ljava/lang/String;",
                },
            },
            // Show Bool
            IntrinsicEntry {
                trait_name: "Show",
                type_name: "Bool",
                method_name: "show",
                jvm_type: PrimitiveJvm::Int,
                ir_type: Type::Bool,
                op: IntrinsicOp::ShowVia {
                    box_class: "java/lang/Boolean",
                    unbox_method: "booleanValue",
                    unbox_desc: "()Z",
                    valueof_desc: "(Z)Ljava/lang/String;",
                },
            },
            // Show String
            IntrinsicEntry {
                trait_name: "Show",
                type_name: "String",
                method_name: "show",
                jvm_type: PrimitiveJvm::Ref,
                ir_type: Type::String,
                op: IntrinsicOp::ShowIdentity,
            },
            // Hash Int
            IntrinsicEntry {
                trait_name: "Hash",
                type_name: "Int",
                method_name: "hash",
                jvm_type: PrimitiveJvm::Long,
                ir_type: Type::Int,
                op: IntrinsicOp::HashVia {
                    box_class: "java/lang/Long",
                    unbox_method: "longValue",
                    unbox_desc: "()J",
                    hash_desc: "(J)I",
                },
            },
            // Hash Float
            IntrinsicEntry {
                trait_name: "Hash",
                type_name: "Float",
                method_name: "hash",
                jvm_type: PrimitiveJvm::Double,
                ir_type: Type::Float,
                op: IntrinsicOp::HashVia {
                    box_class: "java/lang/Double",
                    unbox_method: "doubleValue",
                    unbox_desc: "()D",
                    hash_desc: "(D)I",
                },
            },
            // Hash Bool
            IntrinsicEntry {
                trait_name: "Hash",
                type_name: "Bool",
                method_name: "hash",
                jvm_type: PrimitiveJvm::Int,
                ir_type: Type::Bool,
                op: IntrinsicOp::HashVia {
                    box_class: "java/lang/Boolean",
                    unbox_method: "booleanValue",
                    unbox_desc: "()Z",
                    hash_desc: "(Z)I",
                },
            },
            // Hash String
            IntrinsicEntry {
                trait_name: "Hash",
                type_name: "String",
                method_name: "hash",
                jvm_type: PrimitiveJvm::Ref,
                ir_type: Type::String,
                op: IntrinsicOp::HashString,
            },
        ];

        let mut index = HashMap::new();
        for (i, entry) in entries.iter().enumerate() {
            index.insert((entry.trait_name, entry.type_name), i);
        }

        IntrinsicRegistry { entries, index }
    }

    /// Look up an intrinsic by (trait_name, type_name).
    #[allow(dead_code)]
    pub fn get(&self, trait_name: &str, type_name: &str) -> Option<&IntrinsicEntry> {
        self.index
            .get(&(trait_name, type_name))
            .map(|&i| &self.entries[i])
    }

    /// Iterate over all entries.
    pub fn iter(&self) -> impl Iterator<Item = &IntrinsicEntry> {
        self.entries.iter()
    }
}

// --- Bridge bytecode generation helpers ---

fn object_vtype(cpool_index: u16) -> VerificationType {
    VerificationType::Object { cpool_index }
}

fn bridge_locals(this_class: u16, is_unary: bool, object_class: u16) -> Vec<VerificationType> {
    let mut locals = vec![object_vtype(this_class), object_vtype(object_class)];
    if !is_unary {
        locals.push(object_vtype(object_class));
    }
    locals
}

fn branch_bridge_frames(
    branch_target: u16,
    join_target: u16,
    locals: &[VerificationType],
) -> Vec<StackFrame> {
    vec![
        StackFrame::FullFrame {
            frame_type: 255,
            offset_delta: branch_target,
            locals: locals.to_vec(),
            stack: vec![],
        },
        StackFrame::FullFrame {
            frame_type: 255,
            offset_delta: join_target - branch_target - 1,
            locals: locals.to_vec(),
            stack: vec![VerificationType::Integer],
        },
    ]
}

/// Unbox helpers for bridge: returns (box_class_idx, unbox_method_ref)
fn add_unbox_refs(
    cp: &mut ConstantPool,
    jvm_type: PrimitiveJvm,
) -> Result<(u16, u16), CodegenError> {
    match jvm_type {
        PrimitiveJvm::Long => {
            let cls = cp.add_class("java/lang/Long")?;
            let unbox = cp.add_method_ref(cls, "longValue", "()J")?;
            Ok((cls, unbox))
        }
        PrimitiveJvm::Double => {
            let cls = cp.add_class("java/lang/Double")?;
            let unbox = cp.add_method_ref(cls, "doubleValue", "()D")?;
            Ok((cls, unbox))
        }
        PrimitiveJvm::Int => {
            let cls = cp.add_class("java/lang/Boolean")?;
            let unbox = cp.add_method_ref(cls, "booleanValue", "()Z")?;
            Ok((cls, unbox))
        }
        PrimitiveJvm::Ref => {
            let cls = cp.add_class("java/lang/String")?;
            Ok((cls, 0)) // no unbox needed for String
        }
    }
}

fn add_box_ref(cp: &mut ConstantPool, jvm_type: PrimitiveJvm) -> Result<u16, CodegenError> {
    match jvm_type {
        PrimitiveJvm::Long => {
            let cls = cp.add_class("java/lang/Long")?;
            Ok(cp.add_method_ref(cls, "valueOf", "(J)Ljava/lang/Long;")?)
        }
        PrimitiveJvm::Double => {
            let cls = cp.add_class("java/lang/Double")?;
            Ok(cp.add_method_ref(cls, "valueOf", "(D)Ljava/lang/Double;")?)
        }
        PrimitiveJvm::Int => {
            let cls = cp.add_class("java/lang/Boolean")?;
            Ok(cp.add_method_ref(cls, "valueOf", "(Z)Ljava/lang/Boolean;")?)
        }
        PrimitiveJvm::Ref => Ok(0), // not used
    }
}

/// Emit unbox instruction sequence: checkcast + invokevirtual
fn emit_unbox(code: &mut Vec<Instruction>, box_class: u16, unbox_ref: u16, jvm_type: PrimitiveJvm) {
    if jvm_type == PrimitiveJvm::Ref {
        code.push(Instruction::Checkcast(box_class));
    } else {
        code.push(Instruction::Checkcast(box_class));
        code.push(Instruction::Invokevirtual(unbox_ref));
    }
}

/// Build the bridge method bytecode for a built-in trait instance, driven by the registry.
pub fn build_bridge_bytecode(
    cp: &mut ConstantPool,
    this_class: u16,
    object_class: u16,
    entry: &IntrinsicEntry,
) -> Result<(Vec<Instruction>, u16, u16, Vec<StackFrame>), CodegenError> {
    let is_unary = entry.is_unary();
    let locals = bridge_locals(this_class, is_unary, object_class);
    let mut code = Vec::new();

    match &entry.op {
        IntrinsicOp::BinaryArith(instr) => {
            let (box_class, unbox_ref) = add_unbox_refs(cp, entry.jvm_type)?;
            let box_ref = add_box_ref(cp, entry.jvm_type)?;
            // Unbox first arg
            code.push(Instruction::Aload(1));
            emit_unbox(&mut code, box_class, unbox_ref, entry.jvm_type);
            // Unbox second arg
            code.push(Instruction::Aload(2));
            emit_unbox(&mut code, box_class, unbox_ref, entry.jvm_type);
            // Operation
            code.push(instr.clone());
            // Box result
            code.push(Instruction::Invokestatic(box_ref));
            code.push(Instruction::Areturn);
            Ok((code, 4, 3, vec![]))
        }

        IntrinsicOp::StringConcat => {
            let string_class = cp.add_class("java/lang/String")?;
            let string_concat = cp.add_method_ref(
                string_class,
                "concat",
                "(Ljava/lang/String;)Ljava/lang/String;",
            )?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Invokevirtual(string_concat));
            code.push(Instruction::Areturn);
            Ok((code, 2, 3, vec![]))
        }

        IntrinsicOp::UnaryArith(instr) => {
            let (box_class, unbox_ref) = add_unbox_refs(cp, entry.jvm_type)?;
            let box_ref = add_box_ref(cp, entry.jvm_type)?;
            code.push(Instruction::Aload(1));
            emit_unbox(&mut code, box_class, unbox_ref, entry.jvm_type);
            code.push(instr.clone());
            code.push(Instruction::Invokestatic(box_ref));
            code.push(Instruction::Areturn);
            Ok((code, 2, 2, vec![]))
        }

        IntrinsicOp::NumericEq => {
            let (box_class, unbox_ref) = add_unbox_refs(cp, entry.jvm_type)?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            let cmp_instr = match entry.jvm_type {
                PrimitiveJvm::Long => Instruction::Lcmp,
                PrimitiveJvm::Double => Instruction::Dcmpl,
                _ => unreachable!(),
            };
            code.push(Instruction::Aload(1));
            emit_unbox(&mut code, box_class, unbox_ref, entry.jvm_type);
            code.push(Instruction::Aload(2));
            emit_unbox(&mut code, box_class, unbox_ref, entry.jvm_type);
            code.push(cmp_instr);
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifne(branch_idx + 3));
            code.push(Instruction::Iconst_1);
            code.push(Instruction::Goto(branch_idx + 4));
            code.push(Instruction::Iconst_0);
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((
                code,
                4,
                3,
                branch_bridge_frames(branch_idx + 3, branch_idx + 4, &locals),
            ))
        }

        IntrinsicOp::StringEq => {
            let string_class = cp.add_class("java/lang/String")?;
            let string_equals =
                cp.add_method_ref(string_class, "equals", "(Ljava/lang/Object;)Z")?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Invokevirtual(string_equals));
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((code, 2, 3, vec![]))
        }

        IntrinsicOp::BoolEq => {
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_unbox = cp.add_method_ref(bool_class, "booleanValue", "()Z")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(bool_class));
            code.push(Instruction::Invokevirtual(bool_unbox));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(bool_class));
            code.push(Instruction::Invokevirtual(bool_unbox));
            code.push(Instruction::Isub);
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifeq(branch_idx + 3));
            code.push(Instruction::Iconst_0);
            code.push(Instruction::Goto(branch_idx + 4));
            code.push(Instruction::Iconst_1);
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((
                code,
                2,
                3,
                branch_bridge_frames(branch_idx + 3, branch_idx + 4, &locals),
            ))
        }

        IntrinsicOp::NumericOrd => {
            let (box_class, unbox_ref) = add_unbox_refs(cp, entry.jvm_type)?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            let cmp_instr = match entry.jvm_type {
                PrimitiveJvm::Long => Instruction::Lcmp,
                PrimitiveJvm::Double => Instruction::Dcmpl,
                _ => unreachable!(),
            };
            code.push(Instruction::Aload(1));
            emit_unbox(&mut code, box_class, unbox_ref, entry.jvm_type);
            code.push(Instruction::Aload(2));
            emit_unbox(&mut code, box_class, unbox_ref, entry.jvm_type);
            code.push(cmp_instr);
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifge(branch_idx + 3));
            code.push(Instruction::Iconst_1);
            code.push(Instruction::Goto(branch_idx + 4));
            code.push(Instruction::Iconst_0);
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((
                code,
                4,
                3,
                branch_bridge_frames(branch_idx + 3, branch_idx + 4, &locals),
            ))
        }

        IntrinsicOp::ShowVia {
            box_class,
            unbox_method,
            unbox_desc,
            valueof_desc,
        } => {
            let box_cls = cp.add_class(box_class)?;
            let unbox_ref = cp.add_method_ref(box_cls, unbox_method, unbox_desc)?;
            let string_class = cp.add_class("java/lang/String")?;
            let string_valueof = cp.add_method_ref(string_class, "valueOf", valueof_desc)?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(box_cls));
            code.push(Instruction::Invokevirtual(unbox_ref));
            code.push(Instruction::Invokestatic(string_valueof));
            code.push(Instruction::Areturn);
            Ok((code, 4, 2, vec![]))
        }

        IntrinsicOp::ShowIdentity => {
            let string_class = cp.add_class("java/lang/String")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Areturn);
            Ok((code, 4, 2, vec![]))
        }

        IntrinsicOp::HashVia {
            box_class,
            unbox_method,
            unbox_desc,
            hash_desc,
        } => {
            let box_cls = cp.add_class(box_class)?;
            let unbox_ref = cp.add_method_ref(box_cls, unbox_method, unbox_desc)?;
            let hash_ref = cp.add_method_ref(box_cls, "hashCode", hash_desc)?;
            let long_class = cp.add_class("java/lang/Long")?;
            let long_valueof = cp.add_method_ref(long_class, "valueOf", "(J)Ljava/lang/Long;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(box_cls));
            code.push(Instruction::Invokevirtual(unbox_ref));
            code.push(Instruction::Invokestatic(hash_ref));
            code.push(Instruction::I2l);
            code.push(Instruction::Invokestatic(long_valueof));
            code.push(Instruction::Areturn);
            Ok((code, 2, 2, vec![]))
        }

        IntrinsicOp::HashString => {
            let string_class = cp.add_class("java/lang/String")?;
            let hash_ref = cp.add_method_ref(string_class, "hashCode", "()I")?;
            let long_class = cp.add_class("java/lang/Long")?;
            let long_valueof = cp.add_method_ref(long_class, "valueOf", "(J)Ljava/lang/Long;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Invokevirtual(hash_ref));
            code.push(Instruction::I2l);
            code.push(Instruction::Invokestatic(long_valueof));
            code.push(Instruction::Areturn);
            Ok((code, 2, 2, vec![]))
        }
    }
}
