//! Pattern matching compilation (match expressions and let-destructuring).

use krypton_typechecker::typed_ast::{TypedExpr, TypedMatchArm, TypedPattern};
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{Instruction, VerificationType};

use super::compiler::{Compiler, CodegenError, JvmType};

/// Controls whether `compile_pattern` emits instanceof/ifeq guards.
pub(super) enum PatternMode {
    /// Emit instanceof/ifeq guards AND bind variables. Returns ifeq patch index.
    CheckAndBind,
    /// Bind variables only (no guards). For last arm / irrefutable patterns.
    BindOnly,
}

impl Compiler {
    pub(super) fn compile_let_pattern(
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
        let scrutinee_slot = self.builder.alloc_anonymous_local(val_type);
        self.builder.emit_store(scrutinee_slot, val_type);

        // Bind the pattern
        self.bind_irrefutable_pattern(pattern, scrutinee_slot, val_type, &value.ty)?;

        // Compile the body if present
        if let Some(body) = body {
            self.compile_expr(body, in_tail)
        } else {
            self.builder.emit(Instruction::Iconst_0);
            self.builder.frame.push_type(VerificationType::Integer);
            Ok(JvmType::Int)
        }
    }

    /// Bind an irrefutable pattern (Tuple, Var, Wildcard) — used by let-pattern destructuring.
    pub(super) fn bind_irrefutable_pattern(
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
                self.builder.emit_load(scrutinee_slot, scrutinee_type);

                let var_slot = self.builder.alloc_local(name.clone(), scrutinee_type);
                self.builder.emit_store(var_slot, scrutinee_type);
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
                    self.builder.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: tuple_class,
                    });
                    self.builder.emit(Instruction::Invokevirtual(field_ref));
                    self.builder.frame.pop_type(); // pop tuple ref
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: self.builder.refs.object_class,
                    });

                    // Unbox if primitive, checkcast if struct/string ref
                    match elem_jvm_type {
                        JvmType::StructRef(idx) => {
                            self.builder.emit(Instruction::Checkcast(idx));
                            self.builder.frame.pop_type();
                            self.builder.frame
                                .push_type(VerificationType::Object { cpool_index: idx });
                        }
                        JvmType::Ref => {
                            self.builder.emit(Instruction::Checkcast(self.builder.refs.string_class));
                            self.builder.frame.pop_type();
                            self.builder.frame.push_type(VerificationType::Object {
                                cpool_index: self.builder.refs.string_class,
                            });
                        }
                        _ => self.builder.unbox_if_needed(elem_jvm_type),
                    }

                    // For nested tuple or var, store and recurse
                    match sub_pat {
                        TypedPattern::Var { name: var_name, .. } => {
                            let var_slot = self.builder.alloc_local(var_name.clone(), elem_jvm_type);
                self.builder.emit_store(var_slot, elem_jvm_type);
                        }
                        TypedPattern::Tuple { .. } => {
                            // Store in temp local and recurse
                            let nested_slot = self.builder.next_local;
                            self.builder.next_local += 1;
                            self.builder.emit(Instruction::Astore(nested_slot as u8));
                            self.builder.frame.pop_type();
                            self.builder.frame.local_types.push(VerificationType::Object {
                                cpool_index: match elem_jvm_type {
                                    JvmType::StructRef(idx) => idx,
                                    _ => self.builder.refs.object_class,
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
                            self.builder.frame.pop_type();
                            self.builder.emit(Instruction::Pop);
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

    pub(super) fn compile_match(
        &mut self,
        scrutinee: &TypedExpr,
        arms: &[TypedMatchArm],
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // 1. Compile scrutinee and store in temp local
        let scrutinee_type = self.compile_expr(scrutinee, false)?;
        let scrutinee_slot = self.builder.alloc_anonymous_local(scrutinee_type);
        self.builder.emit_store(scrutinee_slot, scrutinee_type);

        let stack_at_match = self.builder.frame.stack_types.clone();
        let locals_at_match = self.builder.locals.clone();
        let local_types_at_match = self.builder.frame.local_types.clone();
        let next_local_at_match = self.builder.next_local;

        let mut goto_patches: Vec<usize> = Vec::new();
        let mut result_type = None;
        let mut max_next_local = next_local_at_match;

        for (i, arm) in arms.iter().enumerate() {
            let is_last = i == arms.len() - 1;

            // Track high-water mark for locals
            if self.builder.next_local > max_next_local {
                max_next_local = self.builder.next_local;
            }

            // Restore state for each arm
            self.builder.frame.stack_types = stack_at_match.clone();
            self.builder.locals = locals_at_match.clone();
            self.builder.frame.local_types = local_types_at_match.clone();
            self.builder.next_local = next_local_at_match;

            // Record frame at this arm's start (branch target) — except first arm
            if i > 0 {
                let arm_start = self.builder.current_offset();
                self.builder.frame.record_frame(arm_start);
            }

            // Compile pattern: CheckAndBind emits guards, BindOnly (last arm) skips them
            self.builder.nested_ifeq_patches.clear();
            let mode = if !is_last {
                PatternMode::CheckAndBind
            } else {
                PatternMode::BindOnly
            };
            let next_arm_patch = self.compile_pattern(
                &arm.pattern,
                scrutinee_slot,
                scrutinee_type,
                &scrutinee.ty,
                mode,
            )?;
            let nested_patches = std::mem::take(&mut self.builder.nested_ifeq_patches);

            // Compile arm body
            let arm_type = self.compile_expr(&arm.body, in_tail)?;

            // Normalize arm result type to match function return type
            let target_type = self.builder.fn_return_type.unwrap_or(arm_type);
            if result_type.is_none() {
                result_type = Some(target_type);
            }
            // Box primitive to Object if needed
            if matches!(target_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
                && !matches!(arm_type, JvmType::StructRef(_) | JvmType::Ref)
            {
                self.builder.box_if_needed(arm_type);
                // Fix stack type to match target (Object)
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.object_class,
                });
            }
            // Unbox Object to primitive if needed
            else if !matches!(target_type, JvmType::StructRef(_) | JvmType::Ref)
                && matches!(arm_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
            {
                self.builder.unbox_if_needed(target_type);
            }
            // Checkcast Object to specific ref type if needed
            else if matches!(target_type, JvmType::Ref | JvmType::StructRef(_))
                && !matches!(target_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
                && matches!(arm_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
            {
                let cast_class = match target_type {
                    JvmType::Ref => self.builder.refs.string_class,
                    JvmType::StructRef(idx) => idx,
                    _ => unreachable!(),
                };
                self.builder.emit(Instruction::Checkcast(cast_class));
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: cast_class,
                });
            }

            // Goto after_match (except last arm)
            if !is_last {
                let goto_idx = self.builder.emit_placeholder(Instruction::Goto(0)); // placeholder
                goto_patches.push(goto_idx);
            }

            // Patch the next_arm branch target (and any nested ifeq patches)
            if let Some(patch_idx) = next_arm_patch {
                let next_arm_target = self.builder.current_offset();
                self.builder.patch(patch_idx, Instruction::Ifeq(next_arm_target));
                for nested_idx in &nested_patches {
                    self.builder.code[*nested_idx] = Instruction::Ifeq(next_arm_target);
                }
            }
        }

        // Track final arm's locals too
        if self.builder.next_local > max_next_local {
            max_next_local = self.builder.next_local;
        }

        // after_match: record frame with pre-match locals and the match result on stack
        // (arm-local bindings are out of scope and different arms may have different types)
        let after_match = self.builder.current_offset();
        self.builder.frame.local_types = local_types_at_match.clone();
        self.builder.frame.stack_types = stack_at_match.clone();
        if let Some(rt) = result_type {
            self.builder.push_jvm_type(rt);
        }
        self.builder.frame.record_frame(after_match);

        // Patch all goto instructions
        for goto_idx in goto_patches {
            self.builder.patch(goto_idx, Instruction::Goto(after_match));
        }

        // Restore locals scope but keep high-water mark for max_locals
        self.builder.locals = locals_at_match;
        self.builder.next_local = max_next_local;

        Ok(result_type.unwrap_or(JvmType::Int))
    }

    /// Compile a pattern: optionally emit guards, extract fields, and bind variables.
    pub(super) fn compile_pattern(
        &mut self,
        pattern: &TypedPattern,
        scrutinee_slot: u16,
        scrutinee_type: JvmType,
        scrutinee_tc_type: &Type,
        mode: PatternMode,
    ) -> Result<Option<usize>, CodegenError> {
        match pattern {
            TypedPattern::Wildcard { .. } => Ok(None),
            TypedPattern::Var { name, .. } => {
                self.builder.emit(Instruction::Aload(scrutinee_slot as u8));
                self.builder.push_jvm_type(scrutinee_type);
                let var_slot = self.builder.alloc_anonymous_local(scrutinee_type);
                self.builder.emit_store(var_slot, scrutinee_type);
                self.builder.locals.insert(name.clone(), (var_slot, scrutinee_type));
                Ok(None)
            }
            TypedPattern::Constructor { name, args, .. } => {
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

                // instanceof + ifeq guard (CheckAndBind only)
                let ifeq_idx = if matches!(mode, PatternMode::CheckAndBind) {
                    self.builder.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.builder.push_jvm_type(scrutinee_type);
                    self.builder.emit(Instruction::Instanceof(variant_class_index));
                    self.builder.pop_jvm_type(scrutinee_type);
                    self.builder.frame.push_type(VerificationType::Integer);

                    let idx = self.builder.emit_placeholder(Instruction::Ifeq(0));
                    self.builder.frame.pop_type();
                    Some(idx)
                } else {
                    None
                };

                // Extract fields if there are sub-patterns
                if !args.is_empty() {
                    self.builder.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.builder.push_jvm_type(scrutinee_type);
                    self.builder.emit(Instruction::Checkcast(variant_class_index));
                    self.builder.pop_jvm_type(scrutinee_type);
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    let cast_slot = self.builder.next_local;
                    self.builder.next_local += 1;
                    self.builder.emit(Instruction::Astore(cast_slot as u8));
                    self.builder.frame.pop_type();
                    self.builder.frame.local_types.push(VerificationType::Object {
                        cpool_index: variant_class_index,
                    });

                    for (j, sub_pat) in args.iter().enumerate() {
                        if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                            continue;
                        }
                        let (_fname, field_jvm_type, is_erased) = &fields[j];
                        let field_ref = field_refs[j];

                        self.builder.emit(Instruction::Aload(cast_slot as u8));
                        self.builder.frame.push_type(VerificationType::Object {
                            cpool_index: variant_class_index,
                        });
                        self.builder.emit(Instruction::Getfield(field_ref));
                        self.builder.frame.pop_type();
                        if *is_erased {
                            self.builder.frame.push_type(VerificationType::Object {
                                cpool_index: self.builder.refs.string_class,
                            });
                        } else {
                            self.builder.push_jvm_type(*field_jvm_type);
                        }

                        match sub_pat {
                            TypedPattern::Var {
                                name: var_name,
                                ty: var_tc_type,
                                ..
                            } => {
                                // For erased fields, resolve actual type from the pattern
                                // variable's typechecker type and emit cast/unbox.
                                let actual_type = if *is_erased {
                                    self.type_to_jvm(var_tc_type)
                                        .unwrap_or(JvmType::StructRef(self.builder.refs.object_class))
                                } else {
                                    *field_jvm_type
                                };

                                if *is_erased {
                                    match actual_type {
                                        JvmType::StructRef(class_idx)
                                            if class_idx != self.builder.refs.object_class =>
                                        {
                                            self.builder.frame.pop_type();
                                            self.builder.frame.push_type(VerificationType::Object {
                                                cpool_index: self.builder.refs.object_class,
                                            });
                                            self.builder.emit(Instruction::Checkcast(class_idx));
                                            self.builder.frame.pop_type();
                                            self.builder.frame.push_type(VerificationType::Object {
                                                cpool_index: class_idx,
                                            });
                                        }
                                        JvmType::Long | JvmType::Double | JvmType::Int => {
                                            self.builder.frame.pop_type();
                                            self.builder.frame.push_type(VerificationType::Object {
                                                cpool_index: self.builder.refs.object_class,
                                            });
                                            self.builder.unbox_if_needed(actual_type);
                                        }
                                        _ => {}
                                    }
                                }

                                let var_slot = self.builder.alloc_local(var_name.clone(), actual_type);
                                self.builder.emit_store(var_slot, actual_type);
                            }
                            TypedPattern::Constructor { args: sub_args, .. }
                                if sub_args.is_empty() =>
                            {
                                // Zero-arg constructor sub-pattern — just pop
                                self.builder.emit(Instruction::Pop);
                                self.builder.frame.pop_type();
                            }
                            TypedPattern::Constructor { .. } => {
                                // Nested constructor: store in local, recurse with CheckAndBind
                                let nested_type = if *is_erased {
                                    JvmType::StructRef(self.get_pattern_class_index(sub_pat)?)
                                } else {
                                    *field_jvm_type
                                };
                                let nested_slot = self.builder.next_local;
                                self.builder.next_local += 1;
                                self.builder.emit(Instruction::Astore(nested_slot as u8));
                                self.builder.frame.pop_type();
                                self.builder.frame.local_types.push(VerificationType::Object {
                                    cpool_index: match nested_type {
                                        JvmType::StructRef(idx) => idx,
                                        _ => self.builder.refs.string_class,
                                    },
                                });
                                if let Some(nested_ifeq) = self.compile_pattern(
                                    sub_pat,
                                    nested_slot,
                                    nested_type,
                                    scrutinee_tc_type,
                                    PatternMode::CheckAndBind,
                                )? {
                                    self.builder.nested_ifeq_patches.push(nested_ifeq);
                                }
                            }
                            TypedPattern::Wildcard { .. } => {
                                self.builder.emit(Instruction::Pop);
                                self.builder.frame.pop_type();
                            }
                            _ => {}
                        }
                    }
                }

                Ok(ifeq_idx)
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

                // instanceof + ifeq guard (CheckAndBind only)
                let ifeq_idx = if matches!(mode, PatternMode::CheckAndBind) {
                    self.builder.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.builder.push_jvm_type(scrutinee_type);
                    self.builder.emit(Instruction::Instanceof(tuple_class));
                    self.builder.pop_jvm_type(scrutinee_type);
                    self.builder.frame.push_type(VerificationType::Integer);

                    let idx = self.builder.emit_placeholder(Instruction::Ifeq(0));
                    self.builder.frame.pop_type();
                    Some(idx)
                } else {
                    None
                };

                // Extract and bind fields
                for (i, sub_pat) in elements.iter().enumerate() {
                    if matches!(sub_pat, TypedPattern::Wildcard { .. }) {
                        continue;
                    }
                    let field_ref = field_refs[i];
                    let elem_ty = &elem_types[i];
                    let elem_jvm_type = self.type_to_jvm(elem_ty)?;

                    self.builder.emit(Instruction::Aload(scrutinee_slot as u8));
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: tuple_class,
                    });
                    self.builder.emit(Instruction::Getfield(field_ref));
                    self.builder.frame.pop_type();
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: self.builder.refs.object_class,
                    });
                    self.builder.unbox_if_needed(elem_jvm_type);

                    if let TypedPattern::Var { name: var_name, .. } = sub_pat {
                        let var_slot = self.builder.alloc_local(var_name.clone(), elem_jvm_type);
                        self.builder.emit_store(var_slot, elem_jvm_type);
                    }
                }

                Ok(ifeq_idx)
            }
            _ => Err(CodegenError::UnsupportedExpr(format!(
                "unsupported pattern: {pattern:?}"
            ))),
        }
    }

    /// Get the class index for a constructor pattern's variant type's parent interface.
    pub(super) fn get_pattern_class_index(&self, pattern: &TypedPattern) -> Result<u16, CodegenError> {
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
}
