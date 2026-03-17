//! Expression compilers (literals, operators, control flow, data structures).

use std::collections::HashMap;

use krypton_parser::ast::{BinOp, Lit, UnaryOp};
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind};
use krypton_typechecker::types::Type;
use ristretto_classfile::attributes::{Instruction, VerificationType};

use super::compiler::{Compiler, CodegenError, JvmType};
use super::type_to_name;

impl Compiler {
    pub(super) fn compile_var(&mut self, name: &str) -> Result<JvmType, CodegenError> {
        // Check if this is a nullary variant constructor
        if let Some(sum_name) = self.types.variant_to_sum.get(name).cloned() {
            let sum_info = &self.types.sum_type_info[&sum_name];
            let vi = &sum_info.variants[name];
            if vi.fields.is_empty() {
                let singleton_field_ref = vi.singleton_field_ref.unwrap();
                let interface_class_index = sum_info.interface_class_index;
                self.builder.emit(Instruction::Getstatic(singleton_field_ref));
                let result_type = JvmType::StructRef(interface_class_index);
                self.builder.push_jvm_type(result_type);
                return Ok(result_type);
            }
        }

        let (slot, ty) = self
            .builder.locals
            .get(name)
            .copied()
            .ok_or_else(|| CodegenError::UndefinedVariable(name.to_string()))?;

        self.builder.emit_load(slot, ty);

        Ok(ty)
    }

    pub(super) fn compile_lit(&mut self, lit: &Lit) -> Result<JvmType, CodegenError> {
        match lit {
            Lit::Int(n) => {
                match *n {
                    0 => self.builder.emit(Instruction::Lconst_0),
                    1 => self.builder.emit(Instruction::Lconst_1),
                    _ => {
                        let idx = self.cp.add_long(*n)?;
                        self.builder.emit(Instruction::Ldc2_w(idx));
                    }
                }
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            Lit::Float(f) => {
                let idx = self.cp.add_double(*f)?;
                self.builder.emit(Instruction::Ldc2_w(idx));
                self.builder.frame.push_double_type();
                Ok(JvmType::Double)
            }
            Lit::Bool(b) => {
                self.builder.emit(if *b {
                    Instruction::Iconst_1
                } else {
                    Instruction::Iconst_0
                });
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            Lit::String(s) => {
                let idx = self.cp.add_string(s)?;
                if idx <= 255 {
                    self.builder.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.builder.emit(Instruction::Ldc_w(idx));
                }
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.string_class,
                });
                Ok(JvmType::Ref)
            }
            Lit::Unit => {
                self.builder.emit(Instruction::Iconst_0);
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
        }
    }

    pub(super) fn compile_binop(
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
                        self.builder.emit(instr);
                        self.builder.frame.pop_type_n(4);
                        self.builder.frame.push_long_type();
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
                        self.builder.emit(instr);
                        self.builder.frame.pop_type_n(4);
                        self.builder.frame.push_double_type();
                        Ok(JvmType::Double)
                    }
                    JvmType::Ref if matches!(op, BinOp::Add) => {
                        // String concat: invokevirtual String.concat
                        self.compile_expr(lhs, false)?;
                        self.compile_expr(rhs, false)?;
                        self.builder.emit(Instruction::Invokevirtual(self.builder.refs.string_concat));
                        self.builder.frame.pop_type(); // pop rhs string
                        Ok(JvmType::Ref)
                    }
                    _ => {
                        // User-type trait dispatch
                        let (trait_name, method_name) = match op {
                            BinOp::Add => ("Semigroup", "combine"),
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
            BinOp::And => {
                // Short-circuit AND: if lhs is false, result is false
                self.compile_expr(lhs, false)?;
                let false_label = self.builder.emit_placeholder(Instruction::Ifeq(0)); // placeholder
                self.builder.frame.pop_type();
                self.compile_expr(rhs, false)?;
                let end_label = self.builder.emit_placeholder(Instruction::Goto(0)); // placeholder
                self.builder.frame.pop_type();
                let false_pos = self.builder.code.len();
                // Record frame at false_pos (Ifeq target: stack has no boolean result)
                self.builder.frame.record_frame(false_pos as u16);
                self.builder.emit(Instruction::Iconst_0);
                self.builder.frame.push_type(VerificationType::Integer);
                let end_pos = self.builder.code.len();
                // Record frame at end_pos (both paths converge with Integer on stack)
                self.builder.frame.record_frame(end_pos as u16);
                // Patch jumps
                self.builder.patch(false_label, Instruction::Ifeq(false_pos as u16));
                self.builder.patch(end_label, Instruction::Goto(end_pos as u16));
                Ok(JvmType::Int)
            }
            BinOp::Or => {
                // Short-circuit OR: if lhs is true, result is true
                self.compile_expr(lhs, false)?;
                let true_label = self.builder.code.len();
                self.builder.emit(Instruction::Ifne(0)); // placeholder
                self.builder.frame.pop_type();
                self.compile_expr(rhs, false)?;
                let end_label = self.builder.emit_placeholder(Instruction::Goto(0)); // placeholder
                self.builder.frame.pop_type();
                let true_pos = self.builder.code.len();
                // Record frame at true_pos (Ifne target: stack has no boolean result)
                self.builder.frame.record_frame(true_pos as u16);
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                let end_pos = self.builder.code.len();
                // Record frame at end_pos (both paths converge with Integer on stack)
                self.builder.frame.record_frame(end_pos as u16);
                // Patch jumps
                self.builder.patch(true_label, Instruction::Ifne(true_pos as u16));
                self.builder.patch(end_label, Instruction::Goto(end_pos as u16));
                Ok(JvmType::Int)
            }
        }
    }

    /// Compile a binary operator via trait dictionary dispatch for user types.
    fn compile_trait_binop(
        &mut self,
        trait_name: &str,
        method_name: &str,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        result_jvm: JvmType,
    ) -> Result<JvmType, CodegenError> {
        let type_name = type_to_name(&lhs.ty);

        let dispatch = self.traits.trait_dispatch.get(trait_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no trait dispatch for {trait_name}"))
        })?;
        let iface_method_ref = *dispatch.method_refs.get(method_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no method {method_name} in {trait_name}"))
        })?;
        let iface_class = dispatch.interface_class;

        let singleton = self
            .traits
            .instance_singletons
            .get(&(trait_name.to_string(), type_name.clone()))
            .ok_or_else(|| {
                CodegenError::UndefinedVariable(format!(
                    "no instance of {trait_name} for {type_name}"
                ))
            })?;
        let field_ref = singleton.instance_field_ref;

        // Load singleton instance
        self.builder.emit(Instruction::Getstatic(field_ref));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: iface_class,
        });

        // Compile and box lhs
        let lhs_jvm = self.compile_expr(lhs, false)?;
        self.builder.box_if_needed(lhs_jvm);

        // Compile and box rhs
        let rhs_jvm = self.compile_expr(rhs, false)?;
        self.builder.box_if_needed(rhs_jvm);

        // invokeinterface (receiver + 2 args = 3)
        self.builder.emit(Instruction::Invokeinterface(iface_method_ref, 3));
        self.builder.frame.pop_type(); // rhs
        self.builder.frame.pop_type(); // lhs
        self.builder.frame.pop_type(); // receiver
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });

        // Unbox result
        self.builder.unbox_if_needed(result_jvm);
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

        let dispatch = self.traits.trait_dispatch.get(trait_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no trait dispatch for {trait_name}"))
        })?;
        let iface_method_ref = *dispatch.method_refs.get(method_name).ok_or_else(|| {
            CodegenError::UndefinedVariable(format!("no method {method_name} in {trait_name}"))
        })?;
        let iface_class = dispatch.interface_class;

        let singleton = self
            .traits
            .instance_singletons
            .get(&(trait_name.to_string(), type_name.clone()))
            .ok_or_else(|| {
                CodegenError::UndefinedVariable(format!(
                    "no instance of {trait_name} for {type_name}"
                ))
            })?;
        let field_ref = singleton.instance_field_ref;

        // Load singleton instance
        self.builder.emit(Instruction::Getstatic(field_ref));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: iface_class,
        });

        // Compile and box operand
        let op_jvm = self.compile_expr(operand, false)?;
        self.builder.box_if_needed(op_jvm);

        // invokeinterface (receiver + 1 arg = 2)
        self.builder.emit(Instruction::Invokeinterface(iface_method_ref, 2));
        self.builder.frame.pop_type(); // operand
        self.builder.frame.pop_type(); // receiver
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });

        // Unbox result
        self.builder.unbox_if_needed(result_jvm);
        Ok(result_jvm)
    }

    pub(super) fn compile_comparison(
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
            self.builder.emit(Instruction::Invokevirtual(self.builder.refs.string_equals));
            self.builder.frame.pop_type(); // pop arg
            self.builder.frame.pop_type(); // pop receiver
            self.builder.frame.push_type(VerificationType::Integer); // boolean result
            if matches!(op, BinOp::Neq) {
                // Negate: XOR with 1
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Ixor);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Integer);
            }
            return Ok(JvmType::Int);
        }

        // Bool equality: use integer comparison (bools are JvmType::Int)
        if operand_jvm == JvmType::Int && matches!(op, BinOp::Eq | BinOp::Neq) {
            self.compile_expr(lhs, false)?;
            self.compile_expr(rhs, false)?;
            // XOR gives 0 if equal, 1 if different
            self.builder.emit(Instruction::Ixor);
            self.builder.frame.pop_type_n(2);
            self.builder.frame.push_type(VerificationType::Integer);
            if matches!(op, BinOp::Eq) {
                // Negate: XOR with 1 (0→1, 1→0)
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Ixor);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Integer);
            }
            return Ok(JvmType::Int);
        }

        // User-type trait dispatch for Eq/Ord
        if !matches!(operand_jvm, JvmType::Long | JvmType::Double) {
            let (trait_name, method_name, swap, negate) = match op {
                BinOp::Eq => ("Eq", "eq", false, false),
                BinOp::Neq => ("Eq", "eq", false, true),
                BinOp::Lt => ("Ord", "lt", false, false),
                BinOp::Gt => ("Ord", "lt", true, false),
                BinOp::Le => ("Ord", "lt", true, true),
                BinOp::Ge => ("Ord", "lt", false, true),
                _ => unreachable!(),
            };
            let (lhs_arg, rhs_arg) = if swap { (rhs, lhs) } else { (lhs, rhs) };
            self.compile_trait_binop(trait_name, method_name, lhs_arg, rhs_arg, JvmType::Int)?;
            if negate {
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Ixor);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Integer);
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
        self.builder.emit(cmp_instr);

        // Lcmp/Dcmpl: pop two 2-slot values (4 slots), push int
        self.builder.frame.pop_type_n(4);
        self.builder.frame.push_type(VerificationType::Integer);

        let branch_idx = self.builder.current_offset();
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
        self.builder.emit(branch);

        // Ifxx consumes the int
        self.builder.frame.pop_type();

        // Record frame at false_target (stack state after Ifxx consumes int)
        let stack_at_false = self.builder.frame.stack_types.clone();
        self.builder.frame.record_frame(false_target);

        // True path: push 1
        self.builder.emit(Instruction::Iconst_1);
        self.builder.frame.push_type(VerificationType::Integer);

        // Record frame at after_target (stack has Integer on top)
        self.builder.frame.record_frame(after_target);
        let stack_after = self.builder.frame.stack_types.clone();

        self.builder.emit(Instruction::Goto(after_target));

        // False path: restore stack to state at false_target
        self.builder.frame.stack_types = stack_at_false;
        self.builder.emit(Instruction::Iconst_0);
        self.builder.frame.push_type(VerificationType::Integer);

        // After both paths merge, stack should match
        debug_assert_eq!(self.builder.frame.stack_types, stack_after);

        Ok(JvmType::Int)
    }

    pub(super) fn compile_unaryop(
        &mut self,
        op: &UnaryOp,
        operand: &TypedExpr,
    ) -> Result<JvmType, CodegenError> {
        let operand_jvm = self.type_to_jvm(&operand.ty)?;
        match op {
            UnaryOp::Neg => match operand_jvm {
                JvmType::Long => {
                    self.compile_expr(operand, false)?;
                    self.builder.emit(Instruction::Lneg);
                    Ok(JvmType::Long)
                }
                JvmType::Double => {
                    self.compile_expr(operand, false)?;
                    self.builder.emit(Instruction::Dneg);
                    Ok(JvmType::Double)
                }
                _ => self.compile_trait_unaryop("Neg", "neg", operand, operand_jvm),
            },
            UnaryOp::Not => {
                // Boolean NOT: XOR with 1
                self.compile_expr(operand, false)?;
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Ixor);
                self.builder.frame.pop_type();
                Ok(JvmType::Int)
            }
        }
    }

    pub(super) fn compile_if(
        &mut self,
        cond: &TypedExpr,
        then_: &TypedExpr,
        else_: &TypedExpr,
        in_tail: bool,
    ) -> Result<JvmType, CodegenError> {
        // Compile condition (produces Int 0/1 on stack)
        self.compile_expr(cond, false)?;

        // Ifeq consumes the int
        self.builder.frame.pop_type();

        // Emit Ifeq with placeholder — will be patched with instruction index
        let ifeq_idx = self.builder.emit_placeholder(Instruction::Ifeq(0)); // placeholder

        // Save stack state at branch point (after consuming condition)
        let stack_at_branch = self.builder.frame.stack_types.clone();
        let locals_at_branch = self.builder.locals.clone();
        let local_types_at_branch = self.builder.frame.local_types.clone();
        let next_local_at_branch = self.builder.next_local;

        // Compile then branch
        let then_type = self.compile_expr(then_, in_tail)?;
        let stack_after_then = self.builder.frame.stack_types.clone();
        let then_next_local = self.builder.next_local;

        // Restore locals for else branch (then-branch locals are out of scope)
        self.builder.locals = locals_at_branch.clone();
        self.builder.frame.local_types = local_types_at_branch.clone();
        self.builder.next_local = next_local_at_branch;

        // Emit Goto with placeholder
        let goto_idx = self.builder.emit_placeholder(Instruction::Goto(0)); // placeholder

        // else starts at this instruction index
        let else_start = self.builder.current_offset();

        // Record frame at else_start with stack state from branch point
        self.builder.frame.stack_types = stack_at_branch;
        self.builder.frame.record_frame(else_start);

        // Compile else branch
        let _else_type = self.compile_expr(else_, in_tail)?;
        let else_next_local = self.builder.next_local;

        // Restore locals for merge point (else-branch locals are out of scope);
        // record high-water mark so max_locals covers branch-local slots.
        let branch_hwm = then_next_local.max(else_next_local);
        self.builder.locals = locals_at_branch;
        self.builder.frame.local_types = local_types_at_branch;
        self.builder.next_local = next_local_at_branch;
        if branch_hwm > self.builder.max_locals_hwm {
            self.builder.max_locals_hwm = branch_hwm;
        }

        let after_else = self.builder.current_offset();

        // Record frame at after_else
        self.builder.frame.record_frame(after_else);

        debug_assert_eq!(self.builder.frame.stack_types, stack_after_then);

        // Patch: Ifeq should jump to else_start instruction index
        self.builder.patch(ifeq_idx, Instruction::Ifeq(else_start));
        // Patch: Goto should jump past else
        self.builder.patch(goto_idx, Instruction::Goto(after_else));

        Ok(then_type)
    }

    pub(super) fn compile_let(
        &mut self,
        name: &str,
        value: &TypedExpr,
        body: &Option<Box<TypedExpr>>,
        in_tail: bool,
        span: krypton_parser::ast::Span,
    ) -> Result<JvmType, CodegenError> {
        // Function-typed bindings need local_fn_info so later `f(args)` calls can
        // unbox/cast the invokeinterface result correctly.
        let is_fn_value = matches!(value.kind, TypedExprKind::Lambda { .. })
            || matches!(
                match &value.ty {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                },
                Type::Fn(_, _)
            );

        // Emit shadow close for old binding before compiling new value
        let shadow_close = self.auto_close.shadow_closes.get(&span).cloned();

        let ty = self.compile_expr(value, false)?;

        // Emit shadow close after evaluating value but before storing
        if let Some(binding) = shadow_close {
            // Save the new value to a temp slot to preserve it while we close the old binding
            let temp_slot = self.builder.alloc_anonymous_local(ty);
            self.builder.emit_store(temp_slot, ty);

            self.emit_auto_close(&binding)?;

            // Reload the new value
            self.builder.emit_load(temp_slot, ty);
        }

        let slot = self.builder.alloc_local(name.to_string(), ty);
        self.builder.emit_store(slot, ty);

        // If the value is function-typed, record local_fn_info from the TypedExpr's type.
        if is_fn_value {
            let fn_type = match &value.ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            if let Type::Fn(param_types, ret_type) = fn_type {
                let param_jvm: Result<Vec<JvmType>, _> =
                    param_types.iter().map(|t| self.type_to_jvm(t)).collect();
                if let Ok(param_jvm) = param_jvm {
                    if let Ok(ret_jvm) = self.type_to_jvm(ret_type) {
                        self.builder.local_fn_info
                            .insert(name.to_string(), (param_jvm, ret_jvm));
                    }
                }
            }
        }

        if let Some(body) = body {
            self.compile_expr(body, in_tail)
        } else {
            self.builder.emit(Instruction::Iconst_0);
            self.builder.frame.push_type(VerificationType::Integer);
            Ok(JvmType::Int)
        }
    }

    pub(super) fn compile_tuple(&mut self, elems: &[TypedExpr], _ty: &Type) -> Result<JvmType, CodegenError> {
        let arity = elems.len();
        let info = self
            .types
            .tuple_info
            .get(&arity)
            .ok_or_else(|| CodegenError::TypeError(format!("unknown tuple arity: {arity}")))?;
        let class_index = info.class_index;
        let constructor_ref = info.constructor_ref;

        // new TupleN + dup
        self.builder.emit_new_dup(class_index);

        // Compile each element and box if primitive
        for elem in elems {
            let elem_type = self.compile_expr(elem, false)?;
            self.builder.box_if_needed(elem_type);
        }

        // Pop args (all Object after boxing) + 2 uninit refs
        for _ in 0..arity {
            self.builder.frame.pop_type(); // each boxed Object
        }
        self.builder.frame.pop_type(); // dup'd uninit
        self.builder.frame.pop_type(); // original uninit

        // invokespecial TupleN.<init>
        self.builder.emit(Instruction::Invokespecial(constructor_ref));
        let result_type = JvmType::StructRef(class_index);
        self.builder.push_jvm_type(result_type);

        Ok(result_type)
    }

    pub(super) fn emit_int_const(&mut self, n: i32) {
        match n {
            0 => self.builder.emit(Instruction::Iconst_0),
            1 => self.builder.emit(Instruction::Iconst_1),
            2 => self.builder.emit(Instruction::Iconst_2),
            3 => self.builder.emit(Instruction::Iconst_3),
            4 => self.builder.emit(Instruction::Iconst_4),
            5 => self.builder.emit(Instruction::Iconst_5),
            _ => {
                let idx = self
                    .cp
                    .add_integer(n)
                    .expect("failed to add integer constant");
                if idx <= 255 {
                    self.builder.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.builder.emit(Instruction::Ldc_w(idx));
                }
            }
        }
    }

    pub(super) fn compile_vec_lit(&mut self, elems: &[TypedExpr]) -> Result<JvmType, CodegenError> {
        let info = self
            .vec_info
            .as_ref()
            .ok_or_else(|| CodegenError::TypeError("Vec info not registered".to_string()))?
            .clone();

        let arr_vtype = VerificationType::Object {
            cpool_index: info.class_index,
        };

        // new KryptonArray(capacity)
        self.builder.emit(Instruction::New(info.class_index));
        self.builder.frame.push_type(VerificationType::UninitializedThis);
        self.builder.emit(Instruction::Dup);
        self.builder.frame.push_type(VerificationType::UninitializedThis);
        self.emit_int_const(elems.len() as i32);
        self.builder.frame.push_type(VerificationType::Integer);
        self.builder.emit(Instruction::Invokespecial(info.init_ref));
        self.builder.frame.pop_type(); // int
        self.builder.frame.pop_type(); // uninit dup
        self.builder.frame.pop_type(); // uninit orig
        self.builder.frame.push_type(arr_vtype.clone());
        // stack: [arr]

        for (i, elem) in elems.iter().enumerate() {
            self.builder.emit(Instruction::Dup);
            self.builder.frame.push_type(arr_vtype.clone());
            // stack: [arr, arr]
            self.emit_int_const(i as i32);
            self.builder.frame.push_type(VerificationType::Integer);
            let elem_type = self.compile_expr(elem, false)?;
            self.builder.box_if_needed(elem_type);
            // stack: [arr, arr, index, boxed_elem]
            self.builder.emit(Instruction::Invokevirtual(info.set_ref));
            self.builder.frame.pop_type(); // boxed_elem
            self.builder.frame.pop_type(); // index
            self.builder.frame.pop_type(); // arr (dup'd)
                                   // stack: [arr]
        }

        // freeze
        self.builder.emit(Instruction::Dup);
        self.builder.frame.push_type(arr_vtype.clone());
        self.builder.emit(Instruction::Invokevirtual(info.freeze_ref));
        self.builder.frame.pop_type(); // arr (dup'd, consumed by freeze)
                               // stack: [arr]

        Ok(JvmType::StructRef(info.class_index))
    }

    pub(super) fn compile_field_access(
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
        let (struct_name, accessor_ref, field_type) = {
            let si = self
                .types
                .struct_info
                .values()
                .find(|s| s.class_index == class_idx)
                .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
            let accessor_ref = *si
                .accessor_refs
                .get(field)
                .ok_or_else(|| CodegenError::TypeError(format!("unknown field: {field}")))?;
            let field_type = si
                .fields
                .iter()
                .find(|(n, _)| n == field)
                .map(|(_, t)| *t)
                .ok_or_else(|| CodegenError::TypeError(format!("unknown field: {field}")))?;
            (si.class_name.clone(), accessor_ref, field_type)
        };

        self.builder.pop_jvm_type(base_type);
        self.builder.emit(Instruction::Invokevirtual(accessor_ref));
        self.builder.push_jvm_type(field_type);

        Ok(field_type)
    }

    pub(super) fn compile_question_mark(
        &mut self,
        inner: &TypedExpr,
        is_option: bool,
        result_ty: &Type,
        span: krypton_parser::ast::Span,
    ) -> Result<JvmType, CodegenError> {
        // Compile inner expression — produces a StructRef for the sum type (Result or Option)
        let inner_type = self.compile_expr(inner, false)?;

        let sum_name = if is_option { "Option" } else { "Result" };
        let success_variant = if is_option { "Some" } else { "Ok" };

        let sum_info = self
            .types
            .sum_type_info
            .get(sum_name)
            .ok_or_else(|| CodegenError::TypeError(format!("unknown sum type: {sum_name}")))?;
        let interface_class_index = sum_info.interface_class_index;
        let success_vi = sum_info.variants.get(success_variant).ok_or_else(|| {
            CodegenError::TypeError(format!("unknown variant: {success_variant}"))
        })?;
        let success_class_index = success_vi.class_index;
        let success_field_refs = success_vi.field_refs.clone();
        let success_fields = success_vi.fields.clone();

        // Store inner expression result in a temp local
        let temp_slot = self.builder.next_local;
        self.builder.next_local += 1;
        self.builder.emit(Instruction::Astore(temp_slot as u8));
        self.builder.pop_jvm_type(inner_type);
        self.builder.frame.local_types.push(VerificationType::Object {
            cpool_index: interface_class_index,
        });

        // instanceof check: is it the success variant?
        self.builder.emit(Instruction::Aload(temp_slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: interface_class_index,
        });
        self.builder.emit(Instruction::Instanceof(success_class_index));
        self.builder.frame.pop_type(); // pop ref
        self.builder.frame.push_type(VerificationType::Integer); // push int result

        // Ifeq → early return branch (not the success variant)
        let ifeq_idx = self.builder.emit_placeholder(Instruction::Ifeq(0)); // placeholder
        self.builder.frame.pop_type(); // consume int from instanceof

        // Save stack state at branch point
        let stack_at_branch = self.builder.frame.stack_types.clone();

        // Success path: checkcast and extract value0 field
        self.builder.emit(Instruction::Aload(temp_slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: interface_class_index,
        });
        self.builder.emit(Instruction::Checkcast(success_class_index));
        self.builder.frame.pop_type(); // pop old ref type
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: success_class_index,
        });

        // Getfield value0
        let field_ref = success_field_refs[0];
        let (_fname, field_jvm_type, is_erased) = &success_fields[0];
        let field_jvm_type = *field_jvm_type;
        let is_erased = *is_erased;
        self.builder.emit(Instruction::Getfield(field_ref));
        self.builder.frame.pop_type(); // pop checkcast ref
        if is_erased {
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
        } else {
            self.builder.push_jvm_type(field_jvm_type);
        }

        // Determine the actual JVM type of the unwrapped value
        let actual_jvm_type = self.type_to_jvm(result_ty)?;
        let result_type = if is_erased {
            // Unbox from Object to the actual type
            self.builder.unbox_if_needed(actual_jvm_type);
            actual_jvm_type
        } else {
            field_jvm_type
        };

        let stack_after_success = self.builder.frame.stack_types.clone();

        // Goto after (skip early return)
        let goto_idx = self.builder.emit_placeholder(Instruction::Goto(0)); // placeholder

        // Early return branch: close live resources, load temp and Areturn
        let early_return_start = self.builder.current_offset();
        self.builder.frame.stack_types = stack_at_branch;
        self.builder.frame.record_frame(early_return_start);

        // Auto-close live resources before early return
        if let Some(bindings) = self.auto_close.early_returns.get(&span).cloned() {
            for binding in &bindings {
                self.emit_auto_close(binding)?;
            }
        }

        self.builder.emit(Instruction::Aload(temp_slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: interface_class_index,
        });
        self.builder.emit(Instruction::Areturn);
        self.builder.frame.pop_type();

        // After label
        let after = self.builder.current_offset();
        self.builder.frame.stack_types = stack_after_success;
        self.builder.frame.record_frame(after);

        // Patch jumps
        self.builder.patch(ifeq_idx, Instruction::Ifeq(early_return_start));
        self.builder.patch(goto_idx, Instruction::Goto(after));

        Ok(result_type)
    }

    pub(super) fn compile_struct_update(
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

        let base_slot = self.builder.alloc_anonymous_local(base_type);
        self.builder.emit_store(base_slot, base_type);

        // Look up struct info
        let si = self
            .types
            .struct_info
            .values()
            .find(|s| s.class_index == class_idx)
            .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
        let constructor_ref = si.constructor_ref;
        let fields = si.fields.clone();
        let accessor_refs = si.accessor_refs.clone();

        self.builder.emit_new_dup(class_idx);

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
                self.builder.emit(Instruction::Aload(base_slot as u8));
                self.builder.push_jvm_type(base_type);
                let accessor_ref = accessor_refs[field_name];
                self.builder.emit(Instruction::Invokevirtual(accessor_ref));
                self.builder.pop_jvm_type(base_type);
                self.builder.push_jvm_type(*field_type);
            }
        }

        // Pop args + uninit refs
        for (_, ft) in &fields {
            self.builder.pop_jvm_type(*ft);
        }
        self.builder.frame.pop_type(); // dup'd uninit
        self.builder.frame.pop_type(); // original uninit

        self.builder.emit(Instruction::Invokespecial(constructor_ref));
        self.builder.push_jvm_type(base_type);

        Ok(base_type)
    }

    pub(super) fn compile_struct_lit(
        &mut self,
        fields: &[(String, TypedExpr)],
        struct_ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        let struct_jvm = self.type_to_jvm(struct_ty)?;
        let class_idx = match struct_jvm {
            JvmType::StructRef(idx) => idx,
            _ => {
                return Err(CodegenError::TypeError(
                    "struct literal for non-struct type".to_string(),
                ))
            }
        };

        let si = self
            .types
            .struct_info
            .values()
            .find(|s| s.class_index == class_idx)
            .ok_or_else(|| CodegenError::TypeError("unknown struct class".to_string()))?;
        let constructor_ref = si.constructor_ref;
        let ordered_fields = si.fields.clone();

        let field_values: HashMap<&str, &TypedExpr> = fields
            .iter()
            .map(|(name, expr)| (name.as_str(), expr))
            .collect();

        self.builder.emit_new_dup(class_idx);

        for (field_name, _) in &ordered_fields {
            let value = field_values.get(field_name.as_str()).ok_or_else(|| {
                CodegenError::TypeError(format!("missing struct field: {field_name}"))
            })?;
            self.compile_expr(value, false)?;
        }

        for (_, field_type) in &ordered_fields {
            self.builder.pop_jvm_type(*field_type);
        }
        self.builder.frame.pop_type();
        self.builder.frame.pop_type();

        self.builder.emit(Instruction::Invokespecial(constructor_ref));
        self.builder.push_jvm_type(struct_jvm);

        Ok(struct_jvm)
    }

    pub(super) fn compile_recur(
        &mut self,
        args: &[TypedExpr],
        in_tail: bool,
        expr_span: krypton_parser::ast::Span,
    ) -> Result<JvmType, CodegenError> {
        if !in_tail {
            return Err(CodegenError::RecurNotInTailPosition);
        }
        let return_type = self
            .builder.fn_return_type
            .ok_or_else(|| CodegenError::UnsupportedExpr("recur outside function".to_string()))?;
        let fn_params = self.builder.fn_params.clone();

        // Auto-close live resources before recur
        if let Some(bindings) = self.auto_close.recur_closes.get(&expr_span).cloned() {
            for binding in &bindings {
                self.emit_auto_close(binding)?;
            }
        }

        // Compile all args onto the stack
        for arg in args {
            self.compile_expr(arg, false)?;
        }

        // Store to param local slots in reverse order (stack is LIFO)
        for &(slot, jvm_ty) in fn_params.iter().rev() {
            self.builder.emit_store(slot, jvm_ty);
        }

        // Record StackMapTable frame at recur target for back-edge.
        let recur_target = self.builder.recur_target;
        let initial_locals: Vec<VerificationType> = self.builder.recur_frame_locals.clone();
        self.builder.frame.frames.insert(
            recur_target,
            (
                initial_locals
                    .iter()
                    .filter(|vt| !matches!(vt, VerificationType::Top))
                    .cloned()
                    .collect(),
                vec![],
            ),
        );

        // Goto recur target (after Nop)
        self.builder.emit(Instruction::Goto(recur_target));

        // Push return type onto stack tracker for consistency with if-else merging.
        self.builder.push_jvm_type(return_type);

        // Record a stack map frame at the (unreachable) instruction after the goto.
        let after_goto = self.builder.code.len() as u16;
        self.builder.frame.record_frame(after_goto);

        Ok(return_type)
    }

    pub(super) fn compile_do(&mut self, exprs: &[TypedExpr], in_tail: bool) -> Result<JvmType, CodegenError> {
        let mut last_type = JvmType::Int;
        for (i, expr) in exprs.iter().enumerate() {
            let is_last = i == exprs.len() - 1;
            let expr_tail = in_tail && is_last;
            let ty = self.compile_expr(expr, expr_tail)?;

            if !is_last {
                // Pop the value — it's not used
                match ty {
                    JvmType::Long | JvmType::Double => {
                        self.builder.emit(Instruction::Pop2);
                        self.builder.frame.pop_type_n(2);
                    }
                    _ => {
                        self.builder.emit(Instruction::Pop);
                        self.builder.frame.pop_type();
                    }
                }
            }
            last_type = ty;
        }
        Ok(last_type)
    }

    /// Emit a close() call for an auto-close binding via the Resource trait dispatch.
    pub(super) fn emit_auto_close(
        &mut self,
        binding: &krypton_typechecker::typed_ast::AutoCloseBinding,
    ) -> Result<(), CodegenError> {
        let key = ("Resource".to_string(), binding.type_name.clone());
        let singleton = self.traits.instance_singletons.get(&key).ok_or_else(|| {
            CodegenError::TypeError(format!("no Resource instance for {}", binding.type_name))
        })?;
        let instance_field_ref = singleton.instance_field_ref;
        let dispatch =
            self.traits.trait_dispatch.get("Resource").ok_or_else(|| {
                CodegenError::TypeError("Resource trait dispatch not found".into())
            })?;
        let interface_class = dispatch.interface_class;
        let method_ref = *dispatch
            .method_refs
            .get("close")
            .ok_or_else(|| CodegenError::TypeError("close method ref not found".into()))?;

        // getstatic Resource$Type.INSTANCE
        self.builder.emit(Instruction::Getstatic(instance_field_ref));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: interface_class,
        });

        // aload <resource_local>
        let (slot, _) = self
            .builder.locals
            .get(&binding.name)
            .copied()
            .ok_or_else(|| CodegenError::UndefinedVariable(binding.name.clone()))?;
        self.builder.emit(Instruction::Aload(slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });

        // invokeinterface Resource.close, 2
        self.builder.emit(Instruction::Invokeinterface(method_ref, 2));
        self.builder.frame.pop_type();
        self.builder.frame.pop_type(); // pop receiver + arg
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });

        // pop Unit return
        self.builder.emit(Instruction::Pop);
        self.builder.frame.pop_type();
        Ok(())
    }
}
