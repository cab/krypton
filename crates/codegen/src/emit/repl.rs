//! REPL-specific codegen: compiles IR modules into class files with an `eval()` wrapper
//! that loads prior bindings from Var registry and returns a boxed result.

use std::collections::HashMap;

use krypton_ir::Type;
use krypton_typechecker::link_context::{LinkContext, ModuleLinkView};
use krypton_typechecker::module_interface::ModulePath;
use ristretto_classfile::attributes::{Instruction, VerificationType};
use ristretto_classfile::{Method, MethodAccessFlags};

use super::compiler::{CodegenError, Compiler, JvmType};
use super::{build_instance_class_map, compile_module_inner};

/// Compile IR modules for a REPL input. Returns class files as (name, bytes) pairs.
/// The first module in `ir_modules` is the REPL module; rest are dependencies.
///
/// Instead of a `main()` wrapper, this emits a `public static Object eval()` method that:
/// 1. Loads prior REPL bindings from `Registry.lookup(name).get()` and unboxes them
/// 2. Calls the compiled `__eval(...)` with those values
/// 3. Boxes the return value
/// 4. Optionally stores the result in a `Var` via `Registry.intern(name).set(result)`
/// 5. Returns the boxed result
pub fn compile_repl_input(
    ir_modules: &[krypton_ir::Module],
    main_class_name: &str,
    link_ctx: &LinkContext,
    module_sources: &HashMap<String, String>,
    repl_vars: &[(String, Type)],
    store_var: Option<&str>,
    show_wrapped: bool,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    let mut all_classes = Vec::new();

    let root_module_path = ir_modules
        .first()
        .map(|m| m.module_path.as_str())
        .unwrap_or("");

    for ir_module in ir_modules {
        let is_entry = ir_module.module_path.as_str() == root_module_path;
        let class_name = if is_entry {
            main_class_name
        } else {
            ir_module.module_path.as_str()
        };
        let view = link_ctx
            .view_for(&ModulePath::new(ir_module.module_path.as_str()))
            .unwrap_or_else(|| {
                panic!(
                    "ICE: no LinkContext view for module '{}'",
                    ir_module.module_path
                )
            });

        if is_entry {
            let classes =
                compile_repl_module(ir_module, class_name, &view, repl_vars, store_var, show_wrapped)
                    .map_err(|e| {
                        if let Some(s) = module_sources.get(ir_module.module_path.as_str()) {
                            return e.with_source(
                                ir_module.module_path.as_str().to_string(),
                                s.clone(),
                            );
                        }
                        e
                    })?;
            all_classes.extend(classes);
        } else {
            // Non-entry modules compile normally (no main required)
            let classes =
                compile_module_inner(ir_module, class_name, false, &view).map_err(|e| {
                    if let Some(s) = module_sources.get(ir_module.module_path.as_str()) {
                        return e.with_source(
                            ir_module.module_path.as_str().to_string(),
                            s.clone(),
                        );
                    }
                    e
                })?;
            all_classes.extend(classes);
        }
    }

    Ok(all_classes)
}

/// Compile the REPL entry module with an eval() wrapper instead of main().
fn compile_repl_module(
    ir_module: &krypton_ir::Module,
    class_name: &str,
    link_view: &ModuleLinkView<'_>,
    repl_vars: &[(String, Type)],
    store_var: Option<&str>,
    show_wrapped: bool,
) -> Result<Vec<(String, Vec<u8>)>, CodegenError> {
    let mut compiler = Compiler::new(class_name, link_view)?;
    compiler.types.class_descriptors.insert(
        compiler.builder.refs.object_class,
        "Ljava/lang/Object;".to_string(),
    );

    // Phase 1: Register types
    let module_path = ir_module.module_path.as_str();
    compiler.register_extern_types_ir(ir_module)?;
    compiler.register_imported_extern_types(module_path)?;
    compiler.register_imported_structs_from_metadata(module_path)?;
    compiler.register_imported_sum_types_from_metadata(module_path)?;

    let mut result_classes: Vec<(String, Vec<u8>)> = Vec::new();
    result_classes.extend(compiler.register_structs_ir(ir_module)?);
    result_classes.extend(compiler.register_sum_types_ir(ir_module)?);

    // Phase 2: Register FunN interfaces, Vec, traits, and instances
    compiler.lambda.preregister_fun_interfaces(
        &mut compiler.cp,
        &mut compiler.types.class_descriptors,
    )?;
    compiler.register_fun_interfaces_ir(ir_module)?;
    compiler.register_vec()?;
    compiler.register_tuples_ir(ir_module)?;
    result_classes.extend(compiler.register_traits_ir(ir_module)?);
    result_classes.extend(compiler.register_extern_traits_ir(ir_module)?);
    result_classes.extend(compiler.register_builtin_instances_ir(ir_module)?);

    let instance_class_map = build_instance_class_map(ir_module, link_view);
    compiler.register_imported_instances(&instance_class_map)?;
    result_classes.extend(compiler.register_instance_defs_ir(ir_module, class_name)?);

    // Phase 3: Register functions
    compiler.register_functions_ir(ir_module, compiler.this_class)?;

    // Phase 4: Compile function bodies
    let extra_methods = compiler.compile_function_bodies_ir(ir_module)?;

    // Instead of emit_main_wrapper, emit eval() wrapper
    emit_eval_wrapper(&mut compiler, repl_vars, store_var, show_wrapped)?;

    let class_bytes = compiler.build_class(extra_methods, false)?;
    // The main REPL class (containing eval()) must be first — the JVM host
    // uses the first class in the list as the eval entry point.
    result_classes.insert(0, (class_name.to_string(), class_bytes));

    Ok(result_classes)
}

/// Emit the `public static Object[] eval()` method body into the compiler's builder.
/// This method:
/// 1. For each repl_var, calls Registry.lookup(name).get() and unboxes to the right type
/// 2. Calls __eval with those loaded values
/// 3. When `show_wrapped`: destructures tuple, stores raw value, returns `[value, displayString]`
/// 4. When `!show_wrapped`: boxes return value, optionally stores, returns `[value, null]`
fn emit_eval_wrapper(
    compiler: &mut Compiler<'_>,
    repl_vars: &[(String, Type)],
    store_var: Option<&str>,
    show_wrapped: bool,
) -> Result<(), CodegenError> {
    // Find __eval's method info
    let eval_info = compiler
        .types
        .get_function("__eval")
        .ok_or_else(|| {
            CodegenError::TypeError("ICE: __eval not registered".to_string(), None)
        })?;
    let eval_method_ref = eval_info.method_ref;
    let eval_return_type = eval_info.return_type;

    compiler.reset_method_state();
    compiler.builder.next_local = 0; // static method, no args
    compiler.builder.frame.local_types.clear();

    // Add constant pool entries for Registry and Var
    let registry_class = compiler.cp.add_class("krypton/repl/Registry")?;
    let registry_lookup = compiler.cp.add_method_ref(
        registry_class,
        "lookup",
        "(Ljava/lang/String;)Lkrypton/repl/Var;",
    )?;
    let var_class = compiler.cp.add_class("krypton/repl/Var")?;
    let var_get = compiler
        .cp
        .add_method_ref(var_class, "get", "()Ljava/lang/Object;")?;

    // Prologue: load each prior binding from Registry
    for (name, ir_type) in repl_vars {
        let jvm_type = compiler.type_to_jvm(ir_type)?;

        // Push the var name string
        let name_idx = compiler.cp.add_string(name)?;
        compiler.builder.emit(Instruction::Ldc_w(name_idx));
        compiler.builder.frame.push_type(VerificationType::Object {
            cpool_index: compiler.builder.refs.string_class,
        });

        // Registry.lookup(name) -> Var
        compiler
            .builder
            .emit(Instruction::Invokestatic(registry_lookup));
        compiler.builder.frame.pop_type(); // pop String
        compiler
            .builder
            .frame
            .push_type(VerificationType::Object {
                cpool_index: var_class,
            });

        // Var.get() -> Object
        compiler
            .builder
            .emit(Instruction::Invokevirtual(var_get));
        compiler.builder.frame.pop_type(); // pop Var
        compiler
            .builder
            .frame
            .push_type(VerificationType::Object {
                cpool_index: compiler.builder.refs.object_class,
            });

        // Unbox if needed
        compiler.builder.unbox_if_needed(jvm_type);

        // Store in local slot
        let slot = compiler.builder.next_local;
        let slot_size: u16 = match jvm_type {
            JvmType::Long | JvmType::Double => 2,
            _ => 1,
        };
        compiler.builder.next_local += slot_size;
        compiler.builder.emit_store(slot, jvm_type);

        // Track in frame local types
        let vtypes = compiler.builder.jvm_type_to_vtypes(jvm_type);
        while compiler.builder.frame.local_types.len() < (slot + slot_size) as usize {
            compiler
                .builder
                .frame
                .local_types
                .push(VerificationType::Top);
        }
        for (i, vt) in vtypes.iter().enumerate() {
            compiler.builder.frame.local_types[slot as usize + i] = vt.clone();
        }
    }

    // Load all locals back onto stack for __eval call
    let mut load_slot: u16 = 0;
    for (_, ir_type) in repl_vars {
        let jvm_type = compiler.type_to_jvm(ir_type)?;
        compiler.builder.emit_load(load_slot, jvm_type);
        load_slot += match jvm_type {
            JvmType::Long | JvmType::Double => 2,
            _ => 1,
        };
    }

    // Call __eval(...)
    compiler
        .builder
        .emit(Instruction::Invokestatic(eval_method_ref));
    // Pop params from frame stack
    for (_, ir_type) in repl_vars {
        let jvm_type = compiler.type_to_jvm(ir_type)?;
        match jvm_type {
            JvmType::Long | JvmType::Double => compiler.builder.frame.pop_type_n(2),
            _ => compiler.builder.frame.pop_type(),
        }
    }
    compiler.builder.push_jvm_type(eval_return_type);

    let object_class = compiler.builder.refs.object_class;

    if show_wrapped {
        // __eval returned a Tuple2(rawValue, showString).
        // Store tuple in a local, then extract elements.
        let tuple_slot = compiler.builder.next_local;
        compiler.builder.next_local += 1;
        compiler.builder.emit(Instruction::Astore(tuple_slot as u8));
        compiler.builder.frame.pop_type(); // pop tuple from stack

        // Get the Tuple2 accessor method refs
        let tuple_info = compiler.types.tuple_info.get(&2).ok_or_else(|| {
            CodegenError::TypeError("ICE: Tuple2 not registered for show_wrapped".to_string(), None)
        })?;
        let tuple_class = tuple_info.class_index;
        let field_0_ref = tuple_info.field_refs[0]; // _0()
        let field_1_ref = tuple_info.field_refs[1]; // _1()

        // Extract _0 (raw value) into local
        compiler.builder.emit(Instruction::Aload(tuple_slot as u8));
        compiler.builder.frame.push_type(VerificationType::Object {
            cpool_index: tuple_class,
        });
        compiler.builder.emit(Instruction::Invokevirtual(field_0_ref));
        compiler.builder.frame.pop_type(); // pop tuple
        compiler.builder.frame.push_type(VerificationType::Object {
            cpool_index: object_class,
        });
        let value_slot = compiler.builder.next_local;
        compiler.builder.next_local += 1;
        compiler.builder.emit(Instruction::Astore(value_slot as u8));
        compiler.builder.frame.pop_type();

        // Store raw value in registry if needed
        if let Some(var_name) = store_var {
            emit_registry_store(compiler, registry_class, var_class, var_name, value_slot)?;
        }

        // Extract _1 (display string) into local
        compiler.builder.emit(Instruction::Aload(tuple_slot as u8));
        compiler.builder.frame.push_type(VerificationType::Object {
            cpool_index: tuple_class,
        });
        compiler.builder.emit(Instruction::Invokevirtual(field_1_ref));
        compiler.builder.frame.pop_type(); // pop tuple
        compiler.builder.frame.push_type(VerificationType::Object {
            cpool_index: object_class,
        });
        let display_slot = compiler.builder.next_local;
        compiler.builder.next_local += 1;
        compiler.builder.emit(Instruction::Astore(display_slot as u8));
        compiler.builder.frame.pop_type();

        // Build Object[2] = [value, display]
        emit_result_array(compiler, value_slot, display_slot)?;
    } else {
        // Box return value
        compiler.builder.box_if_needed(eval_return_type);

        // Store boxed value in local
        let value_slot = compiler.builder.next_local;
        compiler.builder.next_local += 1;
        compiler.builder.emit(Instruction::Astore(value_slot as u8));
        compiler.builder.frame.pop_type();

        // Store in registry if needed
        if let Some(var_name) = store_var {
            emit_registry_store(compiler, registry_class, var_class, var_name, value_slot)?;
        }

        // Build Object[2] = [value, null]
        emit_result_array_with_null(compiler, value_slot)?;
    }

    // areturn (return Object[])
    compiler.builder.emit(Instruction::Areturn);

    // Add eval method to class
    let eval_name_idx = compiler.cp.add_utf8("eval")?;
    let eval_desc_idx = compiler.cp.add_utf8("()[Ljava/lang/Object;")?;
    let eval_code = compiler.builder.finish_method();
    let eval_method = Method {
        access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
        name_index: eval_name_idx,
        descriptor_index: eval_desc_idx,
        attributes: vec![eval_code],
    };
    compiler.lambda.lambda_methods.push(eval_method);

    Ok(())
}

/// Emit bytecode to store a value from a local slot into the Registry.
fn emit_registry_store(
    compiler: &mut Compiler<'_>,
    registry_class: u16,
    var_class: u16,
    var_name: &str,
    value_slot: u16,
) -> Result<(), CodegenError> {
    let registry_intern = compiler.cp.add_method_ref(
        registry_class,
        "intern",
        "(Ljava/lang/String;)Lkrypton/repl/Var;",
    )?;
    let var_set = compiler.cp.add_method_ref(
        var_class,
        "set",
        "(Ljava/lang/Object;)V",
    )?;

    // Registry.intern(name)
    let name_idx = compiler.cp.add_string(var_name)?;
    compiler.builder.emit(Instruction::Ldc_w(name_idx));
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: compiler.builder.refs.string_class,
    });
    compiler
        .builder
        .emit(Instruction::Invokestatic(registry_intern));
    compiler.builder.frame.pop_type(); // pop String
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: var_class,
    });

    // Load value
    compiler.builder.emit(Instruction::Aload(value_slot as u8));
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: compiler.builder.refs.object_class,
    });

    // Var.set(Object)
    compiler
        .builder
        .emit(Instruction::Invokevirtual(var_set));
    compiler.builder.frame.pop_type(); // pop value
    compiler.builder.frame.pop_type(); // pop Var

    Ok(())
}

/// Emit bytecode to create Object[2] = [value, display] and leave it on the stack.
fn emit_result_array(
    compiler: &mut Compiler<'_>,
    value_slot: u16,
    display_slot: u16,
) -> Result<(), CodegenError> {
    let object_class = compiler.builder.refs.object_class;

    // iconst_2; anewarray Object
    compiler.builder.emit(Instruction::Iconst_2);
    compiler.builder.frame.push_type(VerificationType::Integer);
    compiler.builder.emit(Instruction::Anewarray(object_class));
    compiler.builder.frame.pop_type(); // pop int
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });

    // dup; iconst_0; aload value; aastore
    compiler.builder.emit(Instruction::Dup);
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });
    compiler.builder.emit(Instruction::Iconst_0);
    compiler.builder.frame.push_type(VerificationType::Integer);
    compiler.builder.emit(Instruction::Aload(value_slot as u8));
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });
    compiler.builder.emit(Instruction::Aastore);
    compiler.builder.frame.pop_type(); // pop value
    compiler.builder.frame.pop_type(); // pop index
    compiler.builder.frame.pop_type(); // pop array ref (dup)

    // dup; iconst_1; aload display; aastore
    compiler.builder.emit(Instruction::Dup);
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });
    compiler.builder.emit(Instruction::Iconst_1);
    compiler.builder.frame.push_type(VerificationType::Integer);
    compiler.builder.emit(Instruction::Aload(display_slot as u8));
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });
    compiler.builder.emit(Instruction::Aastore);
    compiler.builder.frame.pop_type(); // pop value
    compiler.builder.frame.pop_type(); // pop index
    compiler.builder.frame.pop_type(); // pop array ref (dup)

    // Stack now has: [Object[] array]
    Ok(())
}

/// Emit bytecode to create Object[2] = [value, null] and leave it on the stack.
fn emit_result_array_with_null(
    compiler: &mut Compiler<'_>,
    value_slot: u16,
) -> Result<(), CodegenError> {
    let object_class = compiler.builder.refs.object_class;

    // iconst_2; anewarray Object
    compiler.builder.emit(Instruction::Iconst_2);
    compiler.builder.frame.push_type(VerificationType::Integer);
    compiler.builder.emit(Instruction::Anewarray(object_class));
    compiler.builder.frame.pop_type(); // pop int
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });

    // dup; iconst_0; aload value; aastore
    compiler.builder.emit(Instruction::Dup);
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });
    compiler.builder.emit(Instruction::Iconst_0);
    compiler.builder.frame.push_type(VerificationType::Integer);
    compiler.builder.emit(Instruction::Aload(value_slot as u8));
    compiler.builder.frame.push_type(VerificationType::Object {
        cpool_index: object_class,
    });
    compiler.builder.emit(Instruction::Aastore);
    compiler.builder.frame.pop_type(); // pop value
    compiler.builder.frame.pop_type(); // pop index
    compiler.builder.frame.pop_type(); // pop array ref (dup)

    // index 1 stays null (default for Object arrays)
    // Stack now has: [Object[] array]
    Ok(())
}
