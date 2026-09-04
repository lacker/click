use super::*;

#[test]
fn c0_small_volatile_model_preserves_metadata_and_access_facts() {
    let functions = syntax::parse_functions(
        r#"
        volatile int32 global_value = 3;

        int32 read_twice(volatile int32 value) {
            return value + value;
        }

        int32 read_global() {
            return global_value + global_value;
        }

        int32 read_static() {
            static volatile int32 calls = 5;
            return calls;
        }
        "#,
    )
    .expect("scalar volatile objects should parse");

    let global = &functions[0].globals()["global_value"];
    assert!(global.is_volatile());
    assert!(functions[0].to_kernel_function().global_variables()[0].is_volatile());

    let read_twice = &functions[0];
    assert!(read_twice.parameters()[0].is_volatile());
    let kernel = read_twice.to_kernel_function();
    assert!(kernel.parameters()[0].is_volatile());
    let volatile_read_names = |execution: &crate::kernel::SymbolicCExecution| {
        execution.paths()[0]
            .facts()
            .iter()
            .filter_map(|fact| match fact.proposition() {
                crate::kernel::Proposition::Predicate { name, .. }
                    if name.starts_with("__click_volatile_read_") =>
                {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    let execution = crate::kernel::prove_symbolic_c_function_execution_paths(
        crate::kernel::CState::new(),
        kernel,
        vec![crate::kernel::c_int32_literal(7)],
        crate::kernel::PureFactContext::new(),
    );
    assert_eq!(execution.paths().len(), 1);
    let accesses = volatile_read_names(&execution);
    assert_eq!(accesses.len(), 2);
    assert_ne!(accesses[0], accesses[1]);

    let global_execution = crate::kernel::prove_symbolic_c_function_execution_paths(
        crate::kernel::CState::new(),
        functions[1].to_kernel_function(),
        Vec::new(),
        crate::kernel::PureFactContext::new(),
    );
    assert_eq!(global_execution.paths().len(), 1);
    assert_eq!(volatile_read_names(&global_execution).len(), 2);

    let static_function = &functions[2];
    assert!(
        static_function
            .static_locals()
            .values()
            .next()
            .expect("volatile static local metadata")
            .is_volatile()
    );
    assert!(static_function.to_kernel_function().static_variables()[0].is_volatile());
    let static_execution = crate::kernel::prove_symbolic_c_function_execution_paths(
        crate::kernel::CState::new(),
        static_function.to_kernel_function(),
        Vec::new(),
        crate::kernel::PureFactContext::new(),
    );
    assert_eq!(static_execution.paths().len(), 1);
    assert_eq!(volatile_read_names(&static_execution).len(), 1);
}

#[test]
fn c0_small_volatile_model_rejects_unsupported_pointer_depth() {
    for (source, expected) in [
        (
            r#"
            int32 array() {
                volatile int32 values[2];
                return 0;
            }
            "#,
            "does not support volatile arrays",
        ),
        (
            r#"
            int32 pointer() {
                volatile int32 **value;
                return 0;
            }
            "#,
            "supports scalar objects and pointers to scalar objects",
        ),
        (
            r#"
            struct record {
                volatile int32 value;
            };
            int32 field() {
                return 0;
            }
            "#,
            "volatile struct or union fields",
        ),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unsupported volatile shapes must remain rejected");
        assert!(error.message().contains(expected), "{}", error.message());
    }
}

#[test]
fn c0_pointer_volatile_accesses_preserve_pointee_metadata_and_order() {
    let functions = syntax::parse_functions(
        r#"
        int32 pointer_access() {
            volatile int32 value = 4;
            volatile int32 *pointer = &value;
            *pointer = *pointer + 1;
            return value;
        }

        int32 pointer_parameter(volatile int32 *pointer) {
            return *pointer;
        }
        "#,
    )
    .expect("pointer-qualified volatile scalars should parse");

    let pointer_parameter = &functions[1].parameters()[0];
    assert!(!pointer_parameter.is_volatile());
    assert!(pointer_parameter.pointee_is_volatile());
    let kernel_parameter = functions[1].to_kernel_function().parameters()[0].clone();
    assert!(!kernel_parameter.is_volatile());
    assert!(kernel_parameter.pointee_is_volatile());

    let execution = crate::kernel::prove_symbolic_c_function_execution_paths(
        crate::kernel::CState::new(),
        functions[0].to_kernel_function(),
        Vec::new(),
        crate::kernel::PureFactContext::new(),
    );
    assert_eq!(execution.paths().len(), 1);
    let accesses = execution.paths()[0]
        .facts()
        .iter()
        .filter_map(|fact| match fact.proposition() {
            crate::kernel::Proposition::Predicate { name, .. }
                if name.starts_with("__click_volatile_") =>
            {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(accesses.len(), 4);
    assert!(accesses[0].starts_with("__click_volatile_write_"));
    assert!(accesses[1].starts_with("__click_volatile_read_"));
    assert!(accesses[2].starts_with("__click_volatile_write_"));
    assert!(accesses[3].starts_with("__click_volatile_read_"));
}

#[test]
fn c0_collects_scalar_file_scope_globals() {
    let functions = syntax::parse_functions(
        r#"
        int32 counter = 3;
        uint16 zero;
        int32 read_counter() {
            return counter;
        }
        int32 increment_counter() {
            counter = counter + 1;
            return counter;
        }
        "#,
    )
    .expect("scalar globals should parse");

    assert_eq!(functions[0].globals().len(), 2);
    let global = &functions[0].globals()["counter"];
    assert!(global.is_defined());
    assert_eq!(global.c_type(), syntax::C0Type::Int32);
    assert_eq!(
        functions[1].to_kernel_function().global_variables()[0].initial_value(),
        &crate::kernel::int32(3)
    );
    assert_eq!(
        functions[0].to_kernel_function().global_variables()[1].initial_value(),
        &crate::kernel::uint16(0)
    );
}

#[test]
fn c0_collects_file_scope_scalar_arrays() {
    let functions = syntax::parse_functions(
        r#"
        int32 table[3] = {1, 2};
        uint8 bytes[2];
        int32 read_table() {
            return table[1];
        }
        "#,
    )
    .expect("file-scope scalar arrays should parse");

    assert_eq!(functions[0].global_arrays().len(), 2);
    let table = &functions[0].global_arrays()["table"];
    assert_eq!(table.element_type(), syntax::C0Type::Int32);
    assert_eq!(table.length(), 3);
    assert_eq!(
        table.initializer(),
        Some(
            [
                syntax::C0Expression::Int32Literal(1),
                syntax::C0Expression::Int32Literal(2),
                syntax::C0Expression::Int32Literal(0),
            ]
            .as_slice()
        )
    );
    let kernel_function = functions[0].to_kernel_function();
    let kernel_table = kernel_function
        .global_arrays()
        .iter()
        .find(|array| array.name() == "table")
        .expect("kernel table metadata");
    assert_eq!(kernel_table.name(), "table");
    assert_eq!(kernel_table.element_type(), crate::kernel::CType::Int32);
    assert_eq!(kernel_table.length(), 3);
    assert_eq!(
        kernel_table.initial_values(),
        &[
            crate::kernel::int32(1),
            crate::kernel::int32(2),
            crate::kernel::int32(0)
        ]
    );
}

#[test]
fn c0_collects_file_scope_struct_aggregates() {
    let functions = syntax::parse_functions(
        r#"
        struct state {
            int32 value;
            uint8 ready;
        };

        struct state shared;

        int32 read_shared() {
            return shared.value;
        }
        "#,
    )
    .expect("file-scope struct aggregates should parse");

    let function = functions
        .iter()
        .find(|function| function.name() == "read_shared")
        .expect("reader function");
    let aggregate = &function.global_aggregates()["shared"];
    assert!(aggregate.is_defined());
    assert!(!aggregate.is_file_static());
    assert_eq!(aggregate.name(), "shared");
    assert_eq!(aggregate.struct_name(), "state");
    assert_eq!(aggregate.layout().field("value").unwrap().offset_bytes(), 0);
    assert_eq!(aggregate.layout().field("ready").unwrap().offset_bytes(), 4);

    let kernel_function = function.to_kernel_function();
    let kernel_aggregate = kernel_function
        .global_aggregates()
        .iter()
        .find(|aggregate| aggregate.source_name() == "shared")
        .expect("kernel aggregate metadata");
    assert_eq!(kernel_aggregate.kernel_name(), "shared");
    assert_eq!(
        kernel_aggregate.layout().size_bytes(),
        aggregate.layout().size_bytes()
    );
    assert_eq!(kernel_aggregate.layout().fields().len(), 2);
}

#[test]
fn c0_collects_static_struct_aggregates_with_stable_kernel_names() {
    let functions = syntax::parse_functions(
        r#"
        struct state {
            int32 value;
        };

        int32 increment() {
            static struct state state;
            state.value = state.value + 1;
            return state.value;
        }
        "#,
    )
    .expect("function-local struct statics should parse");

    let function = &functions[0];
    let aggregate = function
        .static_aggregates()
        .values()
        .next()
        .expect("static aggregate metadata");
    assert_eq!(aggregate.name(), "state");
    assert_eq!(aggregate.struct_name(), "state");
    assert_ne!(aggregate.kernel_name(), aggregate.name());

    let kernel_function = function.to_kernel_function();
    let kernel_aggregate = kernel_function
        .static_aggregates()
        .iter()
        .next()
        .expect("kernel static aggregate metadata");
    assert_eq!(kernel_aggregate.source_name(), "state");
    assert_eq!(kernel_aggregate.kernel_name(), aggregate.kernel_name());
    assert_eq!(kernel_aggregate.layout().fields().len(), 1);
}

#[test]
fn c0_collects_aggregate_static_initializers() {
    let functions = syntax::parse_functions(
        r#"
        struct state {
            int32 value;
            uint8 ready;
        };

        struct state shared = {7, 1};

        int32 read() {
            static struct state local = {3};
            return shared.value + shared.ready + local.value + local.ready;
        }
        "#,
    )
    .expect("aggregate static initializers should parse");

    let function = &functions[0];
    let global = &function.global_aggregates()["shared"];
    let global_initializers = global.initializer().expect("global initializer");
    assert_eq!(global_initializers.len(), 2);
    assert_eq!(global_initializers[0].offset_bytes(), 0);
    assert_eq!(global_initializers[0].c_type(), syntax::C0Type::Int32);
    assert!(matches!(
        global_initializers[0].value(),
        syntax::C0Expression::Int32Literal(7)
    ));
    assert_eq!(global_initializers[1].offset_bytes(), 4);
    assert!(matches!(
        global_initializers[1].value(),
        syntax::C0Expression::Int32Literal(1)
    ));

    let static_aggregate = function
        .static_aggregates()
        .values()
        .next()
        .expect("static aggregate initializer");
    assert_eq!(static_aggregate.initializer().len(), 1);
    assert_eq!(static_aggregate.initializer()[0].offset_bytes(), 0);
    assert!(matches!(
        static_aggregate.initializer()[0].value(),
        syntax::C0Expression::Int32Literal(3)
    ));

    let kernel_function = function.to_kernel_function();
    let kernel_global = kernel_function
        .global_aggregates()
        .iter()
        .next()
        .expect("kernel global aggregate initializer");
    assert_eq!(kernel_global.initializers().len(), 2);
    assert_eq!(kernel_global.initializers()[0].offset_bytes(), 0);
    assert_eq!(kernel_global.initializers()[1].offset_bytes(), 4);
    let kernel_static = kernel_function
        .static_aggregates()
        .iter()
        .next()
        .expect("kernel static aggregate initializer");
    assert_eq!(kernel_static.initializers().len(), 1);
    assert_eq!(kernel_static.initializers()[0].offset_bytes(), 0);
}

#[test]
fn c0_collects_aggregate_arrays() {
    let functions = syntax::parse_functions_for_source(
        r#"
        struct entry {
            int32 value;
            uint8 ready;
        };

        static struct entry private_table[2] = {{4, 1}, {5}};
        struct entry shared_table[2] = {{7, 1}, {3}};

        int32 read() {
            static struct entry local_table[2] = {{2}, {6, 1}};
            return private_table[1].value + shared_table[0].value
                + local_table[1].ready;
        }
        "#,
        "aggregate_arrays.c",
    )
    .expect("aggregate arrays should parse");

    let function = functions
        .iter()
        .find(|function| function.name() == "read")
        .expect("aggregate-array reader function");

    let global = &function.global_aggregate_arrays()["shared_table"];
    assert!(global.is_defined());
    assert!(global.is_file_static() == false);
    assert_eq!(global.length(), 2);
    assert_eq!(global.c_type(), syntax::C0Type::UInt8Array(16));
    let global_initializers = global.initializer().expect("global array initializer");
    assert_eq!(global_initializers.len(), 3);
    assert_eq!(global_initializers[0].offset_bytes(), 0);
    assert_eq!(global_initializers[1].offset_bytes(), 4);
    assert_eq!(global_initializers[2].offset_bytes(), 8);

    let private = &function.global_aggregate_arrays()["private_table"];
    assert!(private.is_file_static());
    assert_ne!(private.kernel_name(), private.name());
    assert_eq!(private.initializer().unwrap().len(), 3);

    let local = function
        .static_aggregate_arrays()
        .values()
        .next()
        .expect("local aggregate array metadata");
    assert_eq!(local.name(), "local_table");
    assert_eq!(local.length(), 2);
    assert_eq!(local.c_type(), syntax::C0Type::UInt8Array(16));
    assert_eq!(local.initializer().len(), 3);

    let kernel_function = function.to_kernel_function();
    let kernel_global = kernel_function
        .global_aggregate_arrays()
        .iter()
        .find(|array| array.source_name() == "shared_table")
        .expect("kernel global aggregate array metadata");
    assert_eq!(kernel_global.kernel_name(), "shared_table");
    assert_eq!(kernel_global.length(), 2);
    assert_eq!(kernel_global.initializers().len(), 3);
    let kernel_local = kernel_function
        .static_aggregate_arrays()
        .iter()
        .next()
        .expect("kernel local aggregate array metadata");
    assert_eq!(kernel_local.source_name(), "local_table");
    assert_eq!(kernel_local.kernel_name(), local.kernel_name());
    assert_eq!(kernel_local.initializers().len(), 3);
}

#[test]
fn c0_rejects_unsupported_aggregate_array_initializers() {
    for (source, expected) in [
        (
            "struct state { int32 value; }; struct state shared[2][2];",
            "multidimensional file-scope arrays",
        ),
        (
            "struct state { int32 value; }; struct state shared[2] = {1};",
            "aggregate array elements require nested",
        ),
        (
            "struct state { int32 value; }; int32 seed; struct state shared = {seed}; int32 f() { return 0; }",
            "aggregate initializers currently support only integer, floating-point, or null-pointer literals",
        ),
    ] {
        let error = syntax::parse_functions(source)
            .expect_err("unsupported aggregate static shapes must remain rejected");
        assert!(error.message().contains(expected), "{}", error.message());
    }
}

#[test]
fn c0_struct_designated_initializers_reject_unsupported_designators() {
    for (source, expected) in [
        (
            "struct state { int32 value; }; int32 f() { struct state state = {[0] = 1}; return 0; }",
            "array designators in struct initializers are not supported",
        ),
        (
            "struct state { int32 value; }; int32 f() { struct state state = {.missing = 1}; return 0; }",
            "struct `state` has no field `missing`",
        ),
        (
            "struct state { int32 value; }; int32 f() { struct state state = {.value.more = 1}; return 0; }",
            "nested field designators require an embedded struct field",
        ),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unsupported struct initializer designators must be rejected");
        assert!(error.message().contains(expected), "{}", error.message());
    }
}

#[test]
fn c0_file_static_arrays_are_qualified_by_translation_unit() {
    let alpha = syntax::parse_functions_for_source(
        "static int32 values[2] = {1, 2}; int32 read_alpha() { return values[0]; }",
        "alpha.c",
    )
    .expect("file-scope static arrays should parse");
    let beta = syntax::parse_functions_for_source(
        "static int32 values[2] = {3, 4}; int32 read_beta() { return values[0]; }",
        "beta.c",
    )
    .expect("file-scope static arrays should parse");

    let alpha_array = &alpha[0].global_arrays()["values"];
    let beta_array = &beta[0].global_arrays()["values"];
    assert!(alpha_array.is_file_static());
    assert!(beta_array.is_file_static());
    assert_ne!(alpha_array.kernel_name(), beta_array.kernel_name());
    assert_ne!(
        alpha[0].to_kernel_function().global_arrays()[0].kernel_name(),
        beta[0].to_kernel_function().global_arrays()[0].kernel_name()
    );
}

#[test]
fn c0_headers_accept_extern_scalar_arrays() {
    syntax::validate_header("extern int32 table[3];")
        .expect("headers should accept extern scalar arrays");
    let error = syntax::validate_header("int32 table[3];")
        .expect_err("headers must keep array definitions in source files");
    assert!(error.message().contains("only with `extern`"));
}

#[test]
fn c0_file_static_globals_are_qualified_by_translation_unit() {
    let alpha = syntax::parse_functions_for_source(
        "static int32 counter = 1; int32 read_alpha() { return counter; }",
        "alpha.c",
    )
    .expect("file-scope static globals should parse");
    let beta = syntax::parse_functions_for_source(
        "static int32 counter = 10; int32 read_beta() { return counter; }",
        "beta.c",
    )
    .expect("file-scope static globals should parse");

    let alpha_global = &alpha[0].globals()["counter"];
    let beta_global = &beta[0].globals()["counter"];
    assert!(alpha_global.is_file_static());
    assert!(beta_global.is_file_static());
    assert_eq!(alpha_global.name(), "counter");
    assert_eq!(beta_global.name(), "counter");
    assert_ne!(alpha_global.kernel_name(), alpha_global.name());
    assert_ne!(beta_global.kernel_name(), beta_global.name());
    assert_ne!(alpha_global.kernel_name(), beta_global.kernel_name());
    assert_eq!(
        alpha[0].to_kernel_function().global_variables()[0].name(),
        "counter"
    );
    assert_ne!(
        alpha[0].to_kernel_function().global_variables()[0].kernel_name(),
        beta[0].to_kernel_function().global_variables()[0].kernel_name()
    );
}

#[test]
fn c0_file_static_struct_aggregates_are_qualified_by_translation_unit() {
    let alpha = syntax::parse_functions_for_source(
        "struct state { int32 value; }; static struct state state; int32 read_alpha() { return state.value; }",
        "alpha.c",
    )
    .expect("file-scope static struct aggregates should parse");
    let beta = syntax::parse_functions_for_source(
        "struct state { int32 value; }; static struct state state; int32 read_beta() { return state.value; }",
        "beta.c",
    )
    .expect("file-scope static struct aggregates should parse");

    let alpha_aggregate = &alpha[0].global_aggregates()["state"];
    let beta_aggregate = &beta[0].global_aggregates()["state"];
    assert!(alpha_aggregate.is_file_static());
    assert!(beta_aggregate.is_file_static());
    assert_ne!(alpha_aggregate.kernel_name(), beta_aggregate.kernel_name());
    assert_ne!(
        alpha[0].to_kernel_function().global_aggregates()[0].kernel_name(),
        beta[0].to_kernel_function().global_aggregates()[0].kernel_name()
    );
}

#[test]
fn c0_headers_accept_extern_scalar_globals_only() {
    syntax::validate_header("extern int32 counter;")
        .expect("headers should accept extern scalar globals");
    let error = syntax::validate_header("int32 counter;")
        .expect_err("headers must keep definitions in source files");
    assert!(error.message().contains("only with `extern`"));
    let error = syntax::validate_header("static int32 counter;")
        .expect_err("headers must not define file-scope static storage");
    assert!(error.message().contains("only with `extern`"));
}

#[test]
fn c0_collects_static_scalar_locals_with_stable_kernel_names() {
    let functions = syntax::parse_functions(
        r#"
        int32 increment() {
            static int32 calls = 5;
            calls = calls + 1;
            return calls;
        }
        "#,
    )
    .expect("scalar static locals should parse");

    let function = &functions[0];
    assert_eq!(function.static_locals().len(), 1);
    let local = function
        .static_locals()
        .values()
        .next()
        .expect("static local metadata");
    assert_eq!(local.name(), "calls");
    assert_ne!(local.kernel_name(), local.name());
    assert_eq!(local.c_type(), syntax::C0Type::Int32);
    assert_eq!(local.initializer(), &syntax::C0Expression::Int32Literal(5));
    assert_eq!(
        function.to_kernel_function().static_variables()[0].initial_value(),
        &crate::kernel::int32(5)
    );
}

#[test]
fn c0_collects_static_scalar_arrays_with_stable_kernel_names() {
    let functions = syntax::parse_functions(
        r#"
        int32 lookup() {
            static int32 values[3] = {5, 7};
            return values[0] + values[1] + values[2];
        }
        "#,
    )
    .expect("static arrays should parse");

    let function = &functions[0];
    assert_eq!(function.static_arrays().len(), 1);
    let array = function
        .static_arrays()
        .values()
        .next()
        .expect("static array metadata");
    assert_eq!(array.name(), "values");
    assert_ne!(array.kernel_name(), array.name());
    assert_eq!(array.element_type(), syntax::C0Type::Int32);
    assert_eq!(array.length(), 3);
    assert_eq!(
        array.initializer(),
        &[
            syntax::C0Expression::Int32Literal(5),
            syntax::C0Expression::Int32Literal(7),
            syntax::C0Expression::Int32Literal(0),
        ]
    );
    let kernel_function = function.to_kernel_function();
    assert_eq!(kernel_function.static_arrays().len(), 1);
    assert_eq!(
        kernel_function.static_arrays()[0].initial_values(),
        &[
            crate::kernel::int32(5),
            crate::kernel::int32(7),
            crate::kernel::int32(0)
        ]
    );
}

#[test]
fn c0_collects_string_literals_with_terminators() {
    let functions = syntax::parse_functions(
        r#"
        uint8* literal() {
            return "ok\n";
        }
        "#,
    )
    .expect("string literals should parse in pointer returns");

    let function = &functions[0];
    assert_eq!(function.string_literals().len(), 1);
    let literal = &function.string_literals()[0];
    assert_eq!(literal.bytes(), b"ok\n\0");
    assert_eq!(
        function.to_kernel_function().string_literals()[0].bytes(),
        b"ok\n\0"
    );
    assert!(matches!(function.body(), syntax::C0Statement::Return(_)));
}

#[test]
fn c0_rejects_unsupported_static_local_shapes() {
    let error = syntax::parse_functions(
        r#"
        int32 invalid() {
            static int32 values[2][2];
            return 0;
        }
        "#,
    )
    .expect_err("multidimensional static arrays should remain outside the slice");
    assert!(
        error
            .message()
            .contains("multidimensional static local arrays")
    );
}

fn memory_range(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::CMemoryRange {
    crate::kernel::CMemoryRange::new(base, start.into(), end.into())
}

fn view_memory_context(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::ResourceContext {
    crate::kernel::ResourceContext::new().unchecked_with_fact(
        crate::kernel::CResourceFact::view_memory(memory_range(base, start, end)),
    )
}

fn own_memory_context(
    base: crate::kernel::Pointer,
    start: impl Into<crate::kernel::Bitvector32Term>,
    end: impl Into<crate::kernel::Bitvector32Term>,
) -> crate::kernel::ResourceContext {
    crate::kernel::ResourceContext::new().unchecked_with_fact(
        crate::kernel::CResourceFact::own_memory(memory_range(base, start, end)),
    )
}

#[test]
fn c0_array_parameter_syntax_lowers_to_pointer_parameter() {
    let function = syntax::parse_function(
        r#"
        int32 first(int32 p[3]) {
            return p[0];
        }
        "#,
    )
    .expect("array parameter should parse");

    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );
    assert_eq!(
        function.to_kernel_function().parameters()[0].c_type(),
        crate::kernel::CType::Int32Pointer
    );
}

#[test]
fn c0_accepts_standard_integer_spellings_and_struct_typedefs() {
    let function = syntax::parse_function(
        r#"
        struct record {
            int value;
            unsigned char tag;
        };
        typedef struct record record_t;
        typedef int32_t index_t;

        int read_record(record_t* record, index_t index) {
            int result;
            uint8_t tag;
            result = record->value + index;
            tag = record->tag;
            return result + tag;
        }
        "#,
    )
    .expect("standard C spellings and typedefs should parse");

    assert_eq!(function.return_type(), syntax::C0Type::Int32);
    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );
    assert_eq!(function.parameters()[0].struct_name(), Some("record"));
    assert_eq!(function.parameters()[1].c_type(), syntax::C0Type::Int32);
    assert_eq!(
        function.structs()["record"].field("tag").unwrap().c_type(),
        syntax::C0Type::UInt8
    );
}

#[test]
fn c0_rejects_unmodeled_standard_integer_widths_and_char() {
    for (source, spelling) in [
        ("char unsupported() { return 0; }", "char"),
        ("signed char unsupported() { return 0; }", "signed char"),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unmodeled standard C types should be rejected");
        assert!(
            error.message().contains(spelling),
            "diagnostic for `{spelling}` did not mention the spelling: {}",
            error.message()
        );
    }
}

#[test]
fn c0_syntax_ignores_line_and_block_comments() {
    let function = syntax::parse_function(
        r#"
        /* the imported source may retain its documentation */
        int32 identity(int32 value) {
            // comments do not become syntax
            return /* including inline comments */ value;
        }
        "#,
    )
    .expect("ordinary C comments should parse");

    assert_eq!(function.name(), "identity");
}

#[test]
fn large_straight_line_block_parses_and_lowers_on_a_small_stack() {
    std::thread::Builder::new()
        .name("large-straight-line-c-block".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut source = String::from("int32 straight(int32 x) {\n");
            for _ in 0..10_000 {
                source.push_str("x = x;\n");
            }
            source.push_str("return x;\n}\n");

            let function = syntax::parse_function(&source)
                .expect("a large straight-line C block should parse");
            let _lowered = function.to_kernel_function();
        })
        .expect("the small-stack C parser thread should start")
        .join()
        .expect("large straight-line parsing and lowering should be stack bounded");
}

#[test]
fn c0_void_functions_accept_return_and_fallthrough() {
    let explicit = syntax::parse_function("void stop() { return; }")
        .expect("a void function may return without a value");
    let fallthrough = syntax::parse_function("void stop() { int32 value = 0; }")
        .expect("a void function may fall through");

    assert_eq!(explicit.return_type(), syntax::C0Type::Void);
    assert_eq!(fallthrough.return_type(), syntax::C0Type::Void);
    assert_eq!(
        explicit.to_kernel_function().return_type(),
        crate::kernel::CType::Void
    );
}

#[test]
fn c0_void_and_nonvoid_returns_do_not_mix() {
    let void_error = syntax::parse_function("void bad() { return 1; }")
        .expect_err("a void function cannot return a value");
    assert_eq!(void_error.message(), "void functions cannot return a value");

    let value_error = syntax::parse_function("int32 bad() { return; }")
        .expect_err("a non-void function must return a value");
    assert_eq!(
        value_error.message(),
        "non-void functions must return a value"
    );
}

#[test]
fn c0_parses_standalone_calls() {
    let function =
        syntax::parse_function("int32 caller(int32 value) { observe(value); return 0; }")
            .expect("a function result may be discarded");

    fn contains_call(statement: &syntax::C0Statement) -> bool {
        match statement {
            syntax::C0Statement::Call { function_name, .. } => function_name == "observe",
            syntax::C0Statement::Seq(first, second) => {
                contains_call(first) || contains_call(second)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => contains_call(then_branch) || contains_call(else_branch),
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                contains_call(body)
            }
            _ => false,
        }
    }

    assert!(contains_call(function.body()));
}

#[test]
fn c0_parses_multiple_definitions_and_forward_prototypes() {
    let functions = syntax::parse_functions(
        r#"
        int32 helper(int32 value);

        int32 caller(int32 value) {
            int32 result;
            result = helper(value);
            return result;
        }

        int32 helper(int32 value) {
            return value + 1;
        }
        "#,
    )
    .expect("one source may contain prototypes and multiple definitions");

    assert_eq!(
        functions
            .iter()
            .map(syntax::C0Function::name)
            .collect::<Vec<_>>(),
        vec!["caller", "helper"]
    );
}

#[test]
fn c0_rejects_conflicting_function_prototypes() {
    let error = syntax::parse_functions(
        r#"
        int32 helper(int32 value);
        uint8 helper(uint8 value);
        int32 helper(int32 value) { return value; }
        "#,
    )
    .expect_err("conflicting function declarations should be rejected");

    assert!(
        error
            .message()
            .contains("conflicting declarations for function `helper`")
    );
}

#[test]
fn c0_headers_accept_declarations_but_reject_function_bodies() {
    syntax::validate_header(
        r#"
        typedef int32 index_t;
        struct pair { index_t value; };
        int32 helper(int32 value);
        extern int32 other(int32 value);
        "#,
    )
    .expect("headers should accept supported declarations and prototypes");

    let error = syntax::validate_header("int32 helper() { return 1; }")
        .expect_err("headers must not contain function definitions");
    assert!(
        error
            .message()
            .contains("function definitions are not allowed in headers")
    );
}

#[test]
fn c0_syntax_reports_unterminated_block_comments() {
    let error = syntax::parse_function("/* never closed")
        .expect_err("an unterminated block comment should be rejected");

    assert_eq!(error.message(), "unterminated block comment");
}

#[test]
fn c0_syntax_errors_carry_source_positions() {
    let error = syntax::parse_function("int32 broken(int32 x) {\n    return x\n}\n")
        .expect_err("a missing semicolon should be rejected");

    assert_eq!(error.message(), "expected `;`, got `}`");
    assert_eq!(
        error.position(),
        Some(crate::source::SourcePosition::new(3, 1))
    );
    assert_eq!(error.to_string(), "line 3, column 1: expected `;`, got `}`");
}

#[test]
fn c0_syntax_positions_point_at_the_offending_token() {
    let error =
        syntax::parse_function("int32 broken() {\n    int32 x;\n    x = $;\n    return x;\n}\n")
            .expect_err("an unexpected character should be rejected");

    assert_eq!(error.message(), "unexpected character `$`");
    assert_eq!(
        error.position(),
        Some(crate::source::SourcePosition::new(3, 9))
    );
}

#[test]
fn c0_call_lowering_diagnostics_preserve_original_call_positions() {
    for (source, expected_message, expected_position) in [
        (
            "int32 caller() {\n    return malloc(1);\n}\n",
            "allocation and deallocation builtins must be used in statement form",
            crate::source::SourcePosition::new(2, 12),
        ),
        (
            "int32 caller() {\n    return left() + right();\n}\n",
            "multiple unsequenced calls in one expression are not supported",
            crate::source::SourcePosition::new(2, 21),
        ),
        (
            "int32 caller() {\n    return ready() && later();\n}\n",
            "calls in the short-circuit right operand are not supported",
            crate::source::SourcePosition::new(2, 23),
        ),
        (
            "int32 caller() {\n    return outer(left(), right());\n}\n",
            "multiple unsequenced calls in one expression are not supported",
            crate::source::SourcePosition::new(2, 26),
        ),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unsupported call lowering should be rejected");

        assert_eq!(error.message(), expected_message);
        assert_eq!(error.position(), Some(expected_position));
        assert_eq!(
            error.to_string(),
            format!("{expected_position}: {expected_message}")
        );
    }
}

#[test]
fn c0_syntax_lowers_scalar_declaration_initializers_in_source_order() {
    let function = syntax::parse_function(
        r#"
        int32 initialized() {
            int32 value = 7;
            return value;
        }
        "#,
    )
    .expect("a scalar declaration initializer should parse");

    assert!(matches!(
        function.body(),
        syntax::C0Statement::Seq(first, _)
            if matches!(
                first.as_ref(),
                syntax::C0Statement::Seq(declaration, assignment)
                    if matches!(
                        declaration.as_ref(),
                        syntax::C0Statement::Declare {
                            c_type: syntax::C0Type::Int32,
                            name,
                            ..
                        } if name == "value"
                    )
                    && matches!(
                        assignment.as_ref(),
                        syntax::C0Statement::Assign {
                            name,
                            expression: syntax::C0Expression::Int32Literal(7)
                        } if name == "value"
                    )
            )
    ));
}

#[test]
fn c0_syntax_accepts_declaration_initializer_in_for_loop() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 total = 0;
            for (int32 i = 0; i < 3; i++) {
                total += 1;
            }
            return total;
        }
        "#,
    )
    .expect("a scalar for-loop declaration initializer should parse");
}

#[test]
fn c0_syntax_accepts_continue_in_for_loop() {
    let function = syntax::parse_function(
        r#"
        int32 count() {
            int32 total = 0;
            for (int32 i = 0; i < 3; i++) {
                if (i == 1) {
                    continue;
                }
                total = total + 1;
            }
            return total;
        }
        "#,
    )
    .expect("continue should parse in a for loop");

    fn contains_for(statement: &syntax::C0Statement) -> bool {
        match statement {
            syntax::C0Statement::For { .. } => true,
            syntax::C0Statement::Seq(first, second) => contains_for(first) || contains_for(second),
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => contains_for(then_branch) || contains_for(else_branch),
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                contains_for(body)
            }
            syntax::C0Statement::Switch { cases, .. } => {
                cases.iter().any(|case| contains_for(case.body()))
            }
            _ => false,
        }
    }

    assert!(contains_for(function.body()));
}

#[test]
fn c0_syntax_accepts_a_comma_separated_for_step() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            int32 j = 3;
            for (i = 0; i < 3; i++, j--) {
                j = j + 1;
            }
            return j;
        }
        "#,
    )
    .expect("a for-loop step may sequence scalar updates with commas");
}

#[test]
fn c0_syntax_accepts_omitted_for_initializer_and_step() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            for (; i < 3;) {
                i++;
            }
            return i;
        }
        "#,
    )
    .expect("a for loop may omit its initializer and step");
}

#[test]
fn c0_syntax_accepts_unary_plus_and_a_for_initializer_list() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i;
            int32 j;
            for (i = +0, j = +3; i < 3; i++) {
                j = j + 1;
            }
            return j;
        }
        "#,
    )
    .expect("unary plus and comma-separated scalar for initializers should parse");
}

#[test]
fn c0_syntax_accepts_multiple_declarations_in_a_for_initializer() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 total = 0;
            for (int32 i = 0, j = 3; i < 3; i++, j--) {
                total = total + j;
            }
            return total;
        }
        "#,
    )
    .expect("a for-loop initializer may declare multiple initialized scalars");
}

#[test]
fn c0_syntax_accepts_a_do_while_loop_with_an_unbraced_body() {
    let function = syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            do
                i++;
            while (i < 3);
            return i;
        }
        "#,
    )
    .expect("a do-while loop may control one statement without braces");

    fn contains_do_while(statement: &syntax::C0Statement) -> bool {
        match statement {
            syntax::C0Statement::DoWhile { .. } => true,
            syntax::C0Statement::Seq(first, second) => {
                contains_do_while(first) || contains_do_while(second)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => contains_do_while(then_branch) || contains_do_while(else_branch),
            syntax::C0Statement::While { body, .. } => contains_do_while(body),
            syntax::C0Statement::Switch { cases, .. } => {
                cases.iter().any(|case| contains_do_while(case.body()))
            }
            _ => false,
        }
    }

    assert!(contains_do_while(function.body()));
}

#[test]
fn c0_syntax_accepts_break_and_continue_in_while_bodies() {
    let function = syntax::parse_function(
        r#"
        int32 control() {
            int32 i = 0;
            while (i < 4) {
                i++;
                if (i == 1) {
                    continue;
                }
                if (i == 3) {
                    break;
                }
            }
            return i;
        }
        "#,
    )
    .expect("break and continue should parse in a while body");

    fn count_controls(statement: &syntax::C0Statement) -> (usize, usize) {
        match statement {
            syntax::C0Statement::Break => (1, 0),
            syntax::C0Statement::Continue => (0, 1),
            syntax::C0Statement::Seq(first, second) => {
                let (breaks, continues) = count_controls(first);
                let (more_breaks, more_continues) = count_controls(second);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let (breaks, continues) = count_controls(then_branch);
                let (more_breaks, more_continues) = count_controls(else_branch);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                count_controls(body)
            }
            syntax::C0Statement::Switch { cases, .. } => {
                cases.iter().map(|case| count_controls(case.body())).fold(
                    (0, 0),
                    |(breaks, continues), (more_breaks, more_continues)| {
                        (breaks + more_breaks, continues + more_continues)
                    },
                )
            }
            _ => (0, 0),
        }
    }

    assert_eq!(count_controls(function.body()), (1, 1));
}

#[test]
fn c0_syntax_accepts_break_and_continue_in_do_while_bodies() {
    let function = syntax::parse_function(
        r#"
        int32 control() {
            int32 i = 0;
            do {
                i++;
                if (i == 1) {
                    continue;
                }
                break;
            } while (i < 4);
            return i;
        }
        "#,
    )
    .expect("break and continue should parse in a do-while body");

    fn count_controls(statement: &syntax::C0Statement) -> (usize, usize) {
        match statement {
            syntax::C0Statement::Break => (1, 0),
            syntax::C0Statement::Continue => (0, 1),
            syntax::C0Statement::Seq(first, second) => {
                let (breaks, continues) = count_controls(first);
                let (more_breaks, more_continues) = count_controls(second);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let (breaks, continues) = count_controls(then_branch);
                let (more_breaks, more_continues) = count_controls(else_branch);
                (breaks + more_breaks, continues + more_continues)
            }
            syntax::C0Statement::DoWhile { body, .. } => count_controls(body),
            _ => (0, 0),
        }
    }

    assert_eq!(count_controls(function.body()), (1, 1));
}

#[test]
fn c0_syntax_accepts_switch_cases_and_nested_loop_control() {
    let function = syntax::parse_function(
        r#"
        int32 choose(int32 kind) {
            int32 result = 0;
            while (kind < 2) {
                switch (kind) {
                    case 0:
                        result = 1;
                    case '1':
                        result = 2;
                        continue;
                    default:
                        result = 3;
                        break;
                }
                break;
            }
            return result;
        }
        "#,
    )
    .expect("switch cases should parse inside a while body");

    fn find_switch(statement: &syntax::C0Statement) -> Option<&syntax::C0Statement> {
        match statement {
            syntax::C0Statement::Switch { .. } => Some(statement),
            syntax::C0Statement::Seq(first, second) => {
                find_switch(first).or_else(|| find_switch(second))
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => find_switch(then_branch).or_else(|| find_switch(else_branch)),
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                find_switch(body)
            }
            _ => None,
        }
    }

    let Some(syntax::C0Statement::Switch { expression, cases }) = find_switch(function.body())
    else {
        panic!("expected native switch statement");
    };
    assert!(matches!(expression, syntax::C0Expression::Variable(name) if name == "kind"));
    assert_eq!(cases.len(), 3);
    assert_eq!(cases[0].value(), Some(0));
    assert_eq!(cases[1].value(), Some(u32::from(b'1')));
    assert_eq!(cases[2].value(), None);
}

#[test]
fn c0_syntax_rejects_unsupported_switch_shapes() {
    for (source, expected) in [
        (
            "int32 bad(int32 kind) { switch (kind) { case 1: break; case 1: break; } return 0; }",
            "duplicate `case` label",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) { default: break; default: break; } return 0; }",
            "only one `default`",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) { case kind: break; } return 0; }",
            "integer or character literal",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) { kind = 1; case 0: break; } return 0; }",
            "must begin with a `case` or `default` label",
        ),
        (
            "int32 bad(int32 kind) { switch (kind) {} return 0; }",
            "must contain a `case` or `default` label",
        ),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unsupported switch shape should be rejected");
        assert!(
            error.message().contains(expected),
            "diagnostic did not contain `{expected}`: {}",
            error.message()
        );
    }
}

#[test]
fn c0_syntax_rejects_loop_control_outside_its_supported_loop() {
    for (source, expected) in [
        (
            "int32 bad() { break; return 0; }",
            "`break` must be inside a loop or switch",
        ),
        (
            "int32 bad() { continue; return 0; }",
            "`continue` must be inside a loop",
        ),
    ] {
        let error = syntax::parse_function(source)
            .expect_err("unsupported loop-control placement should be rejected");
        assert!(
            error.message().contains(expected),
            "diagnostic did not contain `{expected}`: {}",
            error.message()
        );
    }
}

#[test]
fn c0_syntax_accepts_prefix_scalar_updates() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0;
            ++i;
            --i;
            for (; i < 3; ++i) {
            }
            return i;
        }
        "#,
    )
    .expect("prefix scalar updates should parse as standalone statements and for steps");
}

#[test]
fn c0_syntax_accepts_a_local_declaration_list() {
    syntax::parse_function(
        r#"
        int32 count() {
            int32 i = 0, j = 1, k = 2;
            return i + j + k;
        }
        "#,
    )
    .expect("a local declaration may contain multiple initialized declarators");
}

#[test]
fn c0_syntax_accepts_a_struct_field_declaration_list() {
    syntax::parse_function(
        r#"
        struct pair {
            int32 first, second;
            uint8 low, high;
        };

        int32 sum_pair(struct pair* value) {
            return value->first + value->second;
        }
        "#,
    )
    .expect("a struct declaration may contain multiple fields");
}

#[test]
fn c0_syntax_accepts_the_remaining_scalar_compound_assignments() {
    syntax::parse_function(
        r#"
        int32 updates() {
            int32 value = 255;
            value /= 3;
            value %= 10;
            value <<= 1;
            value >>= 1;
            value &= 3;
            value |= 4;
            return value;
        }
        "#,
    )
    .expect("scalar compound arithmetic, shift, and bitwise updates should parse");
}

#[test]
fn c0_syntax_accepts_memory_lvalue_updates() {
    let function = syntax::parse_function(
        r#"
        struct counter {
            int32 count;
        };

        int32 updates(int32 values[], struct counter* counter) {
            values[0] += 1;
            ++counter->count;
            counter->count--;
            return values[0] + counter->count;
        }
        "#,
    )
    .expect("indexed and field compound updates should parse");

    fn update_targets<'a>(
        statement: &'a syntax::C0Statement,
        targets: &mut Vec<&'a syntax::C0Expression>,
    ) {
        match statement {
            syntax::C0Statement::Update { target, .. } => targets.push(target),
            syntax::C0Statement::Seq(first, second) => {
                update_targets(first, targets);
                update_targets(second, targets);
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                update_targets(then_branch, targets);
                update_targets(else_branch, targets);
            }
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                update_targets(body, targets)
            }
            _ => {}
        }
    }

    let mut targets = Vec::new();
    update_targets(function.body(), &mut targets);
    assert_eq!(targets.len(), 3);
    assert!(matches!(targets[0], syntax::C0Expression::Index(_, _)));
    assert!(matches!(
        targets[1],
        syntax::C0Expression::Field {
            field_type: syntax::C0Type::Int32,
            ..
        }
    ));
    assert!(matches!(
        targets[2],
        syntax::C0Expression::Field {
            field_type: syntax::C0Type::Int32,
            ..
        }
    ));
}

#[test]
fn c0_syntax_accepts_scalar_casts_and_conditional_expressions() {
    let function = syntax::parse_function(
        r#"
        int32 choose(int32 condition, uint8 left, int32 right) {
            return condition ? (int32) left : right + 1;
        }
        "#,
    )
    .expect("scalar casts and conditional expressions should parse");

    assert!(matches!(
        function.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Conditional {
            condition,
            then_branch,
            else_branch,
        }) if matches!(condition.as_ref(), syntax::C0Expression::Variable(name) if name == "condition")
            && matches!(
                then_branch.as_ref(),
                syntax::C0Expression::Cast {
                    c_type: syntax::C0Type::Int32,
                    expression,
                } if matches!(expression.as_ref(), syntax::C0Expression::Variable(name) if name == "left")
            )
            && matches!(
                else_branch.as_ref(),
                syntax::C0Expression::Add(left, right)
                    if matches!(left.as_ref(), syntax::C0Expression::Variable(name) if name == "right")
                        && matches!(right.as_ref(), syntax::C0Expression::Int32Literal(1))
            )
    ));
}

#[test]
fn c0_syntax_rejects_non_scalar_casts() {
    let error = syntax::parse_function(
        r#"
        int32 bad(int32* value) {
            return (int32*) value;
        }
        "#,
    )
    .expect_err("pointer casts are outside the scalar cast subset");
    assert!(error.message().contains("scalar integer values"));
}

#[test]
fn c0_syntax_rejects_overlong_local_array_initializers() {
    let error = syntax::parse_function(
        r#"
        int32 unsupported() {
            int32 values[2] = {1, 2, 3};
            return 0;
        }
        "#,
    )
    .expect_err("an array initializer cannot exceed the declared length");

    assert_eq!(error.message(), "too many initializers for `values[2]`");
}

#[test]
fn c0_syntax_models_missing_else_and_empty_statements_as_skip() {
    let function = syntax::parse_function(
        r#"
        int32 nonnegative(int32 value) {
            ;
            if (value < 0) {
                return 0;
            }
            if (value == 0) {
            }
            return value;
        }
        "#,
    )
    .expect("if statements should not require artificial else branches");

    fn contains_skip(statement: &syntax::C0Statement) -> bool {
        match statement {
            syntax::C0Statement::Skip => true,
            syntax::C0Statement::Seq(first, second) => {
                contains_skip(first) || contains_skip(second)
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => contains_skip(then_branch) || contains_skip(else_branch),
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                contains_skip(body)
            }
            syntax::C0Statement::For {
                initializer,
                body,
                step,
                ..
            } => contains_skip(initializer) || contains_skip(body) || contains_skip(step),
            syntax::C0Statement::Switch { cases, .. } => {
                cases.iter().any(|case| contains_skip(case.body()))
            }
            syntax::C0Statement::Break
            | syntax::C0Statement::Continue
            | syntax::C0Statement::Declare { .. }
            | syntax::C0Statement::DeclareStructValue { .. }
            | syntax::C0Statement::Assign { .. }
            | syntax::C0Statement::Call { .. }
            | syntax::C0Statement::CallAssign { .. }
            | syntax::C0Statement::HeapAllocate { .. }
            | syntax::C0Statement::HeapFree { .. }
            | syntax::C0Statement::Return(_)
            | syntax::C0Statement::Store { .. }
            | syntax::C0Statement::Update { .. } => false,
        }
    }

    assert!(contains_skip(function.body()));
}

#[test]
fn kernel_skip_preserves_state_without_facts_or_obligations() {
    let state = crate::kernel::CState::new();
    let theorem = crate::kernel::prove_symbolic_c_execution(
        state.clone(),
        crate::kernel::c_skip(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("skip should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: state.clone(),
            statement: crate::kernel::c_skip(),
            outcome: crate::kernel::CStatementOutcome::Normal(state),
        }
    );
}

#[test]
fn c0_syntax_parses_negative_literals_and_unary_minus() {
    let literal = syntax::parse_function(
        r#"
        int32 negative_one() {
            return -1;
        }
        "#,
    )
    .expect("negative literals should parse");
    assert!(matches!(
        literal.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Int32Literal(value))
            if *value == (-1i32) as u32
    ));

    let minimum = syntax::parse_function(
        r#"
        int32 minimum() {
            return -2147483648;
        }
        "#,
    )
    .expect("the minimum int32 literal should parse");
    assert!(matches!(
        minimum.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Int32Literal(0x8000_0000))
    ));

    let negation = syntax::parse_function(
        r#"
        int32 negate(int32 value) {
            return -value;
        }
        "#,
    )
    .expect("general unary minus should parse");
    assert!(matches!(
        negation.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Subtract(left, right))
            if matches!(
                left.as_ref(),
                syntax::C0Expression::Int32Literal(0)
            ) && matches!(
                right.as_ref(),
                syntax::C0Expression::Variable(name) if name == "value"
            )
    ));
}

#[test]
fn c0_syntax_parses_c_integer_literal_radices_and_suffixes() {
    let literals = syntax::parse_function(
        r#"
        int32 literals() {
            return 0x0Fu | 010U;
        }
        "#,
    )
    .expect("C integer literal radices and suffixes should parse");
    assert!(matches!(
        literals.body(),
        syntax::C0Statement::Return(syntax::C0Expression::BitwiseOr(left, right))
            if matches!(left.as_ref(), syntax::C0Expression::UInt32Literal(15))
                && matches!(right.as_ref(), syntax::C0Expression::UInt32Literal(8))
    ));

    let minimum = syntax::parse_function(
        r#"
        int32 minimum() {
            return -0x80000000L;
        }
        "#,
    )
    .expect("negative hexadecimal literals should preserve int32 minimum");
    assert!(matches!(
        minimum.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Int64Literal(-0x8000_0000))
    ));
}

#[test]
fn c0_syntax_rejects_invalid_octal_literals() {
    let error = syntax::parse_function(
        r#"
        int32 invalid() {
            return 08;
        }
        "#,
    )
    .expect_err("digits outside the octal range must not silently become decimal");
    assert!(
        error.message().contains("octal literal"),
        "{}",
        error.message()
    );
}

#[test]
fn c0_unary_minus_preserves_signed_overflow_semantics() {
    let function = syntax::parse_function(
        r#"
        int32 negate(int32 value) {
            return -value;
        }
        "#,
    )
    .expect("unary minus function should parse");
    let state = crate::kernel::CState::new().with_local(
        "value",
        crate::kernel::int32(crate::kernel::Bitvector32Term::Constant(0x8000_0000)),
    );
    let theorem = crate::kernel::prove_symbolic_c_execution(
        state.clone(),
        function.body_kernel_statement(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("concrete signed overflow should have an execution theorem");
    let mut proposition = theorem.proposition();
    while let crate::kernel::Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        crate::kernel::Proposition::CStatementExecutes {
            outcome: crate::kernel::CStatementOutcome::UndefinedBehavior(
                crate::kernel::CUndefinedBehavior::SignedOverflow
            ),
            ..
        }
    ));
}

#[test]
fn c0_syntax_retains_struct_pointee_types_across_chained_fields() {
    let function = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };
        struct node {
            struct leaf* child;
        };

        int32 read_nested(struct node* root) {
            return root->child->value;
        }
        "#,
    )
    .expect("chained struct-pointer fields should parse");

    let child = function
        .structs()
        .get("node")
        .and_then(|layout| layout.field("child"))
        .expect("node child field");
    assert_eq!(child.struct_name(), Some("leaf"));

    let syntax::C0Statement::Return(syntax::C0Expression::Field {
        pointer,
        field_type: syntax::C0Type::Int32,
        field_struct_name: None,
        ..
    }) = function.body()
    else {
        panic!("the terminal scalar field should retain its resolved type")
    };
    assert!(matches!(
        pointer.as_ref(),
        syntax::C0Expression::Field {
            field_type: syntax::C0Type::Int32Pointer,
            field_struct_name: Some(name),
            ..
        } if name == "leaf"
    ));
}

#[test]
fn c0_struct_layout_preserves_embedded_struct_shape() {
    #[repr(C)]
    struct HostInner {
        flag: u8,
        value: i32,
    }
    #[repr(C)]
    struct HostOuter {
        tag: u8,
        inner: HostInner,
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            uint8 flag;
            int32 value;
        };
        struct outer {
            uint8 tag;
            struct inner inner;
            int32 tail;
        };

        int32 read_nested(struct outer* packet) {
            return packet->inner.value;
        }
        "#,
    )
    .expect("embedded struct fields should parse");
    let inner = function.structs().get("inner").expect("inner layout");
    let outer = function.structs().get("outer").expect("outer layout");

    assert_eq!(
        inner.size_bytes() as usize,
        std::mem::size_of::<HostInner>()
    );
    assert_eq!(
        inner.alignment_bytes() as usize,
        std::mem::align_of::<HostInner>()
    );
    assert_eq!(outer.field("tag").unwrap().offset_bytes() as usize, 0);
    assert_eq!(
        outer.field("inner").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, inner)
    );
    assert_eq!(outer.field("inner").unwrap().struct_name(), Some("inner"));
    assert_eq!(
        outer.field("inner").unwrap().byte_width() as usize,
        std::mem::size_of::<HostInner>()
    );
    assert_eq!(
        outer.field("tail").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, tail)
    );
    assert_eq!(
        outer.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
    assert_eq!(
        outer.alignment_bytes() as usize,
        std::mem::align_of::<HostOuter>()
    );
}

#[test]
fn c0_embedded_struct_field_access_lowers_to_nested_scalar_offset() {
    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
        };
        struct outer {
            uint8 tag;
            struct inner inner;
        };

        int32 write_nested(struct outer* packet) {
            packet->inner.value = 7;
            return packet->inner.value;
        }
        "#,
    )
    .expect("nested embedded field access should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 4);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 8))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 8).store(
            crate::kernel::Pointer {
                block: "packet".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(4),
            },
            crate::kernel::int32(7),
        ))
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("nested embedded field access should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_tagged_union_layout_overlaps_members_and_preserves_member_types() {
    #[repr(C)]
    union HostPayload {
        number: i32,
        pointer: *mut i32,
    }
    #[repr(C)]
    struct HostPacket {
        tag: i32,
        payload: HostPayload,
        tail: u8,
    }

    let function = syntax::parse_function(
        r#"
        union payload {
            int32 number;
            int32* pointer;
        };
        struct packet {
            int32 tag;
            union payload payload;
            uint8 tail;
        };

        int32 read_number(struct packet* packet) {
            return packet->payload.number;
        }
        "#,
    )
    .expect("named tagged union members should parse");

    let union = function.unions().get("payload").expect("union metadata");
    assert_eq!(
        union.size_bytes() as usize,
        std::mem::size_of::<HostPayload>()
    );
    assert_eq!(
        union.alignment_bytes() as usize,
        std::mem::align_of::<HostPayload>()
    );
    assert_eq!(union.field("number").unwrap().offset_bytes(), 0);
    assert_eq!(union.field("pointer").unwrap().offset_bytes(), 0);
    assert_eq!(
        union.field("pointer").unwrap().byte_width(),
        std::mem::size_of::<*mut i32>() as u32
    );

    let packet = function.structs().get("packet").expect("packet metadata");
    assert_eq!(
        packet.field("payload").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, payload)
    );
    assert_eq!(
        packet.field("payload").unwrap().union_name(),
        Some("payload")
    );
    assert_eq!(
        packet.field("tail").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, tail)
    );
    assert_eq!(
        packet.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );

    assert!(matches!(
        function.body(),
        syntax::C0Statement::Return(syntax::C0Expression::UnionField {
            field_type: syntax::C0Type::Int32,
            union_name,
            ..
        }) if union_name == "payload"
    ));
}

#[test]
fn c0_tagged_union_member_writes_are_rejected() {
    let error = syntax::parse_function(
        r#"
        union payload { int32 number; int32* pointer; };
        struct packet { int32 tag; union payload payload; };

        int32 write_number(struct packet* packet) {
            packet->payload.number = 7;
            return 0;
        }
        "#,
    )
    .expect_err("tagged union members are read-only in the first slice");
    assert!(
        error.message().contains("writing tagged union members"),
        "unexpected diagnostic: {}",
        error.message()
    );
}

#[test]
fn c0_tagged_union_values_and_by_value_containers_are_rejected() {
    let value_error = syntax::parse_function(
        r#"
        union payload { int32 number; int32* pointer; };
        struct packet { int32 tag; union payload payload; };

        int32 read_union(struct packet* packet) {
            return packet->payload;
        }
        "#,
    )
    .expect_err("whole tagged union values should not become scalar loads");
    assert!(value_error.message().contains("tagged union values"));

    let copy_error = syntax::parse_function(
        r#"
        union payload { int32 number; int32* pointer; };
        struct packet { int32 tag; union payload payload; };

        struct packet copy(struct packet value) {
            return value;
        }
        "#,
    )
    .expect_err("structs containing unions are not by-value aggregates yet");
    assert!(
        copy_error
            .message()
            .contains("contains a function pointer, an unsupported field shape, or a union field")
    );
}

#[test]
fn c0_rejects_embedded_struct_values_outside_member_access() {
    let error = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
        };
        struct outer {
            struct inner inner;
        };

        int32 invalid(struct outer* packet) {
            return packet->inner;
        }
        "#,
    )
    .expect_err("embedded struct values should not be loaded as scalars");

    assert!(
        error
            .to_string()
            .contains("embedded struct fields are only supported through member access")
    );
}

#[test]
fn c0_struct_aggregate_lvalues_support_load_copy_argument_and_return() {
    let functions = syntax::parse_functions(
        r#"
        struct inner {
            int32 value;
            uint8 flag;
        };
        struct outer {
            uint8 tag;
            struct inner inner;
            int32 tail;
        };

        struct outer clone(struct outer* source) {
            return *source;
        }

        void copy_whole(struct outer* destination, struct outer* source) {
            *destination = *source;
        }

        void copy_inner(struct outer* destination, struct outer* source) {
            destination->inner = source->inner;
        }

        int32 inspect(struct outer value) {
            return value.inner.value + value.inner.flag + value.tail;
        }

        int32 pass_loaded(struct outer* source) {
            return inspect(*source);
        }
        "#,
    )
    .expect("direct aggregate lvalues should parse in copies, arguments, and returns");

    let clone = functions
        .iter()
        .find(|function| function.name() == "clone")
        .expect("clone function");
    assert!(matches!(
        clone.body(),
        syntax::C0Statement::Return(syntax::C0Expression::AggregateAddress {
            struct_name,
            ..
        }) if struct_name == "outer"
    ));
    for name in [
        "clone",
        "copy_whole",
        "copy_inner",
        "inspect",
        "pass_loaded",
    ] {
        functions
            .iter()
            .find(|function| function.name() == name)
            .expect("parsed aggregate function")
            .to_kernel_function();
    }
}

#[test]
fn c0_enum_metadata_preserves_named_values_and_field_shape() {
    #[repr(C)]
    struct HostPacket {
        tag: u8,
        state: i32,
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        enum packet_state {
            PACKET_IDLE = -1,
            PACKET_READY = 7,
            PACKET_DONE,
        };
        typedef enum packet_state packet_state_t;
        struct packet {
            uint8 tag;
            packet_state_t state;
            int32 tail;
        };

        int32 read_state(struct packet* packet) {
            return packet->state == PACKET_READY;
        }
        "#,
    )
    .expect("named enum fields should parse");

    let enum_definition = function.enums().get("packet_state").expect("enum metadata");
    assert_eq!(enum_definition.value("PACKET_IDLE"), Some(-1));
    assert_eq!(enum_definition.value("PACKET_READY"), Some(7));
    assert_eq!(enum_definition.value("PACKET_DONE"), Some(8));

    let layout = function.structs().get("packet").expect("packet layout");
    let state = layout.field("state").expect("enum field");
    assert_eq!(state.c_type(), syntax::C0Type::Int32);
    assert_eq!(state.enum_name(), Some("packet_state"));
    assert_eq!(
        state.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, state)
    );
    assert_eq!(state.byte_width() as usize, std::mem::size_of::<i32>());
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        layout.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );
}

#[test]
fn c0_enum_field_comparison_lowers_named_constant() {
    let function = syntax::parse_function(
        r#"
        enum packet_state {
            PACKET_IDLE,
            PACKET_READY = 7,
        };
        struct packet {
            uint8 tag;
            enum packet_state state;
        };

        int32 is_ready(struct packet* packet) {
            return packet->state == PACKET_READY;
        }
        "#,
    )
    .expect("enum comparison should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 1, 2);
    let state_pointer = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("packet", 8)
                .store(state_pointer, crate::kernel::int32(7)),
        )
        .with_resource_context(resources.clone());
    let final_state = state.clone();
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("enum comparison should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_rejects_unsupported_enum_shapes() {
    let error = syntax::parse_function(
        r#"
        enum packet_state { PACKET_IDLE, PACKET_READY };
        struct packet {
            enum packet_state states[2];
        };

        int32 read_state(struct packet* packet) {
            return packet->states[0];
        }
        "#,
    )
    .expect_err("enum arrays should remain outside this slice");
    assert!(
        error
            .message()
            .contains("arrays of enum fields are not supported")
    );

    let error = syntax::parse_function(
        r#"
        enum packet_state { PACKET_IDLE, PACKET_READY };

        enum packet_state read_state() {
            return PACKET_READY;
        }
        "#,
    )
    .expect_err("enum return types should remain outside this slice");
    assert!(
        error
            .message()
            .contains("enum return types are not supported")
    );
}

#[test]
fn c0_syntax_lowers_struct_malloc_sizeof_and_free() {
    fn contains_heap_operations(statement: &syntax::C0Statement) -> (bool, bool) {
        match statement {
            syntax::C0Statement::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => {
                assert_eq!(target, "item");
                assert!(!zeroed);
                assert_eq!(
                    *bytes,
                    syntax::C0Expression::SizeOfStruct {
                        name: "item".to_string(),
                        bytes: 16,
                    }
                );
                (true, false)
            }
            syntax::C0Statement::HeapFree { pointer } => {
                assert_eq!(pointer, &syntax::C0Expression::Variable("item".to_string()));
                (false, true)
            }
            syntax::C0Statement::Seq(first, second) => {
                let first = contains_heap_operations(first);
                let second = contains_heap_operations(second);
                (first.0 || second.0, first.1 || second.1)
            }
            _ => (false, false),
        }
    }

    let function = syntax::parse_function(
        r#"
        struct item {
            int32 value;
            struct item* next;
        };

        int32 allocate_then_free() {
            struct item* item = malloc(sizeof(struct item));
            free(item);
            return 0;
        }
        "#,
    )
    .expect("the supported malloc/free slice should parse");

    assert_eq!(contains_heap_operations(function.body()), (true, true));
}

#[test]
fn c0_syntax_accepts_malloc_size_that_does_not_match_its_target() {
    let function = syntax::parse_function(
        r#"
        struct left { int32 value; };
        struct right { int32 value; };
        struct left* wrong() {
            struct left* value = malloc(sizeof(struct right));
            return value;
        }
        "#,
    )
    .expect("malloc should accept a raw byte extent independent of target type");
    assert!(matches!(function.body(), syntax::C0Statement::Seq(_, _)));
}

#[test]
fn c0_syntax_accepts_runtime_sized_int32_allocation() {
    let function = syntax::parse_function(
        r#"
        int32 allocate(int32 count) {
            int32* data = malloc(count * 4);
            free(data);
            return 0;
        }
        "#,
    )
    .expect("runtime-sized scalar allocation should parse");

    assert!(matches!(function.body(), syntax::C0Statement::Seq(_, _)));
}

#[test]
fn c0_syntax_accepts_realloc_with_two_arguments() {
    let function = syntax::parse_function(
        r#"
        int32* resize(int32* data, int32 bytes) {
            int32* result = realloc(data, bytes);
            return result;
        }
        "#,
    )
    .expect("realloc should parse as a two-argument pointer call");

    fn find_realloc(statement: &syntax::C0Statement) -> Option<usize> {
        match statement {
            syntax::C0Statement::CallAssign {
                function_name,
                arguments,
                ..
            } if function_name == "realloc" => Some(arguments.len()),
            syntax::C0Statement::Seq(first, second) => {
                find_realloc(first).or_else(|| find_realloc(second))
            }
            _ => None,
        }
    }

    assert_eq!(find_realloc(function.body()), Some(2));

    let error = syntax::parse_function(
        "int32* bad(int32* data) { int32* result = realloc(data); return result; }",
    )
    .expect_err("realloc must have two arguments");
    assert!(error.message().contains("`realloc` expects two arguments"));
}

#[test]
fn c0_syntax_lowers_calloc_to_zeroed_runtime_allocation() {
    fn find_allocation(
        statement: &syntax::C0Statement,
    ) -> Option<(&str, &syntax::C0Expression, bool)> {
        match statement {
            syntax::C0Statement::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => Some((target, bytes, *zeroed)),
            syntax::C0Statement::Seq(first, second) => {
                find_allocation(first).or_else(|| find_allocation(second))
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => find_allocation(then_branch).or_else(|| find_allocation(else_branch)),
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                find_allocation(body)
            }
            _ => None,
        }
    }

    let function = syntax::parse_function(
        r#"
        int32* allocate_zeroed(int32 count) {
            int32* data = calloc(count, sizeof(int32));
            return data;
        }
        "#,
    )
    .expect("calloc should parse for int32 allocations");
    let (target, bytes, zeroed) = find_allocation(function.body()).expect("calloc should lower");
    assert_eq!(target, "data");
    assert!(zeroed);
    assert_eq!(
        bytes,
        &syntax::C0Expression::Multiply(
            Box::new(syntax::C0Expression::Variable("count".to_string())),
            Box::new(syntax::C0Expression::SizeOfType {
                c_type: syntax::C0Type::Int32,
                struct_name: None,
                bytes: 4,
            }),
        )
    );
}

#[test]
fn c0_syntax_accepts_matching_struct_calloc() {
    let function = syntax::parse_function(
        r#"
        struct item { int32 value; };
        int32 allocate_zeroed(int32 count) {
            struct item* item = calloc(count, sizeof(struct item));
            return item->value;
        }
        "#,
    )
    .expect("calloc should accept a matching struct element size");

    fn find_allocation(
        statement: &syntax::C0Statement,
    ) -> Option<(&str, &syntax::C0Expression, bool)> {
        match statement {
            syntax::C0Statement::HeapAllocate {
                target,
                bytes,
                zeroed,
            } => Some((target, bytes, *zeroed)),
            syntax::C0Statement::Seq(first, second) => {
                find_allocation(first).or_else(|| find_allocation(second))
            }
            _ => None,
        }
    }

    let (target, bytes, zeroed) =
        find_allocation(function.body()).expect("struct calloc should lower");
    assert_eq!(target, "item");
    assert!(zeroed);
    assert_eq!(
        bytes,
        &syntax::C0Expression::Multiply(
            Box::new(syntax::C0Expression::Variable("count".to_string())),
            Box::new(syntax::C0Expression::SizeOfStruct {
                name: "item".to_string(),
                bytes: 4,
            }),
        )
    );
}

#[test]
fn c0_syntax_accepts_matching_pointer_array_calloc() {
    fn assert_pointer_array_calloc(source: &str) {
        let function = syntax::parse_function(source)
            .expect("calloc should accept matching pointer-array element sizes");

        fn find_allocation<'a>(
            statement: &'a syntax::C0Statement,
            target: &str,
        ) -> Option<&'a syntax::C0Expression> {
            match statement {
                syntax::C0Statement::HeapAllocate {
                    target: allocation_target,
                    bytes,
                    zeroed,
                } if allocation_target == target => {
                    assert!(*zeroed);
                    Some(bytes)
                }
                syntax::C0Statement::Seq(first, second) => {
                    find_allocation(first, target).or_else(|| find_allocation(second, target))
                }
                _ => None,
            }
        }

        assert!(matches!(
            find_allocation(function.body(), "slots"),
            Some(syntax::C0Expression::Multiply(_, _))
        ));
    }

    assert_pointer_array_calloc(
        r#"
        int32* allocate_int32_pointers(int32 count) {
            int32** slots = calloc(count, sizeof(int32*));
            return slots[0];
        }
        "#,
    );
    assert_pointer_array_calloc(
        r#"
        uint8* allocate_uint8_pointers(int32 count) {
            uint8** slots = calloc(count, sizeof(uint8*));
            return slots[0];
        }
        "#,
    );
}

#[test]
fn c0_syntax_rejects_mismatched_pointer_array_calloc_element_size() {
    let error = syntax::parse_function(
        r#"
        int32* bad(int32 count) {
            int32** slots = calloc(count, sizeof(uint8));
            return slots[0];
        }
        "#,
    )
    .expect_err("pointer-array calloc must match the target pointer type");
    assert!(error.message().contains("`calloc` currently supports"));
}

#[test]
fn c0_syntax_accepts_sizeof_for_scalar_and_pointer_types() {
    let function = syntax::parse_function(
        r#"
        int32 sizes() {
            return sizeof(int32) + sizeof(uint8) + sizeof(int32*) + sizeof(uint8**);
        }
        "#,
    )
    .expect("sizeof should accept every supported scalar and pointer type");

    let syntax::C0Statement::Return(expression) = function.body() else {
        panic!("sizeof expression should remain in the return statement");
    };
    let kernel_expression = expression.to_kernel_expression();
    assert_eq!(
        kernel_expression,
        crate::kernel::c_add(
            crate::kernel::c_add(
                crate::kernel::c_add(
                    crate::kernel::c_int32_literal(4),
                    crate::kernel::c_int32_literal(1),
                ),
                crate::kernel::c_int32_literal(8),
            ),
            crate::kernel::c_int32_literal(8),
        )
    );
}

#[test]
fn c0_syntax_rejects_wrong_free_arity() {
    let free_error = syntax::parse_function(
        r#"
        int32 bad_free(int32* value) {
            free(value, value);
            return 0;
        }
        "#,
    )
    .expect_err("free must have one argument");
    assert!(
        free_error
            .message()
            .contains("expects one pointer argument")
    );
}

#[test]
fn c0_chained_field_load_executes_through_typed_pointer_memory() {
    let function = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };
        struct node {
            struct leaf* child;
        };

        int32 read_nested(struct node* root) {
            return root->child->value;
        }
        "#,
    )
    .expect("chained struct-pointer fields should parse");
    let root = crate::kernel::Pointer {
        block: "root".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let leaf = crate::kernel::Pointer {
        block: "leaf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let memory = crate::kernel::CMemory::new()
        .store(root.clone(), crate::kernel::CValue::pointer(leaf.clone()))
        .store(leaf.clone(), crate::kernel::int32(9));
    let resources = crate::kernel::ResourceContext::new()
        .unchecked_with_fact(crate::kernel::CResourceFact::view_memory(memory_range(
            root.clone(),
            0,
            2,
        )))
        .unchecked_with_fact(crate::kernel::CResourceFact::view_memory(memory_range(
            leaf, 0, 1,
        )));
    let state = crate::kernel::CState::new()
        .with_local("root", crate::kernel::CValue::pointer(root))
        .with_memory(memory)
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_execution(
        state,
        function.body_kernel_statement(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("the nested typed loads should execute");
    let mut proposition = theorem.proposition();
    while let crate::kernel::Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        crate::kernel::Proposition::CStatementExecutes {
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::CValue::Int32(crate::kernel::Bitvector32Term::Constant(9)),
                ..
            },
            ..
        }
    ));
}

#[test]
fn c0_syntax_parses_chained_field_store_targets() {
    let function = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };
        struct node {
            struct leaf* child;
        };

        int32 write_nested(struct node* root, int32 value) {
            root->child->value = value;
            return value;
        }
        "#,
    )
    .expect("a chained field should remain a typed assignment target");

    assert!(matches!(
        function.body(),
        syntax::C0Statement::Seq(first, _)
            if matches!(
                first.as_ref(),
                syntax::C0Statement::Store {
                    pointer: syntax::C0Expression::Field {
                        field_type: syntax::C0Type::Int32Pointer,
                        field_struct_name: Some(name),
                        ..
                    },
                    value_type: Some(syntax::C0Type::Int32),
                    ..
                } if name == "leaf"
            )
    ));
}

#[test]
fn c0_syntax_names_invalid_field_chains() {
    let error = syntax::parse_function(
        r#"
        struct leaf {
            int32 value;
        };

        int32 invalid(struct leaf* root) {
            return root->value->missing;
        }
        "#,
    )
    .expect_err("a scalar field cannot be dereferenced as a struct pointer");

    assert_eq!(
        error.message(),
        "cannot access field `missing` through a non-struct-pointer expression"
    );
}

#[test]
fn c0_syntax_targets_kernel_max_body() {
    let function = syntax::parse_function(
        r#"
        int32 max(int32 a, int32 b) {
            if (a < b) {
                return b;
            } else {
                return a;
            }
        }
        "#,
    )
    .expect("max should parse");
    let statement = function.body_kernel_statement();

    assert_eq!(statement, crate::kernel::c_max_body());

    let a = crate::kernel::Variable(30);
    let b = crate::kernel::Variable(31);
    let a_bits = crate::kernel::Bitvector32Term::Variable(a);
    let b_bits = crate::kernel::Bitvector32Term::Variable(b);
    let condition = crate::kernel::c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state =
        crate::kernel::c_max_state(crate::kernel::int32(a_bits), crate::kernel::int32(b_bits));
    let assumptions =
        crate::kernel::PureFactContext::new().assume_condition(condition.clone(), true);
    let theorem =
        crate::kernel::prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
            .expect("parsed max should symbolically execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::Implies(
            Box::new(crate::kernel::Proposition::ConditionIs(condition, true)),
            Box::new(crate::kernel::Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: crate::kernel::CStatementOutcome::Return {
                    value: crate::kernel::int32(crate::kernel::Bitvector32Term::Variable(b)),
                    state,
                },
            }),
        )
    );
}

#[test]
fn c0_syntax_targets_kernel_max_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 max(int32 a, int32 b) {
            if (a < b) {
                return b;
            } else {
                return a;
            }
        }
        "#,
    )
    .expect("max should parse");
    let function = function.to_kernel_function();

    assert_eq!(function, crate::kernel::c_max_function());

    let state = crate::kernel::CState::new();
    let arguments = vec![
        crate::kernel::c_int32_literal(0),
        crate::kernel::c_int32_literal(1),
    ];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed max function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_assignment_and_sequence() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let statement = function.body_kernel_statement();
    let initial = crate::kernel::CState::new().with_local("x", crate::kernel::int32(1));
    let final_state = crate::kernel::CState::new().with_local("x", crate::kernel::int32(2));
    let theorem = crate::kernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: initial,
            statement,
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::int32(2),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_assignment_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 inc(int32 x) {
            x = x + 1;
            return x;
        }
        "#,
    )
    .expect("assignment function should parse");
    let function = function.to_kernel_function();
    let state = crate::kernel::CState::new().with_local("caller", crate::kernel::int32(5));
    let arguments = vec![crate::kernel::c_int32_literal(1)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed assignment function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(2),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_store_and_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_after_store(int32* p) {
            *p = 9;
            return *p;
        }
        "#,
    )
    .expect("store/load function should parse");

    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let statement = function.body_kernel_statement();
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let initial = crate::kernel::CState::new()
        .with_local("p", crate::kernel::CValue::pointer(pointer.clone()))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_local("p", crate::kernel::CValue::pointer(pointer.clone()))
        .with_memory(crate::kernel::CMemory::new().store(pointer.clone(), crate::kernel::int32(9)))
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: initial,
            statement,
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_struct_field_load() {
    let function = syntax::parse_function(
        r#"
        struct json_object {
            int32 ref_count;
        };

        int32 json_object_get_ref_count(struct json_object* obj) {
            return obj->ref_count;
        }
        "#,
    )
    .expect("pilot struct getter should parse");

    assert_eq!(
        function.parameters()[0].c_type(),
        syntax::C0Type::Int32Pointer
    );
    assert_eq!(function.parameters()[0].struct_name(), Some("json_object"));

    let pointer = crate::kernel::Pointer {
        block: "object".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let statement = function.body_kernel_statement();
    let memory = crate::kernel::CMemory::new()
        .with_block("object", 4)
        .store(pointer.clone(), crate::kernel::int32(3));
    let initial = crate::kernel::CState::new()
        .with_local("obj", crate::kernel::CValue::pointer(pointer.clone()))
        .with_memory(memory)
        .with_resource_context(view_memory_context(pointer, 0, 1));
    let theorem = crate::kernel::prove_symbolic_c_execution(
        initial.clone(),
        statement.clone(),
        Default::default(),
    )
    .expect("parsed struct getter should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CStatementExecutes {
            state: initial.clone(),
            statement,
            outcome: crate::kernel::CStatementOutcome::Return {
                value: crate::kernel::int32(3),
                state: initial,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_struct_field_store() {
    let function = syntax::parse_function(
        r#"
        struct json_object {
            int32 ref_count;
        };

        int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
            obj->ref_count = count;
            return obj->ref_count;
        }
        "#,
    )
    .expect("pilot struct setter should parse")
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "object".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("object", 4))
        .with_resource_context(resources.clone());
    let arguments = vec![
        crate::kernel::c_pointer_value(pointer.clone()),
        crate::kernel::c_int32_literal(5),
    ];
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("object", 4)
                .store(pointer, crate::kernel::int32(5)),
        )
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed struct setter should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_accepts_indexed_store_through_struct_pointer_field() {
    syntax::parse_function(
        r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 set_at(struct vector* owner, int32 index, int32 value) {
            owner->data[index] = value;
            return owner->data[index];
        }
        "#,
    )
    .expect("indexed store through pointer field should parse")
    .to_kernel_function();
}

#[test]
fn c0_syntax_targets_kernel_multifield_struct_offset_load() {
    let function = syntax::parse_function(
        r#"
        struct pair {
            int32 first;
            int32 second;
        };

        int32 pair_second(struct pair* p) {
            return p->second;
        }
        "#,
    )
    .expect("multi-field struct getter should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "pair".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "pair".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("pair", 8)
        .store(second, crate::kernel::int32(7));
    let state = crate::kernel::CState::new()
        .with_memory(memory)
        .with_resource_context(view_memory_context(base.clone(), 1, 2));
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed multi-field struct getter should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_struct_pointer_field_roundtrip() {
    let function = syntax::parse_function(
        r#"
        struct owner {
            int32 len;
            int32* data;
        };

        int32 set_owned_first(struct owner* owner, int32 data[]) {
            int32* current;
            owner->len = 1;
            owner->data = data;
            current = owner->data;
            current[0] = owner->len;
            return current[0];
        }
        "#,
    )
    .expect("struct pointer field roundtrip should parse")
    .to_kernel_function();

    let owner = crate::kernel::Pointer {
        block: "owner".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let owner_data = crate::kernel::Pointer {
        block: "owner".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(8),
    };
    let data = crate::kernel::Pointer {
        block: "data".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = crate::kernel::ResourceContext::new().unchecked_with_facts(vec![
        crate::kernel::CResourceFact::own_memory(memory_range(owner.clone(), 0, 4)),
        crate::kernel::CResourceFact::own_memory(memory_range(data.clone(), 0, 1)),
    ]);
    let state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("owner", 16)
                .with_block("data", 4),
        )
        .with_resource_context(resources);
    let arguments = vec![
        crate::kernel::c_pointer_value(owner.clone()),
        crate::kernel::c_pointer_value(data.clone()),
    ];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed struct pointer field roundtrip should execute");

    let crate::kernel::Proposition::CFunctionExecutes {
        outcome:
            crate::kernel::CFunctionOutcome::Return {
                value,
                state: final_state,
            },
        ..
    } = theorem.proposition()
    else {
        panic!("expected function execution theorem, got {:#?}", theorem);
    };

    assert_eq!(value, &crate::kernel::int32(1));
    assert_eq!(
        final_state.memory().load(&owner),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::int32(1))
    );
    assert_eq!(
        final_state.memory().load(&owner_data),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::CValue::pointer(data.clone()))
    );
    assert_eq!(
        final_state.memory().load(&data),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::int32(1))
    );
}

#[test]
fn c0_syntax_targets_kernel_store_and_load_function_call() {
    let function = syntax::parse_function(
        r#"
        int32 load_after_store(int32* p) {
            *p = 9;
            return *p;
        }
        "#,
    )
    .expect("store/load function should parse")
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(pointer.clone(), 0, 1);
    let state = crate::kernel::CState::new()
        .with_local("caller", crate::kernel::int32(7))
        .with_resource_context(resources.clone());
    let arguments = vec![crate::kernel::c_pointer_value(pointer.clone())];
    let final_state = crate::kernel::CState::new()
        .with_local("caller", crate::kernel::int32(7))
        .with_memory(crate::kernel::CMemory::new().store(pointer.clone(), crate::kernel::int32(9)))
        .with_resource_context(resources);
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed store/load function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_pointer_addition_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_second(int32* p) {
            return *(p + 1);
        }
        "#,
    )
    .expect("pointer-add load function should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), crate::kernel::int32(23));
    let resources = view_memory_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed pointer-add load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(23),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_array_index_load() {
    let function = syntax::parse_function(
        r#"
        int32 load_second(int32* p) {
            return p[1];
        }
        "#,
    )
    .expect("array-index load function should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), crate::kernel::int32(23));
    let resources = view_memory_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed array-index load should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(23),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_array_index_store() {
    let function = syntax::parse_function(
        r#"
        int32 store_second(int32* p) {
            p[1] = 7;
            return p[1];
        }
        "#,
    )
    .expect("array-index store function should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let memory = crate::kernel::CMemory::new().with_block("block", 16);
    let resources = own_memory_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("block", 16)
                .store(second, crate::kernel::int32(7)),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed array-index store should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_address_of_array_index() {
    let function = syntax::parse_function(
        r#"
        int32 load_second_through_address(int32* p) {
            int32* q;
            q = &p[1];
            return *q;
        }
        "#,
    )
    .expect("address-of array-index function should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let local_q = crate::kernel::Pointer {
        block: "local:q".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let memory = crate::kernel::CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), crate::kernel::int32(23));
    let resources = view_memory_context(base.clone(), 1, 2);
    let state = crate::kernel::CState::new()
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("block", 16)
                .with_block("local:q", 8)
                .store(second.clone(), crate::kernel::int32(23))
                .store(local_q, crate::kernel::CValue::pointer(second.clone())),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed address-of array-index should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(23),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_pointer_null_equality() {
    let function = syntax::parse_function(
        r#"
        int32 is_null(int32* p) {
            if (p == 0) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("pointer null check should parse")
    .to_kernel_function();

    let null = crate::kernel::Pointer {
        block: "null".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_pointer_value(null)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("parsed pointer null check should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_logical_short_circuiting() {
    let function = syntax::parse_function(
        r#"
        int32 safe_is_three(int32* p) {
            if (p == 0 || (p != 0 && *p == 3)) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("logical short-circuit function should parse")
    .to_kernel_function();

    let null = crate::kernel::Pointer {
        block: "null".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let cases = [
        (
            crate::kernel::CState::new(),
            vec![crate::kernel::c_pointer_value(null)],
            crate::kernel::int32(1),
        ),
        (
            crate::kernel::CState::new()
                .with_memory(
                    crate::kernel::CMemory::new()
                        .with_block("block", 4)
                        .store(pointer.clone(), crate::kernel::int32(3)),
                )
                .with_resource_context(view_memory_context(pointer.clone(), 0, 1)),
            vec![crate::kernel::c_pointer_value(pointer.clone())],
            crate::kernel::int32(1),
        ),
        (
            crate::kernel::CState::new()
                .with_memory(
                    crate::kernel::CMemory::new()
                        .with_block("block", 4)
                        .store(pointer.clone(), crate::kernel::int32(4)),
                )
                .with_resource_context(view_memory_context(pointer.clone(), 0, 1)),
            vec![crate::kernel::c_pointer_value(pointer.clone())],
            crate::kernel::int32(0),
        ),
    ];

    for (state, arguments, expected) in cases {
        let theorem = crate::kernel::prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            arguments.clone(),
            crate::kernel::PureFactContext::new(),
        )
        .expect("logical short-circuit function should execute");

        assert_eq!(
            theorem.proposition(),
            &crate::kernel::Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments,
                outcome: crate::kernel::CFunctionOutcome::Return {
                    value: expected,
                    state,
                },
            }
        );
    }
}

#[test]
fn c0_syntax_targets_kernel_unary_not() {
    let function = syntax::parse_function(
        r#"
        int32 not_null(int32* p) {
            if (!(p == 0)) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("unary not function should parse")
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_pointer_value(pointer)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        crate::kernel::PureFactContext::new(),
    )
    .expect("unary not function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_local_address_of() {
    let function = syntax::parse_function(
        r#"
        int32 local_read() {
            int32 x;
            x = 5;
            return *(&x);
        }
        "#,
    )
    .expect("local address-of function should parse")
    .to_kernel_function();

    let local_pointer = crate::kernel::Pointer {
        block: "local:x".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, crate::kernel::int32(5)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("parsed local address-of function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_local_array_storage() {
    let function = syntax::parse_function(
        r#"
        int32 local_array_roundtrip() {
            int32 a[3];
            a[0] = 5;
            a[1] = 7;
            return a[1];
        }
        "#,
    )
    .expect("local array function should parse")
    .to_kernel_function();

    let a0 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let a1 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:a", 12)
            .store(a0, crate::kernel::int32(5))
            .store(a1, crate::kernel::int32(7)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local array function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_lowers_local_array_initializer_stores() {
    let function = syntax::parse_function(
        r#"
        int32 local_array_initializer() {
            int32 a[3] = {1, 2};
            return a[2];
        }
        "#,
    )
    .expect("local array initializer should parse")
    .to_kernel_function();

    let a0 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let a1 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let a2 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(8),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:a", 12)
            .store(a0, crate::kernel::int32(1))
            .store(a1, crate::kernel::int32(2))
            .store(a2, crate::kernel::int32(0)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local array initializer should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(0),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_flattens_multidimensional_local_array_indices() {
    let function = syntax::parse_function(
        r#"
        int32 matrix_roundtrip() {
            int32 values[2][3];
            values[0][0] = 1;
            values[1][2] = 7;
            return values[1][2];
        }
        "#,
    )
    .expect("multidimensional local array should parse")
    .to_kernel_function();

    let first = crate::kernel::Pointer {
        block: "local:values".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let last = crate::kernel::Pointer {
        block: "local:values".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(20),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:values", 24)
            .store(first, crate::kernel::int32(1))
            .store(last, crate::kernel::int32(7)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("multidimensional local array should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_lowers_nested_multidimensional_array_initializers() {
    let function = syntax::parse_function(
        r#"
        int32 matrix_initializer() {
            int32 values[2][3] = {{1, 2, 3}, {4, 5, 6}};
            return values[1][2];
        }
        "#,
    )
    .expect("nested multidimensional array initializers should parse")
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:values", 24)
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0),
                },
                crate::kernel::int32(1),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(4),
                },
                crate::kernel::int32(2),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(8),
                },
                crate::kernel::int32(3),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(12),
                },
                crate::kernel::int32(4),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(16),
                },
                crate::kernel::int32(5),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:values".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(20),
                },
                crate::kernel::int32(6),
            ),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("nested multidimensional array initializers should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(6),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_lowers_local_struct_array_fields_with_abi_stride() {
    let function = syntax::parse_function(
        r#"
        struct item {
            uint8 tag;
            int32 value;
        };

        int32 struct_array_roundtrip() {
            struct item items[2];
            items[0].tag = 3;
            items[1].value = 7;
            return items[0].tag + items[1].value;
        }
        "#,
    )
    .expect("local arrays of structs should parse")
    .to_kernel_function();

    let tag = crate::kernel::Pointer {
        block: "local:items".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let value = crate::kernel::Pointer {
        block: "local:items".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(12),
    };
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:items", 16)
            .store(tag, crate::kernel::uint8(3))
            .store(value, crate::kernel::int32(7)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local struct array fields should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(10),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_lowers_local_struct_array_initializers() {
    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
            uint8 enabled;
        };

        struct item {
            uint8 tag;
            struct inner inner;
            int32 values[2];
        };

        int32 local_struct_array_initializer() {
            struct item items[2] = {
                {1, {10, 1}, {2}},
                {2, {20}, {3, 4}}
            };
            return items[0].tag + items[0].inner.value
                + items[0].inner.enabled + items[0].values[0]
                + items[0].values[1] + items[1].tag
                + items[1].inner.value + items[1].inner.enabled
                + items[1].values[0] + items[1].values[1];
        }
        "#,
    )
    .expect("local struct array initializers should parse")
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:items", 40)
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0),
                },
                crate::kernel::uint8(1),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(4),
                },
                crate::kernel::int32(10),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(8),
                },
                crate::kernel::uint8(1),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(12),
                },
                crate::kernel::int32(2),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(16),
                },
                crate::kernel::int32(0),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(20),
                },
                crate::kernel::uint8(2),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(24),
                },
                crate::kernel::int32(20),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(28),
                },
                crate::kernel::uint8(0),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(32),
                },
                crate::kernel::int32(3),
            )
            .store(
                crate::kernel::Pointer {
                    block: "local:items".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(36),
                },
                crate::kernel::int32(4),
            ),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("local struct array initializers should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(43),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_struct_array_parameter_retains_abi_stride() {
    let function = syntax::parse_function(
        r#"
        struct item {
            uint8 tag;
            int32 value;
        };

        int32 read_item(struct item items[2]) {
            return items[1].value;
        }
        "#,
    )
    .expect("struct array parameters should parse");

    let parameter = &function.parameters()[0];
    assert_eq!(parameter.c_type(), syntax::C0Type::Int32Pointer);
    assert_eq!(parameter.array_element_width(), Some(8));
    assert_eq!(
        parameter.to_kernel_parameter().c_type(),
        crate::kernel::CType::UInt8Pointer
    );
}

#[test]
fn c0_syntax_local_array_decays_to_pointer_argument() {
    let read_first = syntax::parse_function(
        r#"
        int32 read_first(int32* p) {
            return p[0];
        }
        "#,
    )
    .expect("helper function should parse")
    .to_kernel_function();
    let caller = syntax::parse_function(
        r#"
        int32 caller() {
            int32 a[2];
            a[0] = 11;
            int32 result;
            result = read_first(a);
            return result;
        }
        "#,
    )
    .expect("caller function should parse")
    .to_kernel_function();

    let a0 = crate::kernel::Pointer {
        block: "local:a".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let result_pointer = crate::kernel::Pointer {
        block: "local:result".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let environment = crate::kernel::CExecutionEnvironment::new().with_function(read_first);
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:a", 8)
            .with_block("local:result", 4)
            .store(a0, crate::kernel::int32(11))
            .store(result_pointer, crate::kernel::int32(11)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        environment,
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("local array should decay to pointer argument");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(11),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_struct_layout_uses_lp64_alignment_and_tail_padding() {
    let function = syntax::parse_function(
        r#"
        struct mixed {
            int32 tag;
            int32* data;
            int32 length;
        };

        int32 read_tag(struct mixed* value) {
            return value->tag;
        }
        "#,
    )
    .expect("LP64 struct should parse");
    let layout = function.structs().get("mixed").expect("mixed layout");

    assert_eq!(layout.field("tag").unwrap().offset_bytes(), 0);
    assert_eq!(layout.field("data").unwrap().offset_bytes(), 8);
    assert_eq!(layout.field("length").unwrap().offset_bytes(), 16);
    assert_eq!(layout.alignment_bytes(), 8);
    assert_eq!(layout.size_bytes(), 24);
}

#[test]
fn c0_struct_layout_preserves_wide_scalar_field_types_and_lp64_offsets() {
    #[repr(C)]
    struct HostPacket {
        tag: u8,
        count: u32,
        total: i64,
        mask: u64,
        tail: u8,
    }

    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            uint32 count;
            int64 total;
            uint64 mask;
            uint8 tail;
        };

        uint64 read_mask(struct packet* packet) {
            return packet->mask;
        }
        "#,
    )
    .expect("wide scalar struct fields should parse");
    let layout = function.structs().get("packet").expect("packet layout");

    let tag = layout.field("tag").expect("tag field");
    assert_eq!(tag.c_type(), syntax::C0Type::UInt8);
    assert_eq!(tag.byte_width(), 1);
    assert_eq!(
        tag.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, tag)
    );

    let count = layout.field("count").expect("count field");
    assert_eq!(count.c_type(), syntax::C0Type::UInt32);
    assert_eq!(count.byte_width(), 4);
    assert_eq!(
        count.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, count)
    );

    let total = layout.field("total").expect("total field");
    assert_eq!(total.c_type(), syntax::C0Type::Int64);
    assert_eq!(total.byte_width(), 8);
    assert_eq!(
        total.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, total)
    );

    let mask = layout.field("mask").expect("mask field");
    assert_eq!(mask.c_type(), syntax::C0Type::UInt64);
    assert_eq!(mask.byte_width(), 8);
    assert_eq!(
        mask.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, mask)
    );

    let tail = layout.field("tail").expect("tail field");
    assert_eq!(tail.c_type(), syntax::C0Type::UInt8);
    assert_eq!(tail.byte_width(), 1);
    assert_eq!(
        tail.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, tail)
    );
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        layout.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );
}

#[test]
fn c0_wide_scalar_struct_fields_execute_at_declared_widths() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            uint32 count;
            int64 total;
            uint64 mask;
            uint8 tail;
        };

        uint64 update(struct packet* packet) {
            packet->count = 7u;
            packet->total = -9;
            packet->mask = 11ull;
            return packet->mask;
        }
        "#,
    )
    .expect("wide scalar struct fields should lower")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 8);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 32))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("packet", 32)
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(4),
                    },
                    crate::kernel::uint32(7),
                )
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(8),
                    },
                    crate::kernel::int64(crate::kernel::Bitvector32Term::Int64Constant(-9)),
                )
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(16),
                    },
                    crate::kernel::uint64(crate::kernel::Bitvector32Term::UInt64Constant(11)),
                ),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("wide scalar struct fields should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::uint64(crate::kernel::Bitvector32Term::UInt64Constant(11)),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_scalar_struct_values_preserve_named_kernel_layout_metadata() {
    let function = syntax::parse_function(
        r#"
        struct pair {
            int32 first;
            uint8 tag;
        };

        struct pair identity(struct pair value) {
            return value;
        }
        "#,
    )
    .expect("scalar-only struct values should parse");

    assert_eq!(function.return_type(), syntax::C0Type::UInt8Array(8));
    assert_eq!(function.return_struct_name(), Some("pair"));
    let parameter = &function.parameters()[0];
    assert!(parameter.is_struct_value());
    assert_eq!(parameter.struct_name(), Some("pair"));
    assert_eq!(parameter.struct_layout().unwrap().size_bytes(), 8);

    let kernel = function.to_kernel_function();
    assert_eq!(kernel.return_type(), crate::kernel::CType::UInt8Pointer);
    let return_layout = kernel
        .return_aggregate_layout()
        .expect("struct return should retain aggregate metadata");
    assert_eq!(return_layout.size_bytes(), 8);
    assert_eq!(return_layout.fields()[0].name(), "first");
    assert_eq!(return_layout.fields()[0].offset_bytes(), 0);
    assert_eq!(
        return_layout.fields()[0].c_type(),
        crate::kernel::CType::Int32
    );
    assert_eq!(return_layout.fields()[1].name(), "tag");
    assert_eq!(return_layout.fields()[1].offset_bytes(), 4);
    assert_eq!(
        return_layout.fields()[1].c_type(),
        crate::kernel::CType::UInt8
    );

    let parameter_layout = kernel.parameters()[0]
        .aggregate_layout()
        .expect("struct parameter should retain aggregate metadata");
    assert_eq!(parameter_layout, return_layout);
}

#[test]
fn c0_struct_values_preserve_wide_scalar_layout_metadata() {
    let function = syntax::parse_function(
        r#"
        struct widths {
            uint32 count;
            int64 total;
            uint64 mask;
        };

        struct widths update(struct widths value) {
            value.count = 7u;
            value.total = -9;
            value.mask = 11ull;
            return value;
        }
        "#,
    )
    .expect("wide scalar struct values should parse");

    let kernel = function.to_kernel_function();
    let layout = kernel.parameters()[0]
        .aggregate_layout()
        .expect("wide scalar struct parameter should retain aggregate metadata");
    assert_eq!(layout.size_bytes(), 24);
    let field = |name: &str| {
        layout
            .fields()
            .iter()
            .find(|field| field.name() == name)
            .unwrap_or_else(|| panic!("missing aggregate field `{name}`"))
    };
    assert_eq!(field("count").offset_bytes(), 0);
    assert_eq!(field("count").c_type(), crate::kernel::CType::UInt32);
    assert_eq!(field("total").offset_bytes(), 8);
    assert_eq!(field("total").c_type(), crate::kernel::CType::Int64);
    assert_eq!(field("mask").offset_bytes(), 16);
    assert_eq!(field("mask").c_type(), crate::kernel::CType::UInt64);

    let return_layout = kernel
        .return_aggregate_layout()
        .expect("wide scalar struct return should retain aggregate metadata");
    assert_eq!(return_layout, layout);
}

#[test]
fn c0_struct_values_flatten_embedded_layout_for_recursive_copies() {
    #[repr(C)]
    struct HostInner {
        value: i32,
        flag: u8,
    }
    #[repr(C)]
    struct HostOuter {
        tag: u8,
        inner: HostInner,
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
            uint8 flag;
        };
        struct outer {
            uint8 tag;
            struct inner inner;
            int32 tail;
        };

        struct outer finish(struct outer value) {
            value.inner.value = 7;
            value.inner.flag = 9;
            return value;
        }
        "#,
    )
    .expect("embedded structs should be supported in struct values");

    let outer = function.structs().get("outer").expect("outer layout");
    assert_eq!(
        outer.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
    assert_eq!(
        outer.alignment_bytes() as usize,
        std::mem::align_of::<HostOuter>()
    );
    assert_eq!(
        outer.field("inner").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, inner)
    );
    assert_eq!(
        outer.field("inner").unwrap().byte_width() as usize,
        std::mem::size_of::<HostInner>()
    );

    let kernel = function.to_kernel_function();
    let layout = kernel.parameters()[0]
        .aggregate_layout()
        .expect("embedded struct parameter should retain aggregate metadata");
    let field = |name: &str| {
        layout
            .fields()
            .iter()
            .find(|field| field.name() == name)
            .unwrap_or_else(|| panic!("missing flattened aggregate field `{name}`"))
    };
    assert_eq!(field("tag").offset_bytes(), 0);
    assert_eq!(field("tag").c_type(), crate::kernel::CType::UInt8);
    assert_eq!(
        field("inner.value").offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, inner) + std::mem::offset_of!(HostInner, value)
    );
    assert_eq!(field("inner.value").c_type(), crate::kernel::CType::Int32);
    assert_eq!(
        field("inner.flag").offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, inner) + std::mem::offset_of!(HostInner, flag)
    );
    assert_eq!(field("inner.flag").c_type(), crate::kernel::CType::UInt8);
    assert_eq!(
        field("tail").offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, tail)
    );
    assert_eq!(field("tail").c_type(), crate::kernel::CType::Int32);
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
}

#[test]
fn c0_struct_values_flatten_embedded_array_layout_for_recursive_copies() {
    #[repr(C)]
    struct HostInner {
        value: i32,
        flag: u8,
    }
    #[repr(C)]
    struct HostOuter {
        tag: u8,
        points: [HostInner; 2],
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
            uint8 flag;
        };
        struct outer {
            uint8 tag;
            struct inner points[2];
            int32 tail;
        };

        struct outer finish(struct outer value) {
            value.points[1].value = 7;
            value.points[1].flag = 9;
            return value;
        }
        "#,
    )
    .expect("one-dimensional embedded struct arrays should be supported in struct values");

    let outer = function.structs().get("outer").expect("outer layout");
    assert_eq!(
        outer.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
    assert_eq!(
        outer.alignment_bytes() as usize,
        std::mem::align_of::<HostOuter>()
    );
    let points = outer.field("points").expect("points field");
    assert_eq!(points.c_type(), syntax::C0Type::UInt8Array(16));
    assert_eq!(points.struct_name(), Some("inner"));
    assert_eq!(points.array_element_width(), Some(8));
    assert_eq!(points.array_shape(), Some(&[2][..]));
    assert_eq!(
        points.offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, points)
    );

    let kernel = function.to_kernel_function();
    let layout = kernel.parameters()[0]
        .aggregate_layout()
        .expect("embedded struct array parameter should retain aggregate metadata");
    let field = |name: &str| {
        layout
            .fields()
            .iter()
            .find(|field| field.name() == name)
            .unwrap_or_else(|| panic!("missing flattened aggregate field `{name}`"))
    };
    assert_eq!(field("tag").offset_bytes(), 0);
    assert_eq!(field("tag").c_type(), crate::kernel::CType::UInt8);
    assert_eq!(field("points[0].value").offset_bytes(), 4);
    assert_eq!(
        field("points[0].value").c_type(),
        crate::kernel::CType::Int32
    );
    assert_eq!(field("points[0].flag").offset_bytes(), 8);
    assert_eq!(
        field("points[0].flag").c_type(),
        crate::kernel::CType::UInt8
    );
    assert_eq!(field("points[1].value").offset_bytes(), 12);
    assert_eq!(
        field("points[1].value").c_type(),
        crate::kernel::CType::Int32
    );
    assert_eq!(field("points[1].flag").offset_bytes(), 16);
    assert_eq!(
        field("points[1].flag").c_type(),
        crate::kernel::CType::UInt8
    );
    assert_eq!(field("tail").offset_bytes(), 20);
    assert_eq!(field("tail").c_type(), crate::kernel::CType::Int32);
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
}

#[test]
fn c0_struct_values_flatten_multidimensional_embedded_array_layout_for_recursive_copies() {
    #[repr(C)]
    struct HostInner {
        value: i32,
        flag: u8,
    }

    #[repr(C)]
    struct HostOuter {
        tag: u8,
        points: [[HostInner; 2]; 2],
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
            uint8 flag;
        };
        struct outer {
            uint8 tag;
            struct inner points[2][2];
            int32 tail;
        };

        struct outer finish(struct outer value) {
            value.points[1][1].value = 7;
            value.points[1][1].flag = 9;
            return value;
        }
        "#,
    )
    .expect("multidimensional embedded struct arrays should be supported in struct values");

    let outer = function.structs().get("outer").expect("outer layout");
    assert_eq!(
        outer.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
    assert_eq!(
        outer.alignment_bytes() as usize,
        std::mem::align_of::<HostOuter>()
    );
    let points = outer.field("points").expect("points field");
    assert_eq!(points.c_type(), syntax::C0Type::UInt8Array(32));
    assert_eq!(points.struct_name(), Some("inner"));
    assert_eq!(points.array_element_width(), Some(8));
    assert_eq!(points.array_shape(), Some(&[2, 2][..]));
    assert_eq!(
        points.offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, points)
    );

    let kernel = function.to_kernel_function();
    let layout = kernel.parameters()[0]
        .aggregate_layout()
        .expect("multidimensional embedded struct array parameter metadata");
    let field = |name: &str| {
        layout
            .fields()
            .iter()
            .find(|field| field.name() == name)
            .unwrap_or_else(|| panic!("missing flattened aggregate field `{name}`"))
    };
    assert_eq!(field("tag").offset_bytes(), 0);
    assert_eq!(field("points[0][0].value").offset_bytes(), 4);
    assert_eq!(field("points[0][0].flag").offset_bytes(), 8);
    assert_eq!(field("points[0][1].value").offset_bytes(), 12);
    assert_eq!(field("points[0][1].flag").offset_bytes(), 16);
    assert_eq!(field("points[1][0].value").offset_bytes(), 20);
    assert_eq!(field("points[1][0].flag").offset_bytes(), 24);
    assert_eq!(field("points[1][1].value").offset_bytes(), 28);
    assert_eq!(field("points[1][1].flag").offset_bytes(), 32);
    assert_eq!(field("tail").offset_bytes(), 36);
    assert_eq!(field("tail").c_type(), crate::kernel::CType::Int32);
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostOuter>()
    );
}

#[test]
fn c0_struct_values_preserve_pointer_field_layout_metadata() {
    #[repr(C)]
    struct HostPacket {
        data: *mut i32,
        length: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct packet {
            int32* data;
            int32 length;
        };

        struct packet identity(struct packet value) {
            return value;
        }
        "#,
    )
    .expect("data-pointer struct values should parse");

    let packet = function.structs().get("packet").expect("packet layout");
    assert_eq!(
        packet.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        packet.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );
    assert_eq!(packet.field("data").unwrap().offset_bytes(), 0);
    assert_eq!(packet.field("length").unwrap().offset_bytes(), 8);

    let kernel = function.to_kernel_function();
    let layout = kernel.parameters()[0]
        .aggregate_layout()
        .expect("pointer-bearing struct parameter should retain aggregate metadata");
    assert_eq!(layout.size_bytes(), 16);
    assert_eq!(layout.fields()[0].name(), "data");
    assert_eq!(layout.fields()[0].offset_bytes(), 0);
    assert_eq!(
        layout.fields()[0].c_type(),
        crate::kernel::CType::Int32Pointer
    );
    assert_eq!(layout.fields()[1].name(), "length");
    assert_eq!(layout.fields()[1].offset_bytes(), 8);
    assert_eq!(layout.fields()[1].c_type(), crate::kernel::CType::Int32);
}

#[test]
fn c0_struct_value_pointer_parameter_and_return_copy_pointee_identity() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            int32* data;
            int32 length;
        };

        struct packet bump(struct packet value) {
            value.length = 7;
            return value;
        }
        "#,
    )
    .expect("pointer-bearing struct function should parse")
    .to_kernel_function();

    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let data = crate::kernel::Pointer {
        block: "data".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("packet", 16)
            .with_block("data", 4)
            .store(data.clone(), crate::kernel::int32(2))
            .store(
                packet.clone(),
                crate::kernel::CValue::typed_pointer(
                    data.clone(),
                    crate::kernel::CType::Int32Pointer,
                ),
            )
            .store(packet.offset_by_bytes(8), crate::kernel::int32(4)),
    );
    let arguments = vec![crate::kernel::c_typed_pointer_value(
        packet.clone(),
        crate::kernel::CType::UInt8Pointer,
    )];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state,
        function,
        arguments,
        Default::default(),
    )
    .expect("pointer-bearing struct parameter and return should execute");

    let crate::kernel::Proposition::CFunctionExecutes {
        outcome:
            crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::CValue::Pointer(return_pointer),
                state: final_state,
            },
        ..
    } = theorem.proposition()
    else {
        panic!("expected a pointer-bearing aggregate return");
    };
    let return_data = return_pointer.pointer().offset_by_bytes(0);
    assert_eq!(
        final_state.memory().load(&return_data),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::CValue::typed_pointer(
            data,
            crate::kernel::CType::Int32Pointer,
        ))
    );
    assert_eq!(
        final_state
            .memory()
            .load(&return_pointer.pointer().offset_by_bytes(8)),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::int32(7))
    );
    assert_eq!(
        final_state.memory().load(&packet.offset_by_bytes(8)),
        crate::kernel::CExpressionOutcome::Value(crate::kernel::int32(4))
    );
}

#[test]
fn c0_rejects_union_struct_values_with_a_shape_diagnostic() {
    let error = syntax::parse_function(
        r#"
        union payload {
            int32 number;
            int32* pointer;
        };

        struct packet {
            union payload payload;
        };

        struct packet invalid(struct packet value) {
            return value;
        }
        "#,
    )
    .expect_err("union-bearing struct values should remain outside this slice");

    assert!(error.message().contains(
        "int16, int32, uint8, uint16, uint32, int64, uint64, named enum fields, fixed scalar arrays, fixed-dimensional embedded-struct arrays, data-pointer fields, and embedded struct fields"
    ));
    assert!(
        error
            .message()
            .contains("contains a function pointer, an unsupported field shape, or a union field")
    );
}

#[test]
fn c0_rejects_unsupported_designated_struct_initializer_forms() {
    for source in [
        r#"
        struct packet {
            int32 value;
        };

        struct packet packet = {.value = 1};

        int32 read() {
            return packet.value;
        }
        "#,
        r#"
        struct packet {
            int32 value;
        };

        int32 read() {
            static struct packet packet = {.value = 1};
            return packet.value;
        }
        "#,
    ] {
        let error = syntax::parse_functions(source)
            .expect_err("static and file-scope designated initializers remain unsupported");
        assert_eq!(
            error.message(),
            "designated aggregate initializers are not supported"
        );
    }
}

#[test]
fn c0_struct_values_preserve_inline_array_layout_metadata() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            int32 values[2];
            uint8 bytes[3];
        };

        struct packet identity(struct packet value) {
            return value;
        }
        "#,
    )
    .expect("inline scalar arrays should be allowed in struct values");

    let packet = function.structs().get("packet").expect("packet layout");
    assert_eq!(packet.field("tag").unwrap().offset_bytes(), 0);
    assert_eq!(packet.field("values").unwrap().offset_bytes(), 4);
    assert_eq!(
        packet.field("values").unwrap().c_type(),
        syntax::C0Type::Int32Array(2)
    );
    assert_eq!(packet.field("bytes").unwrap().offset_bytes(), 12);
    assert_eq!(
        packet.field("bytes").unwrap().c_type(),
        syntax::C0Type::UInt8Array(3)
    );
    assert_eq!(packet.size_bytes(), 16);

    let kernel_function = function.to_kernel_function();
    let layout = kernel_function.parameters()[0]
        .aggregate_layout()
        .expect("array struct parameter layout");
    let values = layout
        .fields()
        .iter()
        .find(|field| field.name() == "values")
        .expect("values field in kernel layout");
    assert_eq!(values.offset_bytes(), 4);
    assert_eq!(values.c_type(), crate::kernel::CType::Int32Array(2));
    let bytes = layout
        .fields()
        .iter()
        .find(|field| field.name() == "bytes")
        .expect("bytes field in kernel layout");
    assert_eq!(bytes.offset_bytes(), 12);
    assert_eq!(bytes.c_type(), crate::kernel::CType::UInt8Array(3));
}

#[test]
fn c0_scalar_struct_values_allow_named_enum_fields() {
    let function = syntax::parse_function(
        r#"
        enum packet_state {
            PACKET_READY = 7,
            PACKET_DONE = 9,
        };

        struct packet {
            int32 count;
            enum packet_state state;
            uint8 tag;
        };

        struct packet finish(struct packet value) {
            value.count = 5;
            value.state = PACKET_DONE;
            return value;
        }
        "#,
    )
    .expect("enum fields should be allowed in struct values");

    let field = function
        .structs()
        .get("packet")
        .and_then(|layout| layout.field("state"))
        .expect("enum field metadata");
    assert_eq!(field.c_type(), syntax::C0Type::Int32);
    assert_eq!(field.enum_name(), Some("packet_state"));

    let kernel = function.to_kernel_function();
    let layout = kernel.parameters()[0]
        .aggregate_layout()
        .expect("enum struct parameter layout");
    let state = layout
        .fields()
        .iter()
        .find(|field| field.name() == "state")
        .expect("enum field in kernel layout");
    assert_eq!(state.offset_bytes(), 4);
    assert_eq!(state.c_type(), crate::kernel::CType::Int32);
}

#[test]
fn c0_struct_layout_preserves_inline_scalar_array_shape() {
    #[repr(C)]
    struct HostPacket {
        buf: [u8; 16],
        values: [i32; 2],
        count: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 buf[16];
            int32 values[2];
            int32 count;
        };

        int32 read_packet(struct packet* packet) {
            return packet->buf[2] + packet->count;
        }
        "#,
    )
    .expect("inline scalar array fields should parse");
    let layout = function.structs().get("packet").expect("packet layout");

    assert_eq!(
        layout.field("buf").unwrap().c_type(),
        syntax::C0Type::UInt8Array(16)
    );
    assert_eq!(
        layout.field("buf").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, buf)
    );
    assert_eq!(
        layout.field("values").unwrap().c_type(),
        syntax::C0Type::Int32Array(2)
    );
    assert_eq!(
        layout.field("values").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, values)
    );
    assert_eq!(
        layout.field("count").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, count)
    );
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        layout.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );
}

#[test]
fn c0_struct_layout_preserves_multidimensional_scalar_array_shape() {
    #[repr(C)]
    struct HostPacket {
        tag: u8,
        values: [[i32; 3]; 2],
        bytes: [[u8; 2]; 3],
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            int32 values[2][3];
            uint8 bytes[3][2];
            int32 tail;
        };

        int32 read_packet(struct packet* packet) {
            return packet->values[1][2] + packet->bytes[2][1] + packet->tail;
        }
        "#,
    )
    .expect("multidimensional inline scalar array fields should parse");
    let layout = function.structs().get("packet").expect("packet layout");

    let values = layout.field("values").expect("values field");
    assert_eq!(values.c_type(), syntax::C0Type::Int32Array(6));
    assert_eq!(values.array_shape(), Some(&[2, 3][..]));
    assert_eq!(values.byte_width(), 24);
    assert_eq!(
        values.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, values)
    );

    let bytes = layout.field("bytes").expect("bytes field");
    assert_eq!(bytes.c_type(), syntax::C0Type::UInt8Array(6));
    assert_eq!(bytes.array_shape(), Some(&[3, 2][..]));
    assert_eq!(bytes.byte_width(), 6);
    assert_eq!(
        bytes.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, bytes)
    );
    assert_eq!(
        layout.field("tail").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, tail)
    );
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        layout.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );
}

#[test]
fn c0_struct_inline_scalar_array_field_supports_indexed_load_and_store() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 buf[16];
        };

        uint8 write_packet(struct packet* packet) {
            packet->buf[2] = 7;
            return packet->buf[2];
        }
        "#,
    )
    .expect("indexed inline scalar array access should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 4);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 16))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("packet", 16)
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(2),
                    },
                    crate::kernel::uint8(7),
                ),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("indexed inline scalar array access should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::uint8(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_struct_multidimensional_scalar_array_field_flattens_row_major() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            int32 values[2][3];
        };

        int32 write_packet(struct packet* packet) {
            packet->values[1][2] = 7;
            return packet->values[1][2];
        }
        "#,
    )
    .expect("multidimensional indexed scalar array access should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 10);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 28))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("packet", 28)
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(24),
                    },
                    crate::kernel::int32(7),
                ),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("multidimensional indexed scalar array access should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_struct_scalar_array_element_address_preserves_row_major_offset() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            int32 values[2][3];
        };

        int32* address_value(struct packet* packet) {
            return &packet->values[1][2];
        }
        "#,
    )
    .expect("address of an inline scalar array element should parse");

    let syntax::C0Statement::Return(syntax::C0Expression::AddressOf(target)) = function.body()
    else {
        panic!("array element address should remain an address-of lvalue")
    };
    let syntax::C0Expression::Index(base, index) = target.as_ref() else {
        panic!("array element address should target an indexed lvalue")
    };
    assert!(matches!(
        base.as_ref(),
        syntax::C0Expression::Field {
            field_type: syntax::C0Type::Int32Array(6),
            array_shape: Some(shape),
            ..
        } if shape == &[2, 3]
    ));
    assert!(matches!(
        index.as_ref(),
        syntax::C0Expression::Add(left, right)
            if matches!(left.as_ref(), syntax::C0Expression::Multiply(multiplier, stride)
                if matches!(multiplier.as_ref(), syntax::C0Expression::Int32Literal(1))
                    && matches!(stride.as_ref(), syntax::C0Expression::Int32Literal(3)))
                && matches!(right.as_ref(), syntax::C0Expression::Int32Literal(2))
    ));

    let crate::kernel::CStatement::Return(crate::kernel::CExpression::AddressOf(target)) =
        function.body_kernel_statement()
    else {
        panic!("array element address should lower to kernel address-of")
    };
    let crate::kernel::CExpression::Index(base, index) = target.as_ref() else {
        panic!("array element address should preserve indexed lvalue lowering")
    };
    assert!(matches!(
        base.as_ref(),
        crate::kernel::CExpression::TypedLoad {
            value_type: crate::kernel::CType::Int32Array(6),
            ..
        }
    ));
    assert!(matches!(
        index.as_ref(),
        crate::kernel::CExpression::Add(left, right)
            if matches!(left.as_ref(), crate::kernel::CExpression::Multiply(multiplier, stride)
                if matches!(multiplier.as_ref(), crate::kernel::CExpression::Value(value)
                    if value == &crate::kernel::int32(1))
                    && matches!(stride.as_ref(), crate::kernel::CExpression::Value(value)
                        if value == &crate::kernel::int32(3)))
                && matches!(right.as_ref(), crate::kernel::CExpression::Value(value)
                    if value == &crate::kernel::int32(2))
    ));
}

#[test]
fn c0_struct_scalar_array_element_address_executes_at_element_width() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            int32 values[2][3];
        };

        int32 update_value(struct packet* packet) {
            int32* value_pointer;
            value_pointer = &packet->values[1][2];
            *value_pointer = 7;
            return packet->values[1][2];
        }
        "#,
    )
    .expect("address of an inline scalar array element should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let value = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(24),
    };
    let local_value_pointer = crate::kernel::Pointer {
        block: "local:value_pointer".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 10);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 28))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("local:value_pointer", 8)
                .with_block("packet", 28)
                .store(
                    local_value_pointer,
                    crate::kernel::CValue::pointer(value.clone()),
                )
                .store(value, crate::kernel::int32(7)),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("address of an inline scalar array element should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_struct_byte_array_element_address_executes_at_byte_width() {
    let function = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            uint8 bytes[3][2];
        };

        uint8 update_byte(struct packet* packet) {
            uint8* byte_pointer;
            byte_pointer = &packet->bytes[2][1];
            *byte_pointer = 9;
            return packet->bytes[2][1];
        }
        "#,
    )
    .expect("address of an inline byte array element should parse")
    .to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let byte = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(6),
    };
    let local_byte_pointer = crate::kernel::Pointer {
        block: "local:byte_pointer".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 2);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 8))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("local:byte_pointer", 8)
                .with_block("packet", 8)
                .store(
                    local_byte_pointer,
                    crate::kernel::CValue::typed_pointer(
                        byte.clone(),
                        crate::kernel::CType::UInt8Pointer,
                    ),
                )
                .store(byte, crate::kernel::uint8(9)),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("address of an inline byte array element should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::uint8(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_embedded_struct_array_field_preserves_stride_and_accesses_leaf() {
    #[repr(C)]
    struct HostInner {
        value: i32,
        flag: u8,
    }

    #[repr(C)]
    struct HostPacket {
        tag: u8,
        points: [HostInner; 2],
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
            uint8 flag;
        };
        struct packet {
            uint8 tag;
            struct inner points[2];
            int32 tail;
        };

        int32 write_point(struct packet* packet) {
            packet->points[1].value = 7;
            return packet->points[1].value;
        }
        "#,
    )
    .expect("one-dimensional arrays of embedded structs should parse");

    let packet_layout = function.structs().get("packet").expect("packet layout");
    let points = packet_layout
        .field("points")
        .expect("embedded struct array field");
    assert_eq!(points.c_type(), syntax::C0Type::UInt8Array(16));
    assert_eq!(points.struct_name(), Some("inner"));
    assert_eq!(points.array_element_width(), Some(8));
    assert_eq!(points.byte_width(), 16);
    assert_eq!(
        points.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, points)
    );
    assert_eq!(
        packet_layout.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        packet_layout.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );

    let function = function.to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 6);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 24))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("packet", 24)
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(12),
                    },
                    crate::kernel::int32(7),
                ),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("indexed embedded struct fields should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_multidimensional_embedded_struct_array_preserves_row_major_stride() {
    #[repr(C)]
    struct HostInner {
        value: i32,
        flag: u8,
    }

    #[repr(C)]
    struct HostPacket {
        tag: u8,
        points: [[HostInner; 2]; 2],
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            int32 value;
            uint8 flag;
        };
        struct packet {
            uint8 tag;
            struct inner points[2][2];
            int32 tail;
        };

        int32 read_point(struct packet* packet) {
            packet->points[1][1].value = 7;
            return packet->points[1][1].value;
        }
        "#,
    )
    .expect("multidimensional arrays of embedded structs should parse");

    let packet_layout = function.structs().get("packet").expect("packet layout");
    let points = packet_layout
        .field("points")
        .expect("embedded struct array field");
    assert_eq!(points.c_type(), syntax::C0Type::UInt8Array(32));
    assert_eq!(points.struct_name(), Some("inner"));
    assert_eq!(points.array_element_width(), Some(8));
    assert_eq!(points.array_shape(), Some(&[2, 2][..]));
    assert_eq!(points.byte_width(), 32);
    assert_eq!(
        points.offset_bytes() as usize,
        std::mem::offset_of!(HostPacket, points)
    );
    assert_eq!(
        packet_layout.size_bytes() as usize,
        std::mem::size_of::<HostPacket>()
    );
    assert_eq!(
        packet_layout.alignment_bytes() as usize,
        std::mem::align_of::<HostPacket>()
    );

    let function = function.to_kernel_function();
    let packet = crate::kernel::Pointer {
        block: "packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let resources = own_memory_context(packet.clone(), 0, 10);
    let state = crate::kernel::CState::new()
        .with_memory(crate::kernel::CMemory::new().with_block("packet", 40))
        .with_resource_context(resources.clone());
    let final_state = crate::kernel::CState::new()
        .with_memory(
            crate::kernel::CMemory::new()
                .with_block("packet", 40)
                .store(
                    crate::kernel::Pointer {
                        block: "packet".into(),
                        offset: crate::kernel::PointerOffsetTerm::Constant(28),
                    },
                    crate::kernel::int32(7),
                ),
        )
        .with_resource_context(resources);
    let arguments = vec![crate::kernel::c_pointer_value(packet)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("multidimensional embedded struct fields should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(7),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_lp64_layout_matches_the_host_c_abi() {
    #[repr(C)]
    struct HostMixed {
        tag: i32,
        data: *mut i32,
        length: i32,
    }

    assert_eq!(
        std::mem::size_of::<*mut i32>(),
        8,
        "this cross-check requires an LP64 host"
    );
    let function = syntax::parse_function(
        r#"
        struct mixed {
            int32 tag;
            int32* data;
            int32 length;
        };

        int32 read_tag(struct mixed* value) {
            return value->tag;
        }
        "#,
    )
    .expect("LP64 struct should parse");
    let layout = function.structs().get("mixed").expect("mixed layout");

    assert_eq!(
        layout.field("tag").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostMixed, tag)
    );
    assert_eq!(
        layout.field("data").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostMixed, data)
    );
    assert_eq!(
        layout.field("length").unwrap().offset_bytes() as usize,
        std::mem::offset_of!(HostMixed, length)
    );
    assert_eq!(
        layout.size_bytes() as usize,
        std::mem::size_of::<HostMixed>()
    );
    assert_eq!(
        layout.alignment_bytes() as usize,
        std::mem::align_of::<HostMixed>()
    );
}

#[test]
fn c0_struct_field_lowering_uses_explicit_byte_offsets() {
    let function = syntax::parse_function(
        r#"
        struct mixed {
            int32 tag;
            int32* data;
        };

        int32* get_data(struct mixed* value) {
            return value->data;
        }
        "#,
    )
    .expect("mixed struct getter should parse");
    let syntax::C0Statement::Return(syntax::C0Expression::Field { pointer, .. }) = function.body()
    else {
        panic!("getter should return a field load")
    };
    assert!(matches!(
        pointer.as_ref(),
        syntax::C0Expression::PointerOffsetBytes { bytes: 8, .. }
    ));
    let crate::kernel::CStatement::Return(crate::kernel::CExpression::TypedLoad {
        pointer,
        value_type: crate::kernel::CType::Int32Pointer,
    }) = function.body_kernel_statement()
    else {
        panic!("field load should retain its value type")
    };
    assert!(matches!(
        pointer.as_ref(),
        crate::kernel::CExpression::PointerOffsetBytes { bytes: 8, .. }
    ));
}

#[test]
fn c0_struct_field_address_lowering_preserves_nested_byte_offset() {
    #[repr(C)]
    struct HostInner {
        flag: u8,
        value: i32,
    }

    #[repr(C)]
    struct HostOuter {
        tag: u8,
        inner: HostInner,
        tail: i32,
    }

    let function = syntax::parse_function(
        r#"
        struct inner {
            uint8 flag;
            int32 value;
        };
        struct outer {
            uint8 tag;
            struct inner inner;
            int32 tail;
        };

        int32* address_nested(struct outer* packet) {
            return &packet->inner.value;
        }
        "#,
    )
    .expect("nested scalar field address should parse");

    assert_eq!(
        function.structs()["outer"]
            .field("inner")
            .unwrap()
            .offset_bytes() as usize,
        std::mem::offset_of!(HostOuter, inner)
    );
    assert_eq!(
        function.structs()["inner"]
            .field("value")
            .unwrap()
            .offset_bytes() as usize,
        std::mem::offset_of!(HostInner, value)
    );

    let syntax::C0Statement::Return(syntax::C0Expression::AddressOf(target)) = function.body()
    else {
        panic!("nested field address should remain an address-of lvalue")
    };
    let syntax::C0Expression::Field {
        pointer,
        field_type,
        ..
    } = target.as_ref()
    else {
        panic!("nested field address should target the scalar field")
    };
    assert_eq!(*field_type, syntax::C0Type::Int32);
    let syntax::C0Expression::PointerOffsetBytes {
        pointer: inner_pointer,
        bytes: inner_offset,
    } = pointer.as_ref()
    else {
        panic!("nested field address should include the inner field offset")
    };
    assert_eq!(*inner_offset, std::mem::offset_of!(HostInner, value) as u32);
    assert!(matches!(
        inner_pointer.as_ref(),
        syntax::C0Expression::PointerOffsetBytes { bytes, .. }
            if *bytes == std::mem::offset_of!(HostOuter, inner) as u32
    ));

    let crate::kernel::CStatement::Return(crate::kernel::CExpression::AddressOf(target)) =
        function.body_kernel_statement()
    else {
        panic!("nested field address should lower to kernel address-of")
    };
    let crate::kernel::CExpression::TypedLoad {
        pointer,
        value_type: crate::kernel::CType::Int32,
    } = target.as_ref()
    else {
        panic!("nested field address should preserve the leaf load type")
    };
    let crate::kernel::CExpression::PointerOffsetBytes {
        pointer: inner_pointer,
        bytes: inner_offset,
    } = pointer.as_ref()
    else {
        panic!("nested field address should include the inner field offset")
    };
    assert_eq!(*inner_offset, std::mem::offset_of!(HostInner, value) as u32);
    assert!(matches!(
        inner_pointer.as_ref(),
        crate::kernel::CExpression::PointerOffsetBytes { bytes, .. }
            if *bytes == std::mem::offset_of!(HostOuter, inner) as u32
    ));
}

#[test]
fn c0_address_of_int16_preserves_pointer_type() {
    let function = syntax::parse_function(
        r#"
        int16* address_short() {
            int16 value;
            value = 7;
            return &value;
        }
        "#,
    )
    .expect("address-of an int16 local should parse before execution")
    .to_kernel_function();

    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        crate::kernel::CState::new(),
        function.clone(),
        Vec::new(),
        Default::default(),
    )
    .expect("an int16 address should execute with its typed pointer result");
    let crate::kernel::Proposition::CFunctionExecutes {
        outcome: crate::kernel::CFunctionOutcome::Return { value, .. },
        ..
    } = theorem.proposition()
    else {
        panic!("an int16 address should return a typed pointer")
    };
    assert_eq!(value.c_type(), crate::kernel::CType::Int16Pointer);
}

#[test]
fn c0_syntax_rejects_assignment_to_local_array_object() {
    let function = syntax::parse_function(
        r#"
        int32 bad_assign(int32* p) {
            int32 a[3];
            a = p;
            return 0;
        }
        "#,
    )
    .expect("array assignment function should parse")
    .to_kernel_function();

    let pointer = crate::kernel::Pointer {
        block: "block".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_pointer_value(pointer)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("array assignment should execute to a type error");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::RuntimeError(
                crate::kernel::CRuntimeError::TypeMismatch
            ),
        }
    );
}

#[test]
fn c0_syntax_targets_kernel_int32_subtraction_and_comparisons() {
    let function = syntax::parse_function(
        r#"
        int32 adjust(int32 x) {
            if (x >= 3) {
                return x - 1;
            } else {
                if (x == 0) {
                    return x + 2;
                } else {
                    return x + 1;
                }
            }
        }
        "#,
    )
    .expect("int32 operator function should parse")
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_int32_literal(4)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("parsed int32 operator function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(3),
                state,
            },
        }
    );
}

#[test]
fn c0_if_condition_uses_c_int32_truthiness() {
    let function = syntax::parse_function(
        r#"
        int32 truthy(int32 x) {
            if (x) {
                return 1;
            } else {
                return 0;
            }
        }
        "#,
    )
    .expect("truthiness function should parse")
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_int32_literal(7)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("nonzero int32 condition should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function: function.clone(),
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(1),
                state: state.clone(),
            },
        }
    );

    let arguments = vec![crate::kernel::c_int32_literal(0)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("zero int32 condition should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(0),
                state,
            },
        }
    );
}

#[test]
fn c0_clamp_demo_proves_symbolic_branch_specifications() {
    let function = syntax::parse_function(
        r#"
        int32 clamp(int32 x, int32 lo, int32 hi) {
            if (x < lo) {
                return lo;
            } else {
                if (x > hi) {
                    return hi;
                } else {
                    return x;
                }
            }
        }
        "#,
    )
    .expect("clamp should parse")
    .to_kernel_function();

    let x = crate::kernel::Variable(40);
    let lo = crate::kernel::Variable(41);
    let hi = crate::kernel::Variable(42);
    let x_bits = crate::kernel::Bitvector32Term::Variable(x);
    let lo_bits = crate::kernel::Bitvector32Term::Variable(lo);
    let hi_bits = crate::kernel::Bitvector32Term::Variable(hi);
    let arguments = vec![
        crate::kernel::CExpression::Value(crate::kernel::int32(x_bits.clone())),
        crate::kernel::CExpression::Value(crate::kernel::int32(lo_bits.clone())),
        crate::kernel::CExpression::Value(crate::kernel::int32(hi_bits.clone())),
    ];
    let below_lo = crate::kernel::ConditionTerm::Bitvector32SignedLessThan(
        Box::new(x_bits.clone()),
        Box::new(lo_bits.clone()),
    );
    let above_hi = crate::kernel::ConditionTerm::Bitvector32SignedGreaterThan(
        Box::new(x_bits.clone()),
        Box::new(hi_bits.clone()),
    );
    let cases = vec![
        (
            vec![crate::kernel::Proposition::ConditionIs(
                below_lo.clone(),
                true,
            )],
            crate::kernel::int32(lo_bits),
        ),
        (
            vec![
                crate::kernel::Proposition::ConditionIs(below_lo.clone(), false),
                crate::kernel::Proposition::ConditionIs(above_hi.clone(), true),
            ],
            crate::kernel::int32(hi_bits),
        ),
        (
            vec![
                crate::kernel::Proposition::ConditionIs(below_lo, false),
                crate::kernel::Proposition::ConditionIs(above_hi, false),
            ],
            crate::kernel::int32(x_bits),
        ),
    ];

    for (requires, value) in cases {
        let specification = crate::kernel::c_function_specification(
            crate::kernel::CState::new(),
            arguments.clone(),
            requires.clone(),
            crate::kernel::CFunctionOutcome::Return {
                value,
                state: crate::kernel::CState::new(),
            },
        );
        let theorem = crate::kernel::prove_c_function_satisfies_specification(
            function.clone(),
            specification.clone(),
            crate::kernel::PureFactContext::new(),
        )
        .expect("clamp branch specification should prove");
        let expected = requires.iter().rev().fold(
            crate::kernel::Proposition::CFunctionSatisfiesSpecification {
                function: function.clone(),
                specification: specification.clone(),
            },
            |body, requirement| {
                crate::kernel::Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
            },
        );

        assert_eq!(theorem.proposition(), &expected);
    }
}

#[test]
fn c0_equality_binds_looser_than_relational_comparison() {
    let mixed = syntax::parse_function(
        r#"
        int32 mixed(int32 a, int32 b, int32 c) {
            return a == b < c;
        }
        "#,
    )
    .expect("a mixed equality and relational chain should parse");
    assert!(matches!(
        mixed.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Equal(left, right))
            if matches!(left.as_ref(), syntax::C0Expression::Variable(name) if name == "a")
                && matches!(right.as_ref(), syntax::C0Expression::LessThan(_, _))
    ));

    let paired = syntax::parse_function(
        r#"
        int32 paired(int32 a, int32 b, int32 c, int32 d) {
            return a < b == c < d;
        }
        "#,
    )
    .expect("relational operands on both sides of `==` should parse");
    assert!(matches!(
        paired.body(),
        syntax::C0Statement::Return(syntax::C0Expression::Equal(left, right))
            if matches!(left.as_ref(), syntax::C0Expression::LessThan(_, _))
                && matches!(right.as_ref(), syntax::C0Expression::LessThan(_, _))
    ));
}

#[test]
fn c0_syntax_accepts_a_declaration_that_shadows_an_enclosing_local() {
    let function = syntax::parse_function(
        r#"
        int32 shadow(int32 c) {
            int32 y = 10;
            if (c < 0) { int32 y = 5; } else { int32 y = 5; }
            return y;
        }
        "#,
    )
    .expect("an inner `int32 y` gets a distinct kernel identity");
    assert!(
        format!("{:?}", function.body()).contains("y#scope0"),
        "the shadowed declaration should be renamed in the lowered C0 body"
    );
    assert!(
        format!("{:?}", function.body()).contains("y#scope1"),
        "sibling shadowed declarations should receive distinct identities"
    );
}

#[test]
fn c0_syntax_accepts_a_declaration_that_shadows_a_parameter() {
    let function = syntax::parse_function(
        r#"
        struct S { int32 a; int32 b; };
        struct T { int32 b; int32 z; };
        int32 pick2(struct S* p, struct T* q, int32 c) {
            if (c < 0) { struct T *p = q; p->b = 1; }
            return p->b;
        }
        "#,
    )
    .expect("an inner `struct T *p` gets a distinct kernel identity");
    assert!(
        format!("{:?}", function.body()).contains("p#scope0"),
        "the shadowed pointer declaration should be renamed in the lowered C0 body"
    );
}

#[test]
fn c0_syntax_accepts_sibling_scopes_reusing_a_name() {
    // `q->z` exists only in `T` and `q->a` only in `S`: the second arm parses
    // only if the first arm's struct binding for `q` ended with its block.
    syntax::parse_function(
        r#"
        struct S { int32 a; int32 b; };
        struct T { int32 b; int32 z; };
        int32 siblings(struct S* s, struct T* t, int32 c) {
            int32 r;
            if (c < 0) { int32 v = 1; r = v; } else { int32 v = 2; r = v; }
            for (int32 i = 0; i < 2; i++) { r = r + i; }
            for (int32 i = 0; i < 2; i++) { r = r + i; }
            if (c < 0) { struct T *q = t; r = q->z; } else { struct S *q = s; r = q->a; }
            return r;
        }
        "#,
    )
    .expect("names reused in sibling scopes are distinct objects");
}

#[test]
fn c0_syntax_accepts_else_if_and_unbraced_controlled_statements() {
    let function = syntax::parse_function(
        r#"
        int32 classify(int32 x) {
            if (x < 0)
                return -1;
            else if (x == 0)
                return 0;
            else
                return 1;
        }
        "#,
    )
    .expect("else-if arms may contain one unbraced statement");
    assert!(matches!(
        function.body(),
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } if matches!(then_branch.as_ref(), syntax::C0Statement::Return(_))
            && matches!(else_branch.as_ref(), syntax::C0Statement::If { .. })
    ));

    syntax::parse_function(
        r#"
        int32 advance(int32 n) {
            int32 i = 0;
            while (i < n)
                i = i + 1;
            for (int32 j = 0; j < 2; j++)
                i = i + j;
            return i;
        }
        "#,
    )
    .expect("while and for may control one unbraced statement");
}

#[test]
fn c0_syntax_rejects_a_declaration_as_an_unbraced_controlled_statement() {
    let error = syntax::parse_function(
        r#"
        int32 invalid(int32 condition) {
            if (condition)
                int32 value;
            return 0;
        }
        "#,
    )
    .expect_err("C declarations need a compound statement body");
    assert!(
        error
            .message()
            .contains("declaration controlled by `if` must be enclosed in braces"),
        "{}",
        error.message()
    );
}

#[test]
fn c0_syntax_targets_kernel_known_function_call_assignment() {
    let increment = syntax::parse_function(
        r#"
        int32 increment(int32 x) {
            return x + 1;
        }
        "#,
    )
    .expect("increment function should parse")
    .to_kernel_function();
    let caller = syntax::parse_function(
        r#"
        int32 caller() {
            int32 result;
            result = increment(41);
            return result;
        }
        "#,
    )
    .expect("caller function should parse")
    .to_kernel_function();

    let local_pointer = crate::kernel::Pointer {
        block: "local:result".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let environment = crate::kernel::CExecutionEnvironment::new().with_function(increment);
    let state = crate::kernel::CState::new();
    let final_state = crate::kernel::CState::new().with_memory(
        crate::kernel::CMemory::new()
            .with_block("local:result", 4)
            .store(local_pointer, crate::kernel::int32(42)),
    );
    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        environment,
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("known C0 function call should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(42),
                state: final_state,
            },
        }
    );
}

#[test]
fn c0_syntax_lowers_calls_in_expression_position() {
    let function = syntax::parse_function(
        r#"
        int32 caller(int32 x) {
            int32 result = increment(x) + 1;
            result = increment(result) + 1;
            if (increment(x) > 0)
                return increment(increment(x)) + 1;
            return values[index_of(x)];
        }
        "#,
    )
    .expect("calls should be accepted wherever an unconditional expression is expected");
    let debug = format!("{:?}", function.body());
    assert!(
        debug.contains("CallAssign"),
        "calls lower to call statements"
    );
    assert!(
        debug.contains("__click_call_result0"),
        "lowering uses a kernel-local temporary"
    );
    assert!(
        !debug.contains("Call {"),
        "the lowered C0 body contains no expression-level call nodes"
    );
}

#[test]
fn c0_syntax_lowers_calls_in_conditional_expression_branches() {
    let function = syntax::parse_function(
        r#"
        int32 caller(int32 condition) {
            return condition ? increment(0) : 0;
        }
        "#,
    )
    .expect("calls in conditional branches should be lowered lazily");
    let debug = format!("{:?}", function.body());
    assert!(debug.contains("If {"), "conditional branches become a C if");
    assert!(debug.contains("CallAssign"), "the selected call is checked");
    assert!(
        !debug.contains("Conditional {"),
        "the lowered body does not evaluate conditional call branches eagerly"
    );
    assert!(
        debug.contains("Declare { c_type: Int32"),
        "the conditional result has a stack binding before either arm"
    );
}

#[test]
fn c0_syntax_lowers_aggregate_conditional_call_argument() {
    let functions = syntax::parse_functions(
        r#"
        struct inner { int32 value; uint8 enabled; };
        struct packet { uint8 tag; struct inner inner; int32 tail; };
        int32 sum_packet(struct packet packet) {
            return packet.tag + packet.inner.value + packet.inner.enabled + packet.tail;
        }
        int32 caller() {
            struct packet left = {3, {4, 1}, 5};
            struct packet right = {20, {30, 2}, 40};
            int32 result = sum_packet(0 ? left : right);
            return result;
        }
        "#,
    )
    .expect("aggregate conditional input parses");
    let caller = functions
        .iter()
        .find(|function| function.name() == "caller")
        .expect("caller");
    let debug = format!("{:?}", caller.body());
    assert!(debug.contains("DeclareStructValue"));
    assert!(debug.contains("If {"));
    assert!(debug.contains("CallAssign"));
    assert!(!debug.contains("Conditional {"));
}

#[test]
fn c0_syntax_lowers_calls_in_reevaluated_loop_conditions() {
    let function = syntax::parse_function(
        r#"
        int32 caller() {
            do {
                continue;
            } while (should_continue());
            while (should_continue()) {
                break;
            }
            for (; should_continue();) {
                break;
            }
            return 0;
        }
        "#,
    )
    .expect("calls in loop conditions should be reevaluated in the loop body");
    let debug = format!("{:?}", function.body());
    assert!(
        debug.matches("CallAssign").count() >= 3,
        "each loop iteration has a checked condition call"
    );
    assert!(
        debug.matches("Int32Literal(1)").count() >= 3,
        "all call-bearing loop conditions become unconditional iteration shells"
    );
    assert!(
        !debug.contains("DoWhile"),
        "do-while conditions move their checked call into the loop body"
    );
}

#[test]
fn c0_syntax_rejects_multiple_unsequenced_expression_calls() {
    let error = syntax::parse_function(
        r#"
        int32 caller(int32 x) {
            return increment(x) + increment(x);
        }
        "#,
    )
    .expect_err("C does not specify the relative order of these calls");
    assert!(
        error
            .message()
            .contains("multiple unsequenced calls in one expression"),
        "{}",
        error.message()
    );
}

#[test]
fn c0_function_pointers_preserve_signature_and_dispatch_callback() {
    let callback =
        syntax::parse_function("int32 compare(int32 left, int32 right) { return left - right; }")
            .expect("callback should parse")
            .to_kernel_function();
    let apply = syntax::parse_function(
        "int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {\
             int32 result; result = callback(left, right); return result;\
         }",
    )
    .expect("callback parameter and indirect call should parse")
    .to_kernel_function();
    let caller = syntax::parse_function(
        "int32 caller() { int32 result; result = apply(&compare, 40, 2); return result; }",
    )
    .expect("function address should parse")
    .to_kernel_function();

    assert!(matches!(
        apply.parameters()[0].c_type(),
        crate::kernel::CType::FunctionPointer(_)
    ));

    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        crate::kernel::CState::new(),
        caller.clone(),
        Vec::new(),
        Default::default(),
        crate::kernel::CExecutionEnvironment::new()
            .with_function(callback)
            .with_function(apply),
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("compatible callback should execute");
    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state: crate::kernel::CState::new(),
            function: caller,
            arguments: Vec::new(),
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(38),
                state: crate::kernel::CState::new().with_memory(
                    crate::kernel::CMemory::new()
                        .with_block("local:result", 4)
                        .store(
                            crate::kernel::Pointer {
                                block: "local:result".into(),
                                offset: crate::kernel::PointerOffsetTerm::Constant(0),
                            },
                            crate::kernel::int32(38),
                        )
                ),
            },
        }
    );
}

#[test]
fn c0_function_pointers_reject_incompatible_callback_targets() {
    let wrong =
        syntax::parse_function("uint8 wrong(uint8 left, uint8 right) { return left - right; }")
            .expect("incompatible callback should parse")
            .to_kernel_function();
    let apply = syntax::parse_function(
        "int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {\
             int32 result; result = callback(left, right); return result;\
         }",
    )
    .expect("callback parameter and indirect call should parse")
    .to_kernel_function();
    let caller = syntax::parse_function(
        "int32 caller() { int32 result; result = apply(&wrong, 40, 2); return result; }",
    )
    .expect("function address should parse")
    .to_kernel_function();

    let theorem = crate::kernel::prove_symbolic_c_function_execution_with_environment(
        crate::kernel::CState::new(),
        caller,
        Vec::new(),
        Default::default(),
        crate::kernel::CExecutionEnvironment::new()
            .with_function(wrong)
            .with_function(apply),
        crate::kernel::CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("incompatible callback should produce a runtime-error theorem");
    let crate::kernel::Proposition::CFunctionExecutes {
        outcome:
            crate::kernel::CFunctionOutcome::RuntimeError(
                crate::kernel::CRuntimeError::FunctionContract(message),
            ),
        ..
    } = theorem.proposition()
    else {
        panic!("expected incompatible callback error, got {:#?}", theorem);
    };
    assert!(message.contains("incompatible signature"));
}

#[test]
fn c0_syntax_targets_kernel_while_countdown() {
    let function = syntax::parse_function(
        r#"
        int32 countdown(int32 x) {
            while (x > 0) {
                x = x - 1;
            }
            return x;
        }
        "#,
    )
    .expect("while countdown function should parse")
    .to_kernel_function();

    let state = crate::kernel::CState::new();
    let arguments = vec![crate::kernel::c_int32_literal(3)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("while countdown function should execute");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(0),
                state: crate::kernel::CState::new(),
            },
        }
    );
}

#[test]
fn c0_memory_safety_demo_fill_three_ints() {
    let function = syntax::parse_function(
        r#"
        int32 fill3(int32* p) {
            int32 i;
            i = 0;
            while (i < 3) {
                *(p + i) = i;
                i = i + 1;
            }
            return *(p + 2);
        }
        "#,
    )
    .expect("fill3 demo should parse")
    .to_kernel_function();

    let base = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let first = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let second = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(4),
    };
    let third = crate::kernel::Pointer {
        block: "buf".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(8),
    };
    let local_i = crate::kernel::Pointer {
        block: "local:i".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let initial_memory = crate::kernel::CMemory::new().with_block("buf", 12);
    let resources = own_memory_context(base.clone(), 0, 3);
    let state = crate::kernel::CState::new()
        .with_memory(initial_memory)
        .with_resource_context(resources.clone());
    let final_memory = crate::kernel::CMemory::new()
        .with_block("buf", 12)
        .with_block("local:i", 4)
        .store(first, crate::kernel::int32(0))
        .store(second, crate::kernel::int32(1))
        .store(third, crate::kernel::int32(2))
        .store(local_i, crate::kernel::int32(3));
    let arguments = vec![crate::kernel::c_pointer_value(base)];
    let theorem = crate::kernel::prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Default::default(),
    )
    .expect("fill3 should execute without memory obligations");

    assert_eq!(
        theorem.proposition(),
        &crate::kernel::Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: crate::kernel::CFunctionOutcome::Return {
                value: crate::kernel::int32(2),
                state: crate::kernel::CState::new()
                    .with_memory(final_memory)
                    .with_resource_context(resources),
            },
        }
    );
}

#[test]
fn c0_floating_point_storage_types_preserve_abi_layout() {
    let parsed = syntax::parse_function(
        r#"
        struct packet {
            uint8 tag;
            float value;
            double total;
            float samples[2];
            double wide_samples[2];
        };

        double identity(float input, double value) {
            float local;
            local = input;
            return value;
        }
        "#,
    )
    .expect("floating-point storage declarations should parse");
    let function = parsed.to_kernel_function();

    assert_eq!(function.return_type(), crate::kernel::CType::Float64);
    assert_eq!(
        function.parameters()[0].c_type(),
        crate::kernel::CType::Float32
    );
    assert_eq!(
        function.parameters()[1].c_type(),
        crate::kernel::CType::Float64
    );

    let layout = parsed.structs().get("packet").expect("packet layout");
    assert_eq!(layout.field("tag").unwrap().offset_bytes(), 0);
    assert_eq!(layout.field("value").unwrap().offset_bytes(), 4);
    assert_eq!(layout.field("value").unwrap().byte_width(), 4);
    assert_eq!(layout.field("total").unwrap().offset_bytes(), 8);
    assert_eq!(layout.field("total").unwrap().byte_width(), 8);
    assert_eq!(layout.field("samples").unwrap().offset_bytes(), 16);
    assert_eq!(layout.field("samples").unwrap().byte_width(), 8);
    assert_eq!(layout.field("wide_samples").unwrap().offset_bytes(), 24);
    assert_eq!(layout.field("wide_samples").unwrap().byte_width(), 16);
    assert_eq!(layout.alignment_bytes(), 8);
    assert_eq!(layout.size_bytes(), 40);
}

#[test]
fn c0_floating_point_literals_use_declared_binary_formats() {
    let single = syntax::parse_function("float single() { return 1.5f; }")
        .expect("binary32 literal should parse");
    assert_eq!(
        single.body(),
        &syntax::C0Statement::Return(syntax::C0Expression::Float32Literal(1.5f32.to_bits(),))
    );

    let double = syntax::parse_function("double double_value() { return 1.5; }")
        .expect("binary64 literal should parse");
    assert_eq!(
        double.body(),
        &syntax::C0Statement::Return(syntax::C0Expression::Float64Literal(1.5f64.to_bits(),))
    );

    let hex = syntax::parse_function("double hex() { return 0x1.0p0; }")
        .expect_err("hexadecimal floating-point literals must remain unsupported");
    assert!(
        hex.to_string()
            .contains("hexadecimal floating-point literals are not supported in C0")
    );

    let suffix = syntax::parse_function("double extended() { return 1.0L; }")
        .expect_err("long-double literal suffix must remain unsupported");
    assert!(
        suffix
            .to_string()
            .contains("long double literals are not modeled in C0")
    );
}

#[test]
fn c0_floating_point_storage_initializers_cover_static_local_arrays_and_calloc() {
    let functions = syntax::parse_functions(
        r#"
        float file_value = 1.5f;
        double file_zero;

        float load_storage() {
            static float stored = 2.5f;
            float local_values[2] = {1.5f};
            double wide_values[2] = {2.5};
            return stored;
        }

        float* allocate_storage() {
            float* values;
            values = calloc(2, sizeof(float));
            return values;
        }
        "#,
    )
    .expect("floating-point storage initializers should parse");

    let load = &functions[0];
    assert_eq!(
        load.globals()["file_value"].initializer(),
        Some(&syntax::C0Expression::Float32Literal(1.5f32.to_bits()))
    );
    assert_eq!(
        load.globals()["file_zero"].initializer(),
        Some(&syntax::C0Expression::Float64Literal(0))
    );
    let stored = load
        .static_locals()
        .values()
        .next()
        .expect("static floating-point local");
    assert_eq!(
        stored.initializer(),
        &syntax::C0Expression::Float32Literal(2.5f32.to_bits())
    );
    assert_eq!(
        load.to_kernel_function().static_variables()[0].initial_value(),
        &crate::kernel::CValue::Float32(
            crate::kernel::Bitvector32Term::Constant(2.5f32.to_bits(),)
        )
    );

    let allocate = functions
        .iter()
        .find(|function| function.name() == "allocate_storage")
        .expect("floating-point allocator function");
    assert_eq!(allocate.return_type(), syntax::C0Type::Float32Pointer);
    assert_eq!(
        allocate.to_kernel_function().return_type(),
        crate::kernel::CType::Float32Pointer
    );
}
