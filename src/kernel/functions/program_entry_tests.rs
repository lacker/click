use super::*;

fn storage_function(name: &str, globals: Vec<CGlobal>) -> CFunction {
    c_function(CType::Int32, name, vec![], c_return(c_int32_literal(0)))
        .with_global_variables(globals)
}

fn scalar_ownership(name: &str) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new(
        CMemory::global_pointer(name),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ))
}

#[test]
fn static_declaration_preserves_a_cell_materialized_before_its_block() {
    let function =
        storage_function("increment", vec![]).with_static_variables(vec![CStaticLocal::new(
            "calls",
            "calls",
            CType::Int32,
            int32(5),
        )]);
    let pointer = CMemory::static_pointer("increment", "calls");
    let state = CState::new().with_memory(CMemory::new().store(pointer.clone(), int32(37)));
    assert!(!state.memory().has_block(&pointer.block));
    let initialized = initialize_c_function_globals(&state, &function);
    assert!(initialized.memory().has_block(&pointer.block));
    assert_eq!(
        initialized.memory().load(&pointer),
        CExpressionOutcome::Value(int32(37))
    );
    assert!(initialized.resources().facts().is_empty());
}

#[test]
fn ordinary_function_entry_does_not_restore_static_initializers() {
    let global = CGlobal::new("state", CType::Int32, int32(7));
    let function =
        storage_function("read", vec![global]).with_static_variables(vec![CStaticLocal::new(
            "calls",
            "calls",
            CType::Int32,
            int32(11),
        )]);

    let ordinary = initialize_c_function_globals(&CState::new(), &function);
    assert!(
        ordinary
            .memory()
            .has_block(&CMemory::global_pointer("state").block)
    );
    assert_ne!(
        ordinary.memory().load(&CMemory::global_pointer("state")),
        CExpressionOutcome::Value(int32(7))
    );
    assert!(
        ordinary
            .memory()
            .has_block(&CMemory::static_pointer("read", "calls").block)
    );
    assert_ne!(
        ordinary
            .memory()
            .load(&CMemory::static_pointer("read", "calls")),
        CExpressionOutcome::Value(int32(11))
    );

    let startup = initialize_c_program_storage([function]).expect("no run limit is installed");
    assert_eq!(
        startup.memory().load(&CMemory::global_pointer("state")),
        CExpressionOutcome::Value(int32(7))
    );
    assert_eq!(
        startup
            .memory()
            .load(&CMemory::static_pointer("read", "calls")),
        CExpressionOutcome::Value(int32(11))
    );
}

#[test]
fn startup_coalesces_declarations_and_calls_cannot_replenish_ownership() {
    let global = CGlobal::new("state", CType::Int32, int32(7));
    let left = storage_function("left", vec![global.clone()]);
    let right = storage_function("right", vec![global]);
    let startup =
        initialize_c_program_storage([left.clone(), right]).expect("no run limit is installed");
    let owned = scalar_ownership("state");
    let assumptions = PureFactContext::new();
    assert_eq!(startup.resources().facts().len(), 1);
    assert!(startup.resources().satisfies_fact(&owned, &assumptions));
    assert!(
        !initialize_c_function_globals(&CState::new(), &left)
            .resources()
            .satisfies_fact(&owned, &assumptions)
    );
    let consumed = startup
        .resources()
        .clone()
        .without_fact(&owned, &assumptions)
        .unwrap();
    assert!(
        consumed
            .clone()
            .without_fact(&owned, &assumptions)
            .is_none()
    );
    let state = startup.with_resource_context(consumed).with_memory(
        initialize_c_function_globals(&CState::new(), &left)
            .memory()
            .clone()
            .store(CMemory::global_pointer("state"), int32(19)),
    );
    let call = initialize_c_function_globals(&state, &left);
    assert!(!call.resources().satisfies_fact(&owned, &assumptions));
    assert_eq!(
        call.memory().load(&CMemory::global_pointer("state")),
        CExpressionOutcome::Value(int32(19))
    );
}

#[test]
fn startup_preserves_private_identities_and_const_permissions() {
    let left = storage_function(
        "left",
        vec![CGlobal::new_with_kernel_name(
            "state",
            "left::state",
            CType::Int32,
            int32(7),
        )],
    );
    let right = storage_function(
        "right",
        vec![
            CGlobal::new_with_kernel_name("state", "right::state", CType::Int32, int32(40))
                .with_constant(true),
        ],
    );
    let state = initialize_c_program_storage([left, right]).expect("no run limit is installed");
    let assumptions = PureFactContext::new();
    assert_eq!(state.resources().facts().len(), 2);
    assert!(
        state
            .resources()
            .satisfies_fact(&scalar_ownership("left::state"), &assumptions)
    );
    let readonly = scalar_ownership("right::state");
    assert!(!state.resources().satisfies_fact(&readonly, &assumptions));
    assert!(state.resources().satisfies_fact(
        &CResourceFact::View(readonly.resource().clone()),
        &assumptions
    ));
    assert!(!state.locals().contains_name("state"));
}

#[test]
fn startup_permission_partition_visits_scale_with_cells_and_blocks() {
    for count in [16u32, 64, 256] {
        let mut memory = CMemory::new();
        for index in 0..count {
            let pointer = CMemory::global_pointer(&format!("state_{index}"));
            memory = memory
                .with_block(pointer.block.clone(), 4)
                .store(pointer, int32(7));
        }
        let mut visits = 0;
        let resources =
            initial_static_resources(&memory, || visits += 1).expect("no run limit is installed");
        assert_eq!(resources.facts().len(), count as usize);
        assert_eq!(visits, 4 * count);
    }
}

#[test]
fn startup_contract_cannot_be_packaged_as_an_ordinary_rule() {
    let function = storage_function("main", vec![])
        .with_program_entry()
        .with_contract(
            vec![],
            vec![],
            vec![],
            vec![CFunctionContractClaim::body_safety()],
            true,
        );
    assert!(c_recursive_function_contract_hypothesis(function.clone()).is_none());
    assert!(c_external_function_rule(function.clone()).is_none());
    assert!(c_verified_function_rule(function, &[]).is_none());
}

#[test]
fn binding_program_entry_does_not_upgrade_literal_views_to_ownership() {
    let function = storage_function("main", vec![])
        .with_string_literals(vec![CStringLiteral::new("text", vec![b'x', 0])])
        .with_program_entry();
    let startup =
        initialize_c_program_storage([function.clone()]).expect("no run limit is installed");
    let entry = initialize_c_function_globals(&startup, &function);
    assert_eq!(entry.resources().facts().len(), 1);
    assert!(entry.resources().facts()[0].is_view());
    let ordinary = initialize_c_function_globals(&CState::new(), &function);
    assert!(ordinary.resources().facts().is_empty());
}

#[test]
fn startup_includes_uncalled_local_statics_and_typed_arrays() {
    let left = storage_function("left", vec![]).with_static_variables(vec![CStaticLocal::new(
        "state",
        "state",
        CType::Int32,
        int32(3),
    )]);
    let right = storage_function("right", vec![]).with_static_variables(vec![CStaticLocal::new(
        "state",
        "state",
        CType::Int32,
        int32(5),
    )]);
    let array = storage_function("array", vec![]).with_global_arrays(vec![
        CGlobalArray::new_with_kernel_name(
            "values",
            "values",
            CType::UInt16,
            2,
            vec![uint16(7), uint16(9)],
        ),
    ]);
    let startup =
        initialize_c_program_storage([left, right, array]).expect("no run limit is installed");
    assert_eq!(startup.resources().facts().len(), 3);
    assert_eq!(
        startup
            .memory()
            .load(&CMemory::static_pointer("left", "state")),
        CExpressionOutcome::Value(int32(3))
    );
    assert_eq!(
        startup
            .memory()
            .load(&CMemory::static_pointer("right", "state")),
        CExpressionOutcome::Value(int32(5))
    );
    let owned = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        CMemory::global_pointer("values"),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
        2,
    ));
    assert!(
        startup
            .resources()
            .satisfies_fact(&owned, &PureFactContext::new())
    );
}

/// A zero of each global-array element type, for initializers the symbolic
/// entry below never reads.
fn zero_element(element_type: CType) -> CValue {
    match element_type {
        CType::Int8 => int8(0),
        CType::Int16 => int16(0),
        CType::Int32 => int32(0),
        CType::UInt8 => uint8(0),
        CType::UInt16 => uint16(0),
        CType::UInt32 => uint32(0),
        CType::Int64 => CValue::Int64(Bitvector32Term::Int64Constant(0)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
        pointer => CValue::typed_pointer(Pointer::null(), pointer),
    }
}

fn function_with_global_array(element_type: CType, length: u32) -> CFunction {
    storage_function("read", vec![]).with_global_arrays(vec![CGlobalArray::new_with_kernel_name(
        "buf",
        "buf",
        element_type,
        length,
        CArrayContents::new(length, zero_element(element_type), []),
    )])
}

/// An ordinary function's entry names every element of a global array it has
/// no initializer authority over by its symbolic entry value. The elements
/// are one run and their access widths one declaration, and together they
/// are exactly what materializing each element by itself leaves: the same
/// cells, and the same width recorded at every element before and after the
/// elements are named one by one.
#[test]
fn a_symbolic_global_array_entry_holds_exactly_the_per_element_cells() {
    for element_type in [
        CType::Int8,
        CType::Int32,
        CType::UInt8,
        CType::UInt16,
        CType::Int64,
        CType::UInt64,
        CType::Int32Pointer,
        CType::UInt8Pointer,
    ] {
        for length in [1u32, 5, 64, 65, 300] {
            crate::kernel::eval::clear_load_variable_registry();
            let function = function_with_global_array(element_type, length);
            let entry = initialize_c_function_globals(&CState::new(), &function);
            let base = CMemory::global_pointer("buf");
            let width = element_type.byte_width();
            assert_eq!(
                entry.memory().cells.representation_len(),
                1,
                "{element_type:?}[{length}] is one run"
            );
            let source =
                crate::kernel::intern_c_memory(symbolic_memory_base(entry.memory(), &base));
            let slot = |index: u32| base.offset_by_bytes(index * width);
            // An object pointer's entry load records no width.
            let expected_width = (!element_type.is_object_pointer()).then_some(width);
            let widths = |memory: &SharedCMemory| {
                (0..length)
                    .map(|index| {
                        (
                            crate::kernel::eval::recorded_load_access_width(memory, &slot(index)),
                            crate::kernel::load_access_width_at_address_or_widest(&slot(index)),
                        )
                    })
                    .collect::<Vec<_>>()
            };
            let declared = widths(&source);
            assert!(
                declared.iter().all(|(exact, _)| *exact == expected_width),
                "{element_type:?}[{length}] declares its widths: {declared:?}"
            );
            let mut reference =
                CMemory::new().with_block_or_read_only(base.block.clone(), length * width, false);
            for index in 0..length {
                reference = materialize_symbolic_cell(reference, &slot(index), element_type);
            }
            assert_eq!(
                entry.memory().cells.logical(),
                reference.cells.logical(),
                "{element_type:?}[{length}] holds the per-element cells"
            );
            // Recording each element's width again, as the per-element path
            // just did, changes no answer: the declaration was those records.
            assert_eq!(widths(&source), declared, "{element_type:?}[{length}]");
            for index in [0, length / 2, length - 1] {
                assert_eq!(
                    entry.memory().load(&slot(index)),
                    reference.load(&slot(index)),
                    "{element_type:?}[{length}] element {index}"
                );
            }
            // A store into the array writes that element alone.
            let stored = zero_element(element_type);
            let written = entry
                .memory()
                .clone()
                .store(slot(length - 1), stored.clone());
            assert_eq!(
                written.load(&slot(length - 1)),
                CExpressionOutcome::Value(stored)
            );
            if length > 1 {
                assert_eq!(written.load(&slot(0)), reference.load(&slot(0)));
            }
        }
    }
}

/// Entering a function that names a global array costs the same whatever
/// the array's declared length. Before runs, every element was materialized
/// as its own cell, named and width-recorded one by one, so a
/// `static char buf[65536]` cost 65,536 cells at every entry.
#[test]
fn a_symbolic_global_array_entry_costs_the_same_whatever_its_length() {
    for element_type in [CType::UInt8, CType::Int32, CType::Int32Pointer] {
        let samples = [8u32, 1_000, 1_000_000].map(|length| {
            crate::kernel::eval::clear_load_variable_registry();
            let function = function_with_global_array(element_type, length);
            let (entry, work) = crate::instrumentation::measure_deterministic_work(|| {
                initialize_c_function_globals(&CState::new(), &function)
            });
            (length, work, entry.memory().cells.representation_len())
        });
        let least = samples
            .iter()
            .map(|(_, work, _)| *work)
            .min()
            .expect("samples");
        let most = samples
            .iter()
            .map(|(_, work, _)| *work)
            .max()
            .expect("samples");
        assert_eq!(
            least, most,
            "{element_type:?} entry work depends on the array's length: {samples:?}"
        );
        assert!(
            samples.iter().all(|(_, _, entries)| *entries == 1),
            "{element_type:?} entry is one run: {samples:?}"
        );
    }
}

/// Entering a function over a global array, collecting the variables its
/// entry state mentions, and one statement's store into an element and read
/// of another cost the same whatever the array's length, and name exactly the
/// elements read. Collecting the entry state's variables used to name every
/// element to find its load variable, so a one-million-element array minted
/// a million load identities at function entry and exhausted the load
/// registry before the first statement.
#[test]
fn a_symbolic_global_array_names_only_the_elements_a_function_reads() {
    for element_type in [CType::UInt8, CType::Int32, CType::Int32Pointer] {
        let width = i64::from(element_type.byte_width());
        let samples = [8u32, 1_000, 1_000_000].map(|length| {
            // Each sample is its own verification, so none reuses another's
            // named loads or memoized answers.
            let _session = crate::kernel::VerificationSession::enter();
            let function = function_with_global_array(element_type, length);
            let registered = crate::kernel::eval::load_variable_registry_len;
            let before_entry = registered();
            let (entry, entry_work) = crate::instrumentation::measure_deterministic_work(|| {
                let entry = initialize_c_function_globals(&CState::new(), &function);
                let mut variables = std::collections::BTreeSet::new();
                crate::kernel::reasoning::collect_c_state_bitvector_variables(
                    &entry,
                    &mut variables,
                );
                entry
            });
            let entry_named = registered() - before_entry;
            let base = CMemory::global_pointer("buf");
            let element = |index: i64| Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Constant(index * width),
            };
            let before_statement = registered();
            let (read, statement_work) = crate::instrumentation::measure_deterministic_work(|| {
                let stored = entry
                    .memory()
                    .clone()
                    .store(element(5), zero_element(element_type));
                let read = stored.load(&element(6));
                let mut variables = std::collections::BTreeSet::new();
                crate::kernel::reasoning::collect_memory_bitvector_variables(
                    &stored,
                    &mut variables,
                );
                read
            });
            assert!(
                matches!(read, CExpressionOutcome::Value(_)),
                "{element_type:?}[{length}] element 6 reads its entry value: {read:?}"
            );
            let statement_named = registered() - before_statement;
            (
                length,
                entry_work,
                entry_named,
                statement_work,
                statement_named,
            )
        });
        let (_, entry_work, entry_named, statement_work, statement_named) = samples[0];
        assert!(
            samples
                .iter()
                .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                    == (entry_work, entry_named, statement_work, statement_named)),
            "{element_type:?} entry or statement cost depends on the array's length \
             (length, entry work, identities named at entry, statement work, identities \
             named by the statement): {samples:?}"
        );
        assert!(
            statement_named <= 2,
            "{element_type:?} a statement reading one element names at most its load \
             and the stored cell's: {samples:?}"
        );
    }
}

/// A function over a global `int32 buf[length] = {[2] = 7, [length - 1] = 3}`
/// (`const` when asked) and a static `uint8 counts[length] = {255}`.
fn function_with_initialized_arrays(length: u32, constant: bool) -> CFunction {
    storage_function("main", vec![])
        .with_global_arrays(vec![
            CGlobalArray::new_with_kernel_name(
                "buf",
                "buf",
                CType::Int32,
                length,
                CArrayContents::new(length, int32(0), [(2, int32(7)), (length - 1, int32(3))]),
            )
            .with_constant(constant),
        ])
        .with_static_arrays(vec![CStaticArray::new(
            "counts",
            "counts",
            CType::UInt8,
            length,
            CArrayContents::new(length, uint8(0), [(0, uint8(255))]),
        )])
}

/// Program startup stores an initialized array's contents as one run of its
/// default with the written elements stored over it, and that leaves exactly
/// the cells, and the startup permissions, of storing every element one by
/// one in element order.
#[test]
fn an_initialized_array_at_startup_holds_exactly_the_per_element_stores() {
    for length in [4u32, 5, 64, 65, 300] {
        let function = function_with_initialized_arrays(length, false);
        let startup =
            initialize_c_program_storage([function.clone()]).expect("no run limit is installed");
        let mut reference = CMemory::new();
        let mut per_element = |pointer: Pointer, element_type: CType, contents: &CArrayContents| {
            reference = reference.clone().with_block_or_read_only(
                pointer.block.clone(),
                length * element_type.byte_width(),
                false,
            );
            for index in 0..length {
                reference = reference.clone().store(
                    pointer.offset_by_bytes(index * element_type.byte_width()),
                    contents.value_at(index).clone(),
                );
            }
        };
        per_element(
            CMemory::global_pointer("buf"),
            CType::Int32,
            function.global_arrays()[0].initial_values(),
        );
        per_element(
            CMemory::static_pointer("main", "counts"),
            CType::UInt8,
            function.static_arrays()[0].initial_values(),
        );
        assert_eq!(
            startup.memory().cells.logical(),
            reference.cells.logical(),
            "[{length}] holds the per-element cells"
        );
        assert!(
            startup.memory().cells.representation_len() <= 5,
            "[{length}] is two runs and three written cells"
        );
        assert_eq!(
            startup.resources().facts(),
            initial_static_resources(&reference, || {})
                .expect("no run limit is installed")
                .facts(),
            "[{length}] partitions its storage as the per-element cells do"
        );
    }
}

/// Program startup, a load of a written element, of an unwritten one, and
/// a store then a load, cost the same whatever the declared length of the
/// initialized arrays, and every load yields exactly the initializer's (or
/// the store's) value. Startup used to store every element one by one, and
/// partitioning the startup permissions walked every cell.
#[test]
fn an_initialized_array_at_startup_costs_the_same_whatever_its_length() {
    let samples = [8u32, 1_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_initialized_arrays(length, false);
        let (startup, startup_work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_program_storage([function.clone()]).expect("no run limit is installed")
        });
        let buf = CMemory::global_pointer("buf");
        let counts = CMemory::static_pointer("main", "counts");
        let element = |index: u32| buf.offset_by_bytes(index * 4);
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            let memory = startup.memory();
            let stored = memory.clone().store(element(5), int32(9));
            [
                memory.load(&element(2)),
                memory.load(&element(5)),
                memory.load(&element(length - 1)),
                memory.load(&counts),
                memory.load(&counts.offset_by_bytes(length - 1)),
                stored.load(&element(5)),
                stored.load(&element(6)),
            ]
        });
        let value = CExpressionOutcome::Value;
        assert_eq!(
            loads,
            [
                value(int32(7)),
                value(int32(0)),
                value(int32(3)),
                value(uint8(255)),
                value(uint8(0)),
                value(int32(9)),
                value(int32(0)),
            ],
            "[{length}] reads its initializer"
        );
        (
            length,
            startup_work,
            load_work,
            startup.memory().cells.representation_len(),
            startup.resources().facts().len(),
        )
    });
    let (_, startup_work, load_work, entries, facts) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                == (startup_work, load_work, entries, facts)),
        "startup cost depends on the arrays' length (length, startup work, load work, \
         cell entries, startup permissions): {samples:?}"
    );
}

/// An ordinary function's entry knows a `const` array's contents too, and
/// installs them at the same cost whatever the array's length.
#[test]
fn a_constant_array_at_function_entry_costs_the_same_whatever_its_length() {
    let samples = [8u32, 1_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_initialized_arrays(length, true);
        let (entry, work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_function_globals(&CState::new(), &function)
        });
        let buf = CMemory::global_pointer("buf");
        assert_eq!(
            entry.memory().load(&buf.offset_by_bytes(8)),
            CExpressionOutcome::Value(int32(7)),
            "[{length}] element 2"
        );
        assert_eq!(
            entry.memory().load(&buf.offset_by_bytes(12)),
            CExpressionOutcome::Value(int32(0)),
            "[{length}] element 3"
        );
        (length, work, entry.memory().cells.representation_len())
    });
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2) == (samples[0].1, samples[0].2)),
        "constant array entry cost depends on its length (length, work, cell entries): \
         {samples:?}"
    );
}

/// `struct node { int32 key; uint8 tag; int32 *next; int32 pair[2]; }`,
/// with `wide` extra bytes of inline array when asked for one.
fn node_layout(wide: u32) -> CAggregateLayout {
    let mut fields = vec![
        CAggregateField::new("key", 0, CType::Int32),
        CAggregateField::new("tag", 4, CType::UInt8),
        CAggregateField::new("next", 8, CType::Int32Pointer),
        CAggregateField::new("pair", 16, CType::Int32Array(2)),
    ];
    if wide > 0 {
        fields.push(CAggregateField::new("bytes", 24, CType::UInt8Array(wide)));
    }
    CAggregateLayout::new((24 + wide).next_multiple_of(8), 8, fields)
}

/// A global `struct node pool[length]` writing element 2's key and the last
/// element's `pair[1]`, and a static local `slots[length]` writing element
/// 0's tag.
fn function_with_aggregate_arrays(length: u32, wide: u32, constant: bool) -> CFunction {
    let size = node_layout(wide).size_bytes();
    storage_function("main", vec![])
        .with_global_aggregate_arrays(vec![
            CGlobalAggregateArray::new(
                "pool",
                "pool",
                node_layout(wide),
                length,
                vec![
                    CAggregateInitializer::new(2 * size, int32(7)),
                    CAggregateInitializer::new((length - 1) * size + 20, int32(3)),
                ],
            )
            .with_constant(constant),
        ])
        .with_static_aggregate_arrays(vec![CStaticAggregateArray::new(
            "slots",
            "slots",
            node_layout(wide),
            length,
            vec![CAggregateInitializer::new(4, uint8(255))],
        )])
}

/// Program startup stores an array of structs as one zero run per field
/// with the written fields stored over them, and that leaves exactly the
/// cells of zeroing every element's fields one by one and then storing the
/// written fields, with startup permissions owning the same bytes. An
/// inline array field longer than the struct count is one run per struct
/// instead.
#[test]
fn an_aggregate_array_at_startup_holds_exactly_the_per_field_stores() {
    for (length, wide) in [(3u32, 0u32), (4, 0), (5, 12), (12, 8), (65, 0), (3, 100)] {
        let function = function_with_aggregate_arrays(length, wide, false);
        let startup =
            initialize_c_program_storage([function.clone()]).expect("no run limit is installed");
        let layout = node_layout(wide);
        let mut reference = CMemory::new();
        for (pointer, initializers) in [
            (
                CMemory::global_pointer("pool"),
                function.global_aggregate_arrays()[0].initializers(),
            ),
            (
                CMemory::static_pointer("main", "slots"),
                function.static_aggregate_arrays()[0].initializers(),
            ),
        ] {
            reference = reference.clone().with_block_or_read_only(
                pointer.block.clone(),
                length * layout.size_bytes(),
                false,
            );
            for element in 0..length {
                reference = zero_aggregate_fields(
                    reference,
                    &pointer.offset_by_bytes(element * layout.size_bytes()),
                    &layout,
                );
            }
            reference = initialize_aggregate_fields(reference, &pointer, initializers);
        }
        assert_eq!(
            startup.memory().cells.logical(),
            reference.cells.logical(),
            "[{length} x {wide}] holds the per-field cells"
        );
        // The per-field cells partition each block by cell width, a range
        // per field per element; the runs' periodic block is one range of
        // struct-sized elements. Both own exactly the same bytes.
        let per_field =
            initial_static_resources(&reference, || {}).expect("no run limit is installed");
        assert_eq!(
            owned_bytes(startup.resources()),
            owned_bytes(&per_field),
            "[{length} x {wide}] owns the bytes the per-field cells own"
        );
        if wide == 0 && length > 1 {
            assert_eq!(
                startup.resources().facts().len(),
                2,
                "[{length}] each array of structs is one range"
            );
        }
    }
}

/// Every block's owned bytes, as ascending disjoint half-open intervals.
fn owned_bytes(resources: &ResourceContext) -> BTreeMap<PointerBlock, Vec<(i64, i64)>> {
    let mut bytes = BTreeMap::<PointerBlock, Vec<(i64, i64)>>::new();
    for fact in resources.facts() {
        let range = fact
            .memory_own_range()
            .expect("startup permissions own memory");
        let PointerOffsetTerm::Constant(offset) = range.base().offset else {
            panic!("startup ranges have constant bases");
        };
        let width = i64::from(range.element_width());
        let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const()) else {
            panic!("startup ranges have constant bounds");
        };
        bytes.entry(range.base().block.clone()).or_default().push((
            offset + i64::from(start) * width,
            offset + i64::from(end) * width,
        ));
    }
    for intervals in bytes.values_mut() {
        intervals.sort_unstable();
        let mut merged: Vec<(i64, i64)> = Vec::new();
        for (low, high) in intervals.drain(..) {
            match merged.last_mut() {
                Some((_, end)) if *end == low => *end = high,
                _ => merged.push((low, high)),
            }
        }
        *intervals = merged;
    }
    bytes
}

/// Program startup, and loads of written and zero fields and a store then a
/// load, cost the same whatever the length of an array of structs, and
/// every load is exact. Startup used to store every field of every element.
#[test]
fn an_aggregate_array_at_startup_costs_the_same_whatever_its_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_aggregate_arrays(length, 0, false);
        let (startup, startup_work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_program_storage([function.clone()]).expect("no run limit is installed")
        });
        let pool = CMemory::global_pointer("pool");
        let slots = CMemory::static_pointer("main", "slots");
        let field = |element: u32, offset: u32| pool.offset_by_bytes(element * 24 + offset);
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            let memory = startup.memory();
            let stored = memory.clone().store(field(5, 0), int32(9));
            [
                memory.load(&field(2, 0)),
                memory.load(&field(5, 0)),
                memory.load(&field(5, 8)),
                memory.load(&field(length - 1, 20)),
                memory.load(&field(length - 1, 16)),
                memory.load(&slots.offset_by_bytes(4)),
                memory.load(&slots.offset_by_bytes((length - 1) * 24 + 4)),
                stored.load(&field(5, 0)),
                stored.load(&field(6, 0)),
            ]
        });
        let value = CExpressionOutcome::Value;
        assert_eq!(
            loads,
            [
                value(int32(7)),
                value(int32(0)),
                value(CValue::typed_pointer(Pointer::null(), CType::Int32Pointer)),
                value(int32(3)),
                value(int32(0)),
                value(uint8(255)),
                value(uint8(0)),
                value(int32(9)),
                value(int32(0)),
            ],
            "[{length}] reads its initializer"
        );
        (
            length,
            startup_work,
            load_work,
            startup.memory().cells.representation_len(),
            startup.resources().facts().len(),
        )
    });
    let (_, startup_work, load_work, entries, facts) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                == (startup_work, load_work, entries, facts)),
        "startup cost depends on the aggregate arrays' length (length, startup work, load \
         work, cell entries, startup permissions): {samples:?}"
    );
}

/// An ordinary function's entry names every field of a symbolic array of
/// structs as its symbolic entry value, one run per field, and that leaves
/// exactly the cells of materializing every struct's fields one by one. A
/// layout with more cells than there are structs is materialized struct by
/// struct.
#[test]
fn a_symbolic_aggregate_array_at_function_entry_holds_exactly_the_per_struct_cells() {
    for length in [1u32, 2, 5, 64, 65] {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_aggregate_arrays(length, 0, false);
        let entry = initialize_c_function_globals(&CState::new(), &function);
        let layout = node_layout(0);
        let mut reference = CMemory::new();
        for pointer in [
            CMemory::global_pointer("pool"),
            CMemory::static_pointer("main", "slots"),
        ] {
            reference = reference.clone().with_block_or_read_only(
                pointer.block.clone(),
                length * layout.size_bytes(),
                false,
            );
            for element in 0..length {
                reference = materialize_symbolic_aggregate_fields(
                    reference,
                    &pointer.offset_by_bytes(element * layout.size_bytes()),
                    &layout,
                );
            }
        }
        assert_eq!(
            entry.memory().cells.logical(),
            reference.cells.logical(),
            "[{length}] holds the per-struct cells"
        );
    }
}

/// An ordinary function's entry, and loads of its fields, cost the same
/// whatever the length of a symbolic array of structs, and name no field it
/// does not read. Entry used to name every field of every struct, so a
/// million-struct pool exhausted the load identities.
#[test]
fn a_symbolic_aggregate_array_at_function_entry_costs_the_same_whatever_its_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let function = function_with_aggregate_arrays(length, 0, false);
        let registered = crate::kernel::eval::load_variable_registry_len();
        let (entry, entry_work) = crate::instrumentation::measure_deterministic_work(|| {
            initialize_c_function_globals(&CState::new(), &function)
        });
        let pool = CMemory::global_pointer("pool");
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                entry.memory().load(&pool.offset_by_bytes(24 * 7)),
                entry
                    .memory()
                    .load(&pool.offset_by_bytes(24 * (length - 1) + 20)),
            ]
        });
        assert!(
            loads.iter().all(|load| matches!(
                load,
                CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Variable(_)))
            )),
            "[{length}] a field reads as its load: {loads:?}"
        );
        (
            length,
            entry_work,
            load_work,
            entry.memory().cells.representation_len(),
            crate::kernel::eval::load_variable_registry_len() - registered,
        )
    });
    let (_, entry_work, load_work, entries, named) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3, sample.4)
                == (entry_work, load_work, entries, named)),
        "a symbolic aggregate array's entry depends on its length (length, entry work, load \
         work, cell entries, load identities named): {samples:?}"
    );
}

#[test]
fn actual_global_and_static_producers_retain_declared_domains_without_reinitializing() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = CAggregateLayout::new(8, 4, vec![CAggregateField::new("first", 0, CType::Int32)]);
    let function = storage_function(
        "declared_storage",
        vec![CGlobal::new("global", CType::Int32, int32(7))],
    )
    .with_global_arrays(vec![CGlobalArray::new_with_kernel_name(
        "global_items",
        "global_items",
        CType::Int32,
        2,
        vec![int32(1), int32(2)],
    )])
    .with_global_aggregates(vec![CGlobalAggregate::new(
        "global_record",
        "global_record",
        layout.clone(),
        vec![],
    )])
    .with_static_variables(vec![CStaticLocal::new(
        "local",
        "local",
        CType::Int32,
        int32(8),
    )])
    .with_static_arrays(vec![CStaticArray::new(
        "local_items",
        "local_items",
        CType::Int32,
        2,
        vec![int32(3), int32(4)],
    )])
    .with_static_aggregates(vec![CStaticAggregate::new(
        "local_record",
        "local_record",
        layout.clone(),
        vec![],
    )])
    .with_string_literals(vec![CStringLiteral::new("literal", b"ok\0".to_vec())]);
    let global = CMemory::global_pointer("global");
    // Pre-existing storage/values can come from caller resource preparation.
    let caller = CState::new().with_memory(
        CMemory::new()
            .with_block(global.block.clone(), 4)
            .store(global.clone(), int32(37)),
    );
    let initialized = initialize_c_function_globals(&caller, &function);
    assert_eq!(initialized.memory().known_value(&global), Some(int32(37)));
    for root in [
        global.clone(),
        CMemory::static_pointer("declared_storage", "local"),
    ] {
        let pointer = initialized
            .memory()
            .declared_scalar_pointer(&root, CType::Int32)
            .unwrap();
        assert!(
            initialized
                .memory()
                .authenticated_pointer_domain_at_base(&pointer)
        );
        assert!(
            !initialized
                .memory()
                .requires_explicit_scalar_ownership(&root)
        );
    }
    for root in [
        CMemory::global_pointer("global_items"),
        CMemory::static_pointer("declared_storage", "local_items"),
    ] {
        let pointer = initialized
            .memory()
            .declared_array_pointer(&root, CType::Int32, 2)
            .unwrap();
        assert!(
            initialized
                .memory()
                .authenticated_pointer_domain_at_base(&pointer)
        );
        assert!(
            initialized
                .memory()
                .declared_array_pointer(&root, CType::Int32, 3)
                .is_none()
        );
    }
    for root in [
        CMemory::global_pointer("global_record"),
        CMemory::static_pointer("declared_storage", "local_record"),
    ] {
        let pointer = initialized
            .memory()
            .declared_aggregate_pointer(&root, &layout)
            .unwrap();
        assert!(
            initialized
                .memory()
                .authenticated_pointer_domain_at_base(&pointer)
        );
        assert!(!initialized.memory().has_initialized_bytes_under(
            &root.offset_by_bytes(4),
            4,
            &PureFactContext::new()
        ));
    }
    let literal = CMemory::string_literal_pointer("declared_storage", "literal", b"ok\0");
    let pointer = initialized
        .memory()
        .declared_array_pointer(&literal, CType::UInt8, 3)
        .unwrap();
    assert!(
        initialized
            .memory()
            .authenticated_pointer_domain_at_base(&pointer)
    );
    assert!(
        initialized
            .memory()
            .blocks
            .get(&literal.block)
            .unwrap()
            .is_read_only()
    );
    assert_eq!(
        initialized.resources().facts().len(),
        1,
        "only the existing literal authority is installed"
    );
    let again = initialize_c_function_globals(&initialized, &function);
    assert_eq!(
        again.memory(),
        initialized.memory(),
        "repeated declaration setup is a metadata no-op"
    );
    assert_eq!(again.memory().known_value(&global), Some(int32(37)));
}

#[test]
fn aggregate_array_producers_do_not_invent_scalar_byte_array_domains() {
    let function = function_with_aggregate_arrays(4, 0, false);
    let initialized = initialize_c_function_globals(&CState::new(), &function);
    for root in [
        CMemory::global_pointer("pool"),
        CMemory::static_pointer("main", "slots"),
    ] {
        assert!(
            initialized
                .memory()
                .blocks
                .get(&root.block)
                .unwrap()
                .declared_object
                .is_none()
        );
        assert!(
            initialized
                .memory()
                .declared_array_pointer(&root, CType::UInt8, 4 * node_layout(0).size_bytes())
                .is_none()
        );
    }
}
