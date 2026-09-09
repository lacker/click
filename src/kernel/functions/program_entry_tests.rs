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
fn startup_coalesces_declarations_and_calls_cannot_replenish_ownership() {
    let global = CGlobal::new("state", CType::Int32, int32(7));
    let left = storage_function("left", vec![global.clone()]);
    let right = storage_function("right", vec![global]);
    let startup = initialize_c_program_storage([left.clone(), right]);
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
    let state = initialize_c_program_storage([left, right]);
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
        let resources = initial_static_resources(&memory, || visits += 1);
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
    let startup = initialize_c_program_storage([function.clone()]);
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
    let startup = initialize_c_program_storage([left, right, array]);
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
