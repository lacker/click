use super::*;
use crate::kernel::prelude::*;

fn pending_malloc(state: &CState) -> CState {
    let paths = execute_c_statement_paths(
        state,
        &c_heap_allocate("p", 16),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("actual malloc statement executes");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("expected one pending allocation path");
    };
    *pending.clone()
}

fn resolved_malloc(pending: &CState, success: bool) -> CState {
    let Some(CValue::Pointer(pointer)) = pending.locals().get("p") else {
        panic!("pending allocation has a result pointer");
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null()),
        !success,
    ));
    crate::kernel::resolve_pending_heap_allocations(pending, &assumptions)
}

#[test]
fn only_successful_real_malloc_records_creation() {
    let entry = CState::new()
        .with_local("p", CValue::pointer(Pointer::null()))
        .with_population_creation_tracking();
    let pending = pending_malloc(&entry);
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("p") else {
        unreachable!();
    };
    assert!(!pending.population_storage_created_here(pending_pointer));

    let failed = resolved_malloc(&pending, false);
    let Some(CValue::Pointer(failed_pointer)) = failed.locals().get("p") else {
        unreachable!();
    };
    assert!(!failed.population_storage_created_here(failed_pointer));

    let succeeded = resolved_malloc(&pending, true);
    let Some(CValue::Pointer(created)) = succeeded.locals().get("p") else {
        unreachable!();
    };
    assert!(succeeded.population_storage_created_here(created));
    assert!(!entry.population_storage_created_here(created));
    assert!(!succeeded.population_storage_created_here(&created.pointer().offset_by_bytes(4)));
    assert_eq!(
        succeeded
            .clone()
            .with_population_creation_tracking()
            .population_effects
            .creation,
        succeeded.population_effects.creation,
        "opt-in cannot reset a live provenance ledger"
    );

    let imported = CState::new()
        .with_population_creation_tracking()
        .with_memory(
            CMemory::new()
                .with_heap_allocation_claim(created.pointer().clone(), 16)
                .expect("assumed allocation claim"),
        );
    assert!(!imported.population_storage_created_here(created));

    let helper = c_function(
        CType::Void,
        "helper",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_return(c_void_value()),
    );
    let callee = bind_c_function_arguments(
        &succeeded,
        &helper,
        &[CValue::pointer(created.pointer().clone())],
    )
    .expect("bind actual helper environment");
    let Some(CValue::Pointer(copied)) = callee.locals().get("q") else {
        unreachable!();
    };
    assert!(!callee.population_storage_created_here(copied));
    let returned = callee
        .population_effects
        .creation
        .as_ref()
        .expect("callee ledger")
        .return_to(
            succeeded
                .population_effects
                .creation
                .as_ref()
                .expect("caller ledger"),
        );
    let mut resumed = succeeded.clone();
    Arc::make_mut(&mut resumed.population_effects).creation = Some(returned);
    assert!(resumed.population_storage_created_here(created));
    assert_ne!(
        resumed.population_effects.creation, succeeded.population_effects.creation,
        "a call return advances invocation identity even when its ownership is unchanged"
    );
    assert_eq!(
        resumed
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created_here(&created.block),
        succeeded
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created_here(&created.block),
        "the new identity preserves the caller's creation right"
    );

    let freed = execute_c_statement_paths(
        &succeeded,
        &c_heap_free(c_variable("p")),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("free executes");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after_free),
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("free should consume allocation and storage");
    };
    assert!(!after_free.population_storage_created_here(created));

    let untracked = resolved_malloc(
        &pending_malloc(&CState::new().with_local("p", CValue::pointer(Pointer::null()))),
        true,
    );
    assert!(untracked.population_effects.creation.is_none());
}

#[test]
fn caller_pending_malloc_resolved_in_helper_keeps_caller_origin() {
    let caller = CState::new()
        .with_local("p", CValue::pointer(Pointer::null()))
        .with_population_creation_tracking();
    let pending = pending_malloc(&caller);
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("p") else {
        unreachable!();
    };
    let helper = c_function(
        CType::Int32,
        "resolve_in_helper",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_if(
            c_variable("q"),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(0)),
        ),
    );
    let callee = bind_c_function_arguments(
        &pending,
        &helper,
        &[CValue::pointer(pending_pointer.pointer().clone())],
    )
    .expect("bind actual helper environment");
    let paths = execute_c_statement_paths(
        &callee,
        helper.body(),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("helper decides caller's pending malloc result");
    assert_eq!(paths.len(), 2);
    let mut saw_success = false;
    let mut saw_failure = false;
    for path in paths {
        let CStatementOutcome::Return { value, state } = path.outcome else {
            panic!("helper must return from both branches");
        };
        let Some(CValue::Pointer(pointer)) = state.locals().get("q") else {
            panic!("helper retains its resolved parameter");
        };
        assert!(!state.memory().has_pending_heap_allocation());
        assert!(!state.population_storage_created_here(pointer));

        let mut resumed = pending.clone().with_memory(state.memory().clone());
        resumed.restore_population_creation_after_call(
            pending.population_effects.creation.as_ref(),
            state.population_effects.creation.as_ref(),
        );
        if pointer.pointer() == &Pointer::null() {
            saw_failure = true;
            assert_eq!(value, CValue::Int32(0.into()));
            assert!(!resumed.population_storage_created_here(pointer));
        } else {
            saw_success = true;
            assert_eq!(value, CValue::Int32(1.into()));
            assert!(matches!(pointer.block, PointerBlock::Heap(_)));
            assert!(resumed.population_storage_created_here(pointer));
        }
    }
    assert!(saw_success && saw_failure);
}

#[test]
fn creation_lookup_and_call_transport_ignore_unrelated_events() {
    let sizes = [64_u64, 256, 1024];
    let mut work = Vec::new();
    for size in sizes {
        let mut events = CreationEvents::new();
        for id in 0..size {
            events = events.created(PointerBlock::Heap(id));
            events = events.member_created(&PointerBlock::Heap(id), "reference");
            events = events.pending_creation(PointerBlock::Symbolic(Variable(id)));
        }
        let selected = PointerBlock::Heap(size / 2);
        let pending_block = PointerBlock::Symbolic(Variable(10_000 + size));
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.created_here(&selected));
            assert_eq!(
                events.establish(&selected, "reference"),
                Err(CreationRefusal::MembersAlreadyExisted)
            );
            assert!(events.establish(&selected, "other").is_ok());
            let callee = events.enter_call();
            assert!(!callee.created_here(&selected));
            assert!(callee.return_to(&events).created_here(&selected));
            let started = events.pending_creation(pending_block.clone());
            let resolved = started
                .enter_call()
                .resolve_pending(&pending_block, Some(PointerBlock::Heap(size)));
            assert!(!resolved.created_here(&PointerBlock::Heap(size)));
            assert!(
                resolved
                    .return_to(&events)
                    .created_here(&PointerBlock::Heap(size))
            );
        });
        assert!(measured > 0);
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 20, "{work:?}");
}

#[test]
fn actual_stack_declaration_grants_one_lifetime_creation_event() {
    let entry = CState::new().with_population_creation_tracking();
    let paths = execute_c_statement_paths(
        &entry,
        &c_declare("x", CType::Int32),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("declaration executes");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(declared),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("one declaration path");
    };
    let slot = declared.locals().slot("x").expect("declared slot").clone();
    assert!(declared.population_storage_created_here(&slot));
    assert!(!entry.population_storage_created_here(&slot));
    assert!(!declared.population_storage_created_here(&slot.offset_by_bytes(1)));

    let ended = crate::kernel::eval::end_scope_automatic_lifetimes(declared, &["x".to_owned()])
        .expect("scope exit");
    assert!(!ended.population_storage_created_here(&slot));
    let second = execute_c_statement_paths(
        &ended,
        &c_declare("x", CType::Int32),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&CExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .expect("re-enter declaration");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(second),
            ..
        },
    ] = second.as_slice()
    else {
        panic!("one re-entry path");
    };
    let second_slot = second.locals().slot("x").expect("new slot");
    assert_ne!(slot.block, second_slot.block);
    assert!(second.population_storage_created_here(second_slot));
    assert!(!second.population_storage_created_here(&slot));
}

#[test]
fn member_history_blocks_late_establishment_after_transfer_and_return() {
    let block = PointerBlock::Heap(940_100);
    let caller = CreationEvents::new().created(block.clone());
    let moved = caller.member_created(&block, "reference");
    let helper = moved.enter_call();
    assert_eq!(
        helper.establish(&block, "reference"),
        Err(CreationRefusal::NotCreationEnvironment),
    );
    let resumed = helper.return_to(&caller);
    assert_eq!(
        resumed.establish(&block, "reference"),
        Err(CreationRefusal::MembersAlreadyExisted),
    );
    let established_other = resumed
        .establish(&block, "other")
        .expect("unrelated family remains pristine");
    assert_eq!(
        established_other.establish(&block, "other"),
        Err(CreationRefusal::AlreadyEstablished),
    );
    assert_eq!(
        established_other.retired(&block),
        Err(CreationRefusal::OutstandingAuthority),
    );
    let retired_other = established_other
        .retire_authority(&block, "other")
        .expect("zero-member authority retires");
    let ended = retired_other.retired(&block).expect("empty lifetime ends");
    assert_eq!(
        ended.establish(&block, "other"),
        Err(CreationRefusal::NotCreationEnvironment),
    );
}

#[test]
fn pending_member_history_follows_actual_malloc_result() {
    let pending = PointerBlock::Symbolic(Variable(940_101));
    let live = PointerBlock::Heap(940_102);
    let caller = CreationEvents::new()
        .pending_creation(pending.clone())
        .member_created(&pending, "reference");
    let helper = caller.enter_call();
    let decided = helper.resolve_pending(&pending, Some(live.clone()));
    let resumed = decided.return_to(&caller);
    assert_eq!(
        resumed.establish(&live, "reference"),
        Err(CreationRefusal::MembersAlreadyExisted),
    );
    assert!(resumed.establish(&live, "other").is_ok());
}

#[test]
fn storage_cannot_expire_with_outstanding_population_authority() {
    let block = PointerBlock::Heap(940_103);
    let created = CreationEvents::new().created(block.clone());
    let established = created
        .establish(&block, "reference")
        .expect("creation environment establishes empty population");
    assert_eq!(
        established.retirement_refusal(&block),
        Some(CreationRefusal::OutstandingAuthority)
    );
    assert_eq!(
        established.retired(&block),
        Err(CreationRefusal::OutstandingAuthority)
    );
    let retired = established
        .retire_authority(&block, "reference")
        .expect("zero-member authority retires")
        .retired(&block)
        .expect("empty storage lifetime retires");
    assert!(!retired.created_here(&block));
}

#[test]
fn repeated_entry_recheck_reuses_the_same_creation_environment() {
    let caller = CreationEvents::new();
    let first = caller.enter_call();
    assert_eq!(first, caller.enter_call());
    assert_ne!(first, caller);
    let advanced = caller.created(PointerBlock::Heap(940_104));
    assert_ne!(first, advanced.enter_call());
}

#[test]
fn rechecking_c_creation_events_reuses_exact_successor_roots() {
    let live = PointerBlock::Heap(940_107);
    let start = CreationEvents::new();
    assert_eq!(start.created(live.clone()), start.created(live));

    let pending = PointerBlock::Symbolic(Variable(940_108));
    let first = start.pending_creation(pending.clone());
    assert_eq!(first, start.pending_creation(pending.clone()));
    let resolved = first.resolve_pending(&pending, Some(PointerBlock::Heap(940_109)));
    assert_eq!(
        resolved,
        first.resolve_pending(&pending, Some(PointerBlock::Heap(940_109)))
    );
}

fn member_description(block: PointerBlock) -> ResourceDescription {
    ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block,
                offset: PointerOffsetTerm::Constant(0),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    )
}

#[test]
fn opaque_helper_import_has_no_count_and_checks_each_member_exchange() {
    let description = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(940_110)),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let entry = CreationEvents::new()
        .import_opaque_contract_population(&description, 1)
        .unwrap();
    assert!(entry.owns_population_authority(&description));
    assert!(entry.owns_population_member(&description));
    let proof_entry = entry.enter_proof_entry();
    assert!(proof_entry.owns_population_authority(&description));
    assert_eq!(proof_entry, entry.enter_proof_entry());
    let nested_call = proof_entry.enter_call();
    assert!(!nested_call.owns_population_authority(&description));
    assert!(!nested_call.owns_population_member(&description));
    assert_eq!(
        entry.observe(&PointerBlock::ExternalArgument, "reference"),
        Err(CreationRefusal::UnknownTotal)
    );
    let (retained, _) = entry
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .expect("retain may add one member while already holding a member");
    assert!(retained.born_imported_member_since(&entry, &description));
    assert!(retained.observe_symbolic(&description).is_none());
    let (retained_twice, _) = retained
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .expect("each checked birth adds another held member");
    assert!(retained_twice.born_imported_member_since(&retained, &description));
    assert!(retained_twice.observe_symbolic(&description).is_none());
    assert_eq!(
        retained_twice.observe(&PointerBlock::ExternalArgument, "reference"),
        Err(CreationRefusal::UnknownTotal)
    );
    let (restored, _) = retained
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(restored.owns_population_member(&description));
    assert_eq!(
        restored.imported_member_delta_since_entry(&description),
        None
    );
    let two = CreationEvents::new()
        .import_opaque_contract_population(&description, 2)
        .unwrap();
    let (one, _) = two
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(one.spent_imported_member_since(&two, &description));
    assert!(one.owns_population_member(&description));
    let (none, _) = one
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .expect("the second explicitly held fragment can also be spent");
    assert!(!none.owns_population_member(&description));
    assert!(matches!(
        none.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
    let empty = CreationEvents::new()
        .import_opaque_contract_population(&description, 0)
        .unwrap();
    let (born, _) = empty
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .expect("an opaque helper can birth its exact member once");
    assert!(born.born_imported_member_since(&empty, &description));
    assert!(born.owns_population_member(&description));
    let (born_twice, _) = born
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .expect("repeated checked births preserve numeric fragment custody");
    assert!(born_twice.born_imported_member_since(&born, &description));
    assert!(born_twice.observe_symbolic(&description).is_none());
    let (spent, _) = entry
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .expect("an opaque helper can spend its exact imported member once");
    assert!(spent.spent_imported_member_since(&entry, &description));
    assert!(!spent.owns_population_member(&description));
    assert!(matches!(
        spent.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
    let other = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(940_111)),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let both = entry.import_opaque_contract_population(&other, 1).unwrap();
    assert!(both.owns_population_authority(&description));
    assert!(both.owns_population_member(&other));
    let (spent_first, _) = both
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(!spent_first.owns_population_member(&description));
    assert!(spent_first.owns_population_member(&other));
    assert!(!spent_first.spent_imported_member_since(&both, &other));
    let (spent_second, _) = spent_first
        .checked_member_exchange(&PointerBlock::ExternalArgument, &other, false)
        .unwrap();
    assert!(spent_second.spent_imported_member_since(&spent_first, &other));
    assert!(!spent_second.spent_imported_member_since(&spent_first, &description));
    assert_eq!(
        both.import_opaque_contract_population(&description, 0),
        Err(CreationRefusal::OpaqueImportConflict)
    );

    let authority = CResourceFact::own(CResource::PopulationAuthority(description.clone()));
    let member = CResourceFact::own(CResource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let state = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(
            ResourceContext::new().unchecked_with_facts([authority.clone(), member]),
        );
    assert!(!state.recognizes_population_authority(&description));
    let imported = state.import_opaque_population(&authority, 1).unwrap();
    assert!(imported.recognizes_population_authority(&description));
    assert!(
        imported
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .observe_symbolic(&description)
            .is_some()
    );
}

#[test]
fn observable_unary_import_preserves_arbitrary_count_and_current_custody() {
    let description = member_description(PointerBlock::ExternalArgument);
    let source = CreationEvents::new();
    let entry = source
        .import_observable_contract_population(&description, 1)
        .unwrap();
    let count = entry.observe_symbolic(&description).unwrap();
    assert!(matches!(count.entry_count, Bitvector32Term::Variable(_)));
    assert_eq!(count.entry_owned_members, 1);
    assert_eq!(
        entry
            .import_observable_contract_population(&description, 1)
            .unwrap(),
        entry
    );
    let repeated = source
        .import_observable_contract_population(&description, 1)
        .unwrap();
    assert_eq!(
        repeated.observe_symbolic(&description).unwrap().entry_count,
        count.entry_count
    );
    let helper = entry.enter_call();
    let held = entry
        .transfer_call_fact(&entry, &helper, &description, true)
        .unwrap();
    assert!(held.observe_symbolic(&description).is_none());
    let held = held
        .transfer_call_fact(&entry, &helper, &description, false)
        .unwrap()
        .return_to(&helper);
    let (spent, _) = held
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    let after = spent.observe_symbolic(&description).unwrap();
    assert_eq!(after.entry_count, count.entry_count);
    assert_eq!(after.delta, -1);
}

#[test]
fn opaque_numeric_batch_composes_with_units_without_fabricating_custody() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_observable_contract_population(&description, 0)
        .unwrap();
    let initial = entry.observe_symbolic(&description).unwrap();
    let empty = PureFactContext::new().assume_condition(
        crate::kernel::ConditionTerm::equal(
            initial.entry_count.clone(),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let exchange = |state: &CreationEvents, produce, amount, facts: &PureFactContext| {
        state.checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            produce,
            &Bitvector32Term::Constant(amount),
            facts,
        )
    };
    assert!(matches!(
        exchange(&entry, true, 2, &PureFactContext::new()),
        Err(CreationRefusal::InvalidQuantity)
    ));
    let two = exchange(&entry, true, 2, &empty).unwrap().0;
    assert_eq!(two.observe_symbolic(&description).unwrap().delta, 2);
    assert_eq!(
        two.observe_symbolic(&description).unwrap().entry_count,
        initial.entry_count
    );
    let one = exchange(&two, false, 1, &empty).unwrap().0;
    assert_eq!(one.observe_symbolic(&description).unwrap().delta, 1);
    assert!(matches!(
        exchange(&one, false, 2, &empty),
        Err(CreationRefusal::MissingMembers)
    ));
    let none = exchange(&one, false, 1, &empty).unwrap().0;
    assert!(!none.owns_population_member(&description));
    let zero = exchange(&none, true, 0, &empty).unwrap().0;
    assert_eq!(zero.observe_symbolic(&description).unwrap().delta, 0);
    assert!(!zero.owns_population_member(&description));
    let zero = exchange(&zero, false, 0, &empty).unwrap().0;
    assert!(!zero.owns_population_member(&description));
    let max = exchange(&entry, true, i32::MAX as u32, &empty).unwrap().0;
    assert!(matches!(
        exchange(&max, true, 2, &empty),
        Err(CreationRefusal::InvalidQuantity)
    ));
    let literal_empty = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(Bitvector32Term::Constant(0)),
            None,
            None,
        )
        .unwrap();
    let literal_two = exchange(&literal_empty, true, 2, &PureFactContext::new())
        .unwrap()
        .0;
    let literal_one = exchange(&literal_two, false, 1, &PureFactContext::new())
        .unwrap()
        .0;
    assert_eq!(literal_one.observe_symbolic(&description).unwrap().delta, 1);
    let helper = entry.enter_call();
    let lent = two
        .transfer_call_fact(&entry, &helper, &description, true)
        .unwrap();
    // A caller that lent its authority cannot perform even a zero exchange.
    assert!(matches!(
        exchange(&lent, true, 0, &empty),
        Err(CreationRefusal::MissingAuthority)
    ));
}

#[test]
fn field_quantity_moves_and_consumes_only_the_owned_numerical_batch() {
    let description = member_description(PointerBlock::ExternalArgument);
    let quantity = Bitvector32Term::Variable(Variable(940_140));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::equal(quantity.clone(), Bitvector32Term::Constant(2)),
        true,
    );
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            2,
            Some(Bitvector32Term::Constant(2)),
            None,
            None,
        )
        .unwrap();
    let child = entry.enter_call();
    assert_eq!(
        child
            .transfer_call_fact_quantity(
                &entry,
                &child,
                &description,
                false,
                &quantity,
                &PureFactContext::new()
            )
            .unwrap_err(),
        CreationRefusal::MissingMembers,
    );
    let wrong = PureFactContext::new().assume_condition(
        ConditionTerm::equal(quantity.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    assert_eq!(
        child
            .transfer_call_fact_quantity(&entry, &child, &description, false, &quantity, &wrong)
            .unwrap_err(),
        CreationRefusal::MissingMembers,
    );
    // Transfer custody separately from authority; equality grants neither.
    let members = child
        .transfer_call_fact_quantity(&entry, &child, &description, false, &quantity, &facts)
        .unwrap();
    assert!(members.owns_population_member(&description));
    assert!(!members.owns_population_authority(&description));
    assert_eq!(
        members
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &description,
                false,
                &quantity,
                &facts
            )
            .unwrap_err(),
        CreationRefusal::MissingAuthority,
    );
    assert_eq!(
        members
            .transfer_call_fact_quantity(&entry, &child, &description, false, &quantity, &facts)
            .unwrap_err(),
        CreationRefusal::MissingMembers,
    );
    let both = members
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap();
    let spent = both
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            false,
            &quantity,
            &facts,
        )
        .unwrap()
        .0;
    assert!(!spent.owns_population_member(&description));
    assert_eq!(spent.observe_symbolic(&description).unwrap().delta, -2);
    assert_eq!(
        spent
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &description,
                false,
                &quantity,
                &facts
            )
            .unwrap_err(),
        CreationRefusal::MissingMembers,
    );
    let retired = spent
        .checked_retire_imported(&description, &facts)
        .unwrap()
        .0;
    let returned = retired.finish_call(&entry).unwrap();
    assert!(!returned.owns_population_authority(&description));
    assert!(!returned.owns_population_member(&description));
}

#[test]
fn field_quantity_cannot_spend_a_global_count_without_member_custody() {
    let description = member_description(PointerBlock::ExternalArgument);
    let quantity = Bitvector32Term::Variable(Variable(940_141));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::equal(quantity.clone(), Bitvector32Term::Constant(2)),
        true,
    );
    let authority_only = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(Bitvector32Term::Constant(2)),
            None,
            None,
        )
        .unwrap();
    assert_eq!(
        authority_only
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &description,
                false,
                &quantity,
                &facts
            )
            .unwrap_err(),
        CreationRefusal::MissingMembers,
    );
    let child = authority_only.enter_call();
    assert_eq!(
        child
            .transfer_call_fact_quantity(
                &authority_only,
                &child,
                &description,
                false,
                &quantity,
                &facts
            )
            .unwrap_err(),
        CreationRefusal::MissingMembers,
    );
}

#[test]
fn field_quantity_batch_work_ignores_quantity_and_unrelated_facts() {
    let description = member_description(PointerBlock::ExternalArgument);
    let quantity = Bitvector32Term::Variable(Variable(940_142));
    let mut work = Vec::new();
    for (amount, unrelated) in [(2, 0), (64, 32), (1024, 256), (65536, 1024)] {
        let entry = CreationEvents::new()
            .import_opaque_contract_population_inner(
                &description,
                amount,
                Some(Bitvector32Term::Constant(amount)),
                None,
                None,
            )
            .unwrap();
        let mut facts = PureFactContext::new();
        for index in 0..unrelated {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(950_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );
        }
        facts = facts.assume_condition(
            ConditionTerm::equal(quantity.clone(), Bitvector32Term::Constant(amount)),
            true,
        );
        let (returned, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let child = entry.enter_call();
            let both = child
                .transfer_call_fact(&entry, &child, &description, true)
                .unwrap()
                .transfer_call_fact_quantity(&entry, &child, &description, false, &quantity, &facts)
                .unwrap();
            let spent = both
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    false,
                    &quantity,
                    &facts,
                )
                .unwrap()
                .0;
            spent
                .checked_retire_imported(&description, &facts)
                .unwrap()
                .0
                .finish_call(&entry)
                .unwrap()
        });
        assert!(!returned.owns_population_member(&description));
        work.push(measured);
    }
    assert!(work[3] <= work[0] * 2 + 32, "{work:?}");
}

#[test]
fn opaque_numeric_batch_work_does_not_grow_with_quantity() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_observable_contract_population(&description, 0)
        .unwrap();
    let facts = PureFactContext::new().assume_condition(
        crate::kernel::ConditionTerm::equal(
            entry.observe_symbolic(&description).unwrap().entry_count,
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let measurements = [2, 64, 1024, 65536].map(|amount| {
        let (after, work) = crate::persistent::measure_persistent_work(|| {
            entry
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    true,
                    &Bitvector32Term::Constant(amount),
                    &facts,
                )
                .unwrap()
                .0
        });
        assert_eq!(
            after.observe_symbolic(&description).unwrap().delta,
            amount as i32
        );
        work
    });
    assert!(measurements[0] > 0, "{measurements:?}");
    assert!(
        measurements.iter().all(|work| *work == measurements[0]),
        "{measurements:?}"
    );
}

#[test]
fn opaque_symbolic_birth_composes_numeric_custody_and_scales() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let quantity = Bitvector32Term::Variable(Variable(940_150));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_add_overflows(quantity.clone(), Bitvector32Term::Constant(3)),
            false,
        );
    let work = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("unrelated-{index}"),
                description.arguments().to_vec().into(),
                description.schema().clone(),
            );
            entry = entry
                .import_opaque_contract_population_inner(
                    &unrelated,
                    0,
                    Some(Bitvector32Term::Constant(0)),
                    None,
                    None,
                )
                .unwrap();
        }
        entry = entry
            .import_opaque_contract_population_inner(
                &description,
                0,
                Some(Bitvector32Term::Constant(0)),
                None,
                None,
            )
            .unwrap();
        let symbolic = entry
            .checked_member_exchange_quantity(&block, &description, true, &quantity, &assumptions)
            .unwrap()
            .0;
        assert!(matches!(
            symbolic.checked_member_exchange_quantity(
                &block,
                &description,
                true,
                &Bitvector32Term::Constant(3),
                &PureFactContext::new()
            ),
            Err(CreationRefusal::InvalidQuantity)
        ));
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            let born = symbolic
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &Bitvector32Term::Constant(3),
                    &assumptions,
                )
                .unwrap()
                .0;
            let observed = born.observe_symbolic(&description).unwrap();
            assert_eq!(observed.delta, 3);
            assert_eq!(
                observed.combined_delta(),
                Some((
                    true,
                    Bitvector32Term::add(quantity.clone(), Bitvector32Term::Constant(3))
                ))
            );
            assert_eq!(
                born.imported_member_delta_since_entry(&description),
                observed.combined_delta()
            );
            let retired = born
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &quantity,
                    &assumptions,
                )
                .unwrap()
                .0;
            let remaining = retired.observe_symbolic(&description).unwrap();
            assert_eq!(remaining.delta, 3, "numerical custody survives retirement");
            assert_eq!(remaining.symbolic_delta, None);
            assert!(retired.owns_population_member(&description));
            assert_eq!(
                retired.0.opaque_holders.get(&retired.0.opaque_actor),
                born.0
                    .opaque_holders
                    .get(&born.0.opaque_actor)
                    .map(|rights| rights - 1)
                    .as_ref()
            );
            let child = born.enter_call();
            let sent = child
                .transfer_call_fact(&born, &child, &description, true)
                .unwrap()
                .transfer_call_fact(&born, &child, &description, false)
                .unwrap();
            // A numerical fragment can be passed and spent independently of the
            // caller's framed symbolic batch and two other numerical members.
            let spent = sent
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &Bitvector32Term::Constant(1),
                    &assumptions,
                )
                .unwrap()
                .0;
            assert_eq!(spent.observe_symbolic(&description).unwrap().delta, 2);
            let returned = spent
                .transfer_call_fact(&child, &born, &description, true)
                .unwrap()
                .finish_call(&born)
                .unwrap();
            let restored = returned
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &Bitvector32Term::Constant(2),
                    &assumptions,
                )
                .unwrap()
                .0;
            assert_eq!(
                restored
                    .observe_symbolic(&description)
                    .unwrap()
                    .combined_delta(),
                Some((true, quantity.clone()))
            );
            assert!(restored.owns_population_member(&description));
            assert!(matches!(
                restored.checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &Bitvector32Term::Constant(1),
                    &assumptions
                ),
                Err(CreationRefusal::MissingMembers)
            ));
            let wrong = Bitvector32Term::add(quantity.clone(), Bitvector32Term::Constant(1));
            assert!(
                restored
                    .transfer_call_fact_quantity(
                        &born,
                        &child,
                        &description,
                        false,
                        &wrong,
                        &assumptions
                    )
                    .is_err()
            );
            let lent = restored
                .transfer_call_fact(&born, &child, &description, true)
                .unwrap();
            assert!(matches!(
                lent.checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &Bitvector32Term::Constant(1),
                    &assumptions
                ),
                Err(CreationRefusal::MissingAuthority)
            ));
        });
        work
    });
    assert!(work[0] > 0);
    assert!(
        work.iter().all(|sample| *sample <= work[0] + 256),
        "mixed batch work scanned unrelated populations: {work:?}"
    );
}

#[test]
fn opaque_symbolic_batch_has_one_checked_exchange_and_current_custody() {
    let description = member_description(PointerBlock::ExternalArgument);
    // Keep this a genuinely symbolic batch: fixed numerical batches now
    // compose with unit exchanges, covered by the separate numerical test.
    let quantity = Bitvector32Term::Variable(Variable(940_120));
    let assumptions = PureFactContext::new().assume_condition(
        crate::kernel::ConditionTerm::signed_greater_equal(
            quantity.clone(),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let held = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(quantity.clone()),
            Some(quantity.clone()),
            None,
        )
        .unwrap();
    assert!(held.owns_population_member(&description));
    assert!(matches!(
        held.checked_member_exchange(&PointerBlock::ExternalArgument, &description, true),
        Err(CreationRefusal::InvalidQuantity)
    ));
    let (spent, _) = held
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            false,
            &quantity,
            &assumptions,
        )
        .unwrap();
    assert!(!spent.owns_population_member(&description));
    assert!(matches!(
        spent.checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            false,
            &quantity,
            &assumptions,
        ),
        Err(CreationRefusal::InvalidQuantity)
    ));

    let empty = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(Bitvector32Term::Constant(0)),
            None,
            None,
        )
        .unwrap();
    let (born, _) = empty
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            true,
            &quantity,
            &assumptions,
        )
        .unwrap();
    assert!(born.owns_population_member(&description));
    assert!(matches!(
        born.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
}

#[test]
fn opaque_symbolic_batch_call_custody_roundtrips_independently_of_authority() {
    let description = member_description(PointerBlock::ExternalArgument);
    let quantity = Bitvector32Term::Variable(Variable(940_130));
    let assumptions = PureFactContext::new().assume_condition(
        crate::kernel::ConditionTerm::signed_greater_equal(
            quantity.clone(),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(quantity.clone()),
            Some(quantity.clone()),
            None,
        )
        .unwrap();
    let child = entry.enter_call();
    let zero_transfer = child
        .transfer_call_fact_quantity(
            &entry,
            &child,
            &description,
            false,
            &Bitvector32Term::Constant(0),
            &assumptions,
        )
        .unwrap();
    assert!(!zero_transfer.owns_population_member(&description));
    assert!(!zero_transfer.owns_population_authority(&description));
    assert!(
        zero_transfer
            .finish_call(&entry)
            .unwrap()
            .owns_population_member(&description)
    );
    let authority_only = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap();
    assert!(authority_only.owns_population_authority(&description));
    assert!(!authority_only.owns_population_member(&description));
    assert_eq!(
        authority_only
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &description,
                false,
                &quantity,
                &assumptions,
            )
            .unwrap_err(),
        CreationRefusal::MissingMembers
    );
    assert!(
        authority_only
            .return_to(&entry)
            .owns_population_member(&description)
    );
    let wrong = Bitvector32Term::add(quantity.clone(), Bitvector32Term::Constant(1));
    assert_eq!(
        authority_only
            .transfer_call_fact_quantity(&entry, &child, &description, false, &wrong, &assumptions,)
            .unwrap_err(),
        CreationRefusal::InvalidQuantity
    );
    let both = authority_only
        .transfer_call_fact_quantity(&entry, &child, &description, false, &quantity, &assumptions)
        .unwrap();
    assert!(both.owns_population_member(&description));
    assert!(!both.return_to(&entry).owns_population_member(&description));
    assert_eq!(
        both.transfer_call_fact_quantity(
            &entry,
            &child,
            &description,
            false,
            &quantity,
            &assumptions,
        )
        .unwrap_err(),
        CreationRefusal::MissingMembers
    );
    let authority_returned = both
        .transfer_call_fact(&child, &entry, &description, true)
        .unwrap();
    assert!(matches!(
        authority_returned.finish_call(&entry),
        Err(CreationRefusal::OutstandingOwnership)
    ));
    let all_returned = authority_returned
        .transfer_call_fact_quantity(&child, &entry, &description, false, &quantity, &assumptions)
        .unwrap()
        .finish_call(&entry)
        .unwrap();
    assert!(all_returned.owns_population_authority(&description));
    assert!(all_returned.owns_population_member(&description));
    assert_eq!(
        all_returned
            .observe_symbolic(&description)
            .unwrap()
            .entry_count,
        quantity
    );
    assert!(
        all_returned
            .imported_member_delta_since_entry(&description)
            .is_none()
    );
    // Moving only the batch also grants no authority to consume it.
    let child = all_returned.enter_call();
    let batch_only = child
        .transfer_call_fact_quantity(
            &all_returned,
            &child,
            &description,
            false,
            &quantity,
            &assumptions,
        )
        .unwrap();
    assert!(batch_only.owns_population_member(&description));
    assert!(!batch_only.owns_population_authority(&description));
    assert_eq!(
        batch_only
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &description,
                false,
                &quantity,
                &assumptions,
            )
            .unwrap_err(),
        CreationRefusal::MissingAuthority
    );
}

#[test]
fn opaque_symbolic_birth_returns_exact_batch_without_moving_framed_population() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry_count = Bitvector32Term::Variable(Variable(940_132));
    let quantity = Bitvector32Term::Variable(Variable(940_133));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_add_overflows(entry_count.clone(), quantity.clone()),
            false,
        );
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(entry_count.clone()),
            None,
            None,
        )
        .unwrap();
    let child = entry.enter_call();
    let authorized = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap();
    let (born, _) = authorized
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            true,
            &quantity,
            &assumptions,
        )
        .unwrap();
    assert!(born.owns_population_member(&description));
    let wrong = Bitvector32Term::add(quantity.clone(), Bitvector32Term::Constant(1));
    assert_eq!(born.transfer_call_fact_quantity(
        &child, &entry, &description, false, &wrong, &assumptions,
    ).unwrap_err(), CreationRefusal::InvalidQuantity);
    let returned = born
        .transfer_call_fact_quantity(&child, &entry, &description, false, &quantity, &assumptions)
        .unwrap();
    assert!(!returned.owns_population_member(&description));
    assert!(
        returned
            .return_to(&entry)
            .owns_population_member(&description)
    );
    assert_eq!(
        returned
            .transfer_call_fact_quantity(
                &child,
                &entry,
                &description,
                false,
                &quantity,
                &assumptions,
            )
            .unwrap_err(),
        CreationRefusal::MissingMembers
    );
    assert!(matches!(
        returned.finish_call(&entry),
        Err(CreationRefusal::OutstandingOwnership)
    ));
    let finished = returned
        .transfer_call_fact(&child, &entry, &description, true)
        .unwrap()
        .finish_call(&entry)
        .unwrap();
    assert!(finished.owns_population_member(&description));
    assert!(finished.owns_population_authority(&description));
    let observed = finished.observe_symbolic(&description).unwrap();
    assert_eq!(observed.entry_count, entry_count);
    assert_eq!(observed.symbolic_delta, Some((true, quantity)));
}

#[test]
fn opaque_symbolic_batch_transfer_work_ignores_unrelated_populations() {
    let quantity = Bitvector32Term::Variable(Variable(940_131));
    let description = member_description(PointerBlock::ExternalArgument);
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    for born_batch in [false, true] {
        let mut work = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut entry = CreationEvents::new();
            for index in 0..size {
                let unrelated = ResourceDescription::new(
                    format!("unrelated-{index}"),
                    description.arguments().to_vec().into(),
                    description.schema().clone(),
                );
                entry = entry
                    .import_opaque_contract_population_inner(
                        &unrelated,
                        0,
                        Some(Bitvector32Term::Constant(0)),
                        None,
                        None,
                    )
                    .unwrap();
            }
            entry = entry
                .import_opaque_contract_population_inner(
                    &description,
                    0,
                    Some(if born_batch {
                        Bitvector32Term::Constant(0)
                    } else {
                        quantity.clone()
                    }),
                    (!born_batch).then(|| quantity.clone()),
                    None,
                )
                .unwrap();
            let (returned, measured) = crate::instrumentation::measure_deterministic_work(|| {
                let child = entry.enter_call();
                let authority = child
                    .transfer_call_fact(&entry, &child, &description, true)
                    .unwrap();
                let held = if born_batch {
                    authority
                        .checked_member_exchange_quantity(
                            &PointerBlock::ExternalArgument,
                            &description,
                            true,
                            &quantity,
                            &assumptions,
                        )
                        .unwrap()
                        .0
                } else {
                    authority
                        .transfer_call_fact_quantity(
                            &entry,
                            &child,
                            &description,
                            false,
                            &quantity,
                            &assumptions,
                        )
                        .unwrap()
                };
                held.transfer_call_fact_quantity(
                    &child,
                    &entry,
                    &description,
                    false,
                    &quantity,
                    &assumptions,
                )
                .unwrap()
                .transfer_call_fact(&child, &entry, &description, true)
                .unwrap()
                .finish_call(&entry)
                .unwrap()
            });
            assert!(returned.owns_population_member(&description));
            work.push(measured);
        }
        assert!(work[3] <= work[0] * 2 + 32, "born={born_batch}: {work:?}");
    }
}

#[test]
fn independent_opaque_symbolic_populations_keep_their_own_counts_and_members() {
    let first = member_description(PointerBlock::ExternalArgument);
    let second = ResourceDescription::new(
        "other_reference".into(),
        first.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let first_quantity = Bitvector32Term::Constant(3);
    let second_quantity = Bitvector32Term::Constant(5);
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &first,
            0,
            Some(Bitvector32Term::Constant(7)),
            Some(first_quantity.clone()),
            None,
        )
        .unwrap()
        .import_opaque_contract_population_inner(
            &second,
            0,
            Some(Bitvector32Term::Constant(11)),
            Some(second_quantity.clone()),
            None,
        )
        .unwrap();
    let (spent, _) = entry
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &first,
            false,
            &first_quantity,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(!spent.owns_population_member(&first));
    assert!(spent.owns_population_member(&second));
    assert_eq!(
        spent
            .observe_symbolic(&first)
            .unwrap()
            .entry_count
            .as_const(),
        Some(7)
    );
    assert_eq!(
        spent
            .observe_symbolic(&second)
            .unwrap()
            .entry_count
            .as_const(),
        Some(11)
    );
    assert!(spent.imported_member_delta_since_entry(&second).is_none());
    let (spent_both, _) = spent
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &second,
            false,
            &second_quantity,
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(
        spent_both.imported_member_delta_since_entry(&first),
        Some((false, first_quantity))
    );
    assert_eq!(
        spent_both.imported_member_delta_since_entry(&second),
        Some((false, second_quantity))
    );
}

#[test]
fn opaque_population_lookup_and_exchange_ignore_unrelated_imports() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let description_at = |id| {
            ResourceDescription::new(
                "reference".into(),
                vec![
                    CValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(950_000 + id)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            )
        };
        let mut events = CreationEvents::new();
        for id in 0..size {
            events = events
                .import_opaque_contract_population_inner(
                    &description_at(id),
                    1,
                    Some(Bitvector32Term::Constant(3)),
                    None,
                    None,
                )
                .unwrap();
        }
        let selected = description_at(size / 2);
        let neighbor = description_at(size / 2 + 1);
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.owns_population_authority(&selected));
            assert_eq!(events.observe_symbolic(&selected).unwrap().delta, 0);
            let (spent, _) = events
                .checked_member_exchange(&PointerBlock::ExternalArgument, &selected, false)
                .unwrap();
            assert_eq!(spent.observe_symbolic(&selected).unwrap().delta, -1);
            assert_eq!(spent.observe_symbolic(&neighbor).unwrap().delta, 0);
            assert!(spent.spent_imported_member_since(&events, &selected));
            assert!(!spent.spent_imported_member_since(&events, &neighbor));
            assert!(
                spent
                    .enter_proof_entry()
                    .owns_population_authority(&selected)
            );
            assert!(!spent.enter_call().owns_population_authority(&selected));
        });
        assert!(measured > 0);
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 20, "{work:?}");
}

#[test]
fn two_authority_control_import_checks_each_custody_and_scope() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(940_112)),
    };
    let selected = CResourceFact::own(CResource::Composite {
        name: "control".into(),
        arguments: vec![CValue::pointer(pointer.clone()).into()].into(),
    });
    let reference = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "reference".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
    );
    let authority = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(reference),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let cell = SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(SpecExpression::PointerOffset {
            pointer: Box::new(SpecExpression::CExpression(c_variable("p"))),
            elements: Box::new(SpecExpression::Value(int32(0))),
            byte_width: 4,
        }),
        value_type: CType::Int32,
    };
    let count = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::CExpression(c_variable("p")))],
    };
    let mut definition = CCompositeResourceDefinition::new(
        "control",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            )),
            authority,
        ],
        vec![SpecProposition::Comparison {
            left: cell,
            operator: CComparisonOperator::Equal,
            right: count,
        }],
    );
    let state = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let entry = state.population_effects.creation.as_ref().unwrap();
    let wildcard = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            population_arity: Some(2),
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(CResourceSpec::composite(
                    CResourceAccessMode::Own,
                    "item".into(),
                    vec![c_variable("p")],
                    vec![CType::Int32Pointer],
                )),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    definition.contains.push(wildcard);
    let imported = entry
        .import_checked_control_wrapper(&state, &selected, &definition, &PureFactContext::new())
        .unwrap();
    let components = state
        .checked_authority_wrapper_import_components(
            &selected,
            &definition,
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(components.len(), 2);
    assert!(components[0].1.is_some());
    assert!(components[1].1.is_none());
    for (description, _) in &components {
        assert!(imported.owns_population_authority(description));
        assert!(imported.observe_symbolic(description).is_some());
        assert!(!imported.checked_empty_population(description));
        assert!(
            imported
                .checked_establish(&PointerBlock::ExternalArgument, description)
                .is_err()
        );
    }
    let mut current = state.clone();
    Arc::make_mut(&mut current.population_effects).creation = Some(imported.clone());
    assert!(
        current
            .checked_authority_wrapper_body(&selected, &definition, &PureFactContext::new())
            .is_ok()
    );
    let callee = imported.enter_call();
    let handed_off = imported
        .transfer_call_fact(&imported, &callee, &components[0].0, true)
        .unwrap();
    let mut partial = state.clone();
    Arc::make_mut(&mut partial.population_effects).creation = Some(handed_off);
    assert!(
        partial
            .checked_authority_wrapper_body(&selected, &definition, &PureFactContext::new())
            .is_err()
    );
    // A selected wildcard member is authenticated against both the exact
    // input custody and the contained scope; its total remains arbitrary.
    let scope = components
        .iter()
        .find(|(scope, _)| scope.population_arity().is_some())
        .unwrap()
        .0
        .clone();
    let member = ResourceDescription::new(
        scope.family().into(),
        vec![scope.arguments()[0].clone(), int32(7).into()].into(),
        scope.schema().clone(),
    );
    let fact = CResourceFact::own(CResource::Composite {
        name: member.family().into(),
        arguments: member.arguments().to_vec().into(),
    });
    let selected_state = state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_fact(fact.clone()));
    let members = BTreeMap::from([(scope.clone(), vec![fact.clone()])]);
    let selected_import = entry
        .import_checked_control_wrapper_with_members(
            &selected_state,
            &selected,
            &definition,
            &PureFactContext::new(),
            &members,
        )
        .unwrap();
    assert!(selected_import.owns_imported_population_member(&member));
    assert_eq!(
        selected_import
            .observe_symbolic(&scope)
            .unwrap()
            .entry_owned_members,
        1
    );
    assert!(
        entry
            .import_checked_control_wrapper_with_members(
                &state,
                &selected,
                &definition,
                &PureFactContext::new(),
                &members,
            )
            .is_err(),
        "a supplied member map cannot invent ownership"
    );
    let duplicated = BTreeMap::from([(scope.clone(), vec![fact.clone(), fact])]);
    assert!(
        entry
            .import_checked_control_wrapper_with_members(
                &selected_state,
                &selected,
                &definition,
                &PureFactContext::new(),
                &duplicated,
            )
            .is_err()
    );
    let mut wrong_args = member.arguments().to_vec();
    wrong_args[0] = CValue::pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(912),
    })
    .into();
    let wrong = CResourceFact::own(CResource::Composite {
        name: member.family().into(),
        arguments: wrong_args.into(),
    });
    let wrong_state = state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_fact(wrong.clone()));
    assert!(
        entry
            .import_checked_control_wrapper_with_members(
                &wrong_state,
                &selected,
                &definition,
                &PureFactContext::new(),
                &BTreeMap::from([(scope, vec![wrong])]),
            )
            .is_err(),
        "an owned member of another pool cannot seed this scope"
    );

    definition.contains[2] = definition.contains[1].clone();
    assert!(
        entry
            .import_checked_control_wrapper(&state, &selected, &definition, &PureFactContext::new())
            .is_err()
    );
}

#[test]
fn checked_control_import_observes_only_its_exact_entry_population() {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(940_112)),
    };
    let selected = CResourceFact::own(CResource::Composite {
        name: "control".into(),
        arguments: vec![CValue::pointer(pointer.clone()).into()].into(),
    });
    let reference = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "reference".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
    );
    let authority = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(reference),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let cell = SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(SpecExpression::PointerOffset {
            pointer: Box::new(SpecExpression::CExpression(c_variable("p"))),
            elements: Box::new(SpecExpression::Value(int32(0))),
            byte_width: 4,
        }),
        value_type: CType::Int32,
    };
    let count = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::CExpression(c_variable("p")))],
    };
    let definition = CCompositeResourceDefinition::new(
        "control",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            )),
            authority,
        ],
        vec![SpecProposition::Comparison {
            left: cell,
            operator: CComparisonOperator::Equal,
            right: count,
        }],
    );
    let state = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let entry = state.population_effects.creation.as_ref().unwrap();
    let imported = entry
        .import_checked_control_wrapper(&state, &selected, &definition, &PureFactContext::new())
        .expect("checked control body authenticates its entry count");
    let description = ResourceDescription::new(
        "reference".into(),
        vec![CValue::pointer(pointer.clone()).into()].into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let observed = imported.observe_symbolic(&description).unwrap();
    let wrong_population = ResourceDescription::new(
        "other_reference".into(),
        description.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(imported.observe_symbolic(&wrong_population).is_none());
    let member = CResourceFact::own(CResource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let retiring_state = state.clone().with_resource_context(
        ResourceContext::new().unchecked_with_facts([selected.clone(), member]),
    );
    let retiring_entry = retiring_state.population_effects.creation.as_ref().unwrap();
    let imported_with_member = retiring_entry
        .import_checked_control_wrapper(
            &retiring_state,
            &selected,
            &definition,
            &PureFactContext::new(),
        )
        .unwrap();
    let (spent, _) = imported_with_member
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    let retirement_assumptions =
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(spent.observe_symbolic(&description).unwrap().entry_count),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            true,
        ));
    assert!(
        spent
            .checked_retire_imported(&description, &PureFactContext::new())
            .is_err()
    );
    let (retired, _) = spent
        .checked_retire_imported(&description, &retirement_assumptions)
        .unwrap();
    assert!(!retired.owns_population_authority(&description));
    assert_eq!(observed.delta, 0);
    assert_eq!(observed.entry_owned_members, 0);
    assert!(
        matches!(observed.entry_count, Bitvector32Term::MemoryLoad(_, loaded, _) if *loaded == pointer)
    );
    let count_expression = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::Value(CValue::pointer(
            pointer.clone(),
        )))],
    };
    let evaluate_count = |state: &CState| {
        crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            state,
            &count_expression,
            &PureFactContext::new(),
            &BTreeMap::new(),
            &mut ExecutionBudget::default(),
        )
    };
    let mut folded = state.clone();
    Arc::make_mut(&mut folded.population_effects).creation = Some(imported.clone());
    let folded_paths = evaluate_count(&folded).expect("owned control opens for a count read");
    assert!(folded.resources().contains_exact_representation(&selected));
    assert_eq!(folded.resources().facts().len(), 1);
    // Repackaging an existing authority into a different ordinary control
    // retains the same count and custody. It grants no import or creator right.
    let mut replacement_definition = definition.clone();
    replacement_definition.name = "replacement".into();
    let replacement = CResourceFact::own(CResource::Composite {
        name: "replacement".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let replacement_state = folded
        .clone()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(replacement.clone()));
    let registered = replacement_state
        .with_checked_current_control_wrapper(
            &replacement,
            &replacement_definition,
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(
        evaluate_count(&registered).unwrap()[0].value,
        folded_paths[0].value
    );
    assert_eq!(
        registered
            .with_checked_current_control_wrapper(
                &replacement,
                &replacement_definition,
                &PureFactContext::new(),
            )
            .unwrap()
            .population_effects
            .creation,
        registered.population_effects.creation
    );
    assert!(
        folded
            .with_checked_current_control_wrapper(
                &replacement,
                &replacement_definition,
                &PureFactContext::new(),
            )
            .is_err(),
        "an unowned replacement cannot register count permission"
    );
    assert!(
        state
            .clone()
            .with_resource_context(replacement_state.resources().clone())
            .with_checked_current_control_wrapper(
                &replacement,
                &replacement_definition,
                &PureFactContext::new(),
            )
            .is_err(),
        "packaging cannot invent authority custody"
    );
    let absent_control = folded.clone().with_resource_context(ResourceContext::new());
    assert!(evaluate_count(&absent_control).is_err());
    let viewed_control = folded.clone().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::View(selected.resource().clone())),
    );
    assert!(evaluate_count(&viewed_control).is_err());
    let unrelated_control = CResourceFact::own(CResource::Composite {
        name: "other_control".into(),
        arguments: wrong_population.arguments().to_vec().into(),
    });
    // A different definition cannot substitute for the authenticated head,
    // even when its C argument is identical.
    assert!(
        evaluate_count(
            &folded.clone().with_resource_context(
                ResourceContext::new().unchecked_with_fact(unrelated_control)
            )
        )
        .is_err()
    );
    let mut retired_control = folded.clone();
    Arc::make_mut(&mut retired_control.population_effects).creation = Some(retired.clone());
    assert_eq!(
        evaluate_count(&retired_control).unwrap()[0].value,
        CValue::Int32(Bitvector32Term::Constant(0))
    );
    let mut nested_control = folded.clone();
    Arc::make_mut(&mut nested_control.population_effects).creation = Some(imported.enter_call());
    assert!(evaluate_count(&nested_control).is_err());
    let mut rechecked_control = folded.clone();
    Arc::make_mut(&mut rechecked_control.population_effects).creation =
        Some(imported.enter_proof_entry());
    assert_eq!(
        evaluate_count(&rechecked_control).unwrap()[0].value,
        folded_paths[0].value
    );
    let mut projected =
        state
            .clone()
            .with_resource_context(
                ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::PopulationAuthority(description.clone()),
                )),
            );
    Arc::make_mut(&mut projected.population_effects).creation = Some(imported.clone());
    let paths = evaluate_count(&projected).expect("checked import permits exact count");
    assert_eq!(paths[0].value, folded_paths[0].value);
    assert_eq!(paths.len(), 1);
    assert!(matches!(
        paths[0].value,
        CValue::Int32(Bitvector32Term::MemoryLoad(_, _, _))
    ));
    // A population entry in the ledger is insufficient without current
    // ownership. Preserve the same ledger while changing only custody.
    let absent = projected
        .clone()
        .with_resource_context(ResourceContext::new());
    assert!(evaluate_count(&absent).is_err());
    let unrelated =
        projected
            .clone()
            .with_resource_context(
                ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::PopulationAuthority(wrong_population.clone()),
                )),
            );
    assert!(evaluate_count(&unrelated).is_err());
    // Proof-entry rechecking retains the explicit import; an ordinary nested
    // invocation must receive authority through its checked call transfer.
    let mut rechecked = projected.clone();
    Arc::make_mut(&mut rechecked.population_effects).creation = Some(imported.enter_proof_entry());
    assert_eq!(evaluate_count(&rechecked).unwrap()[0].value, paths[0].value);
    let mut nested = projected.clone();
    Arc::make_mut(&mut nested.population_effects).creation = Some(imported.enter_call());
    assert!(evaluate_count(&nested).is_err());
    let mut retired_state = projected.clone();
    Arc::make_mut(&mut retired_state.population_effects).creation = Some(retired);
    assert_eq!(
        evaluate_count(&retired_state).unwrap()[0].value,
        CValue::Int32(Bitvector32Term::Constant(0))
    );
    assert!(
        evaluate_count(&state).is_err(),
        "a folded wrapper alone cannot read count"
    );
    let (with_member, _) = imported
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, true)
        .unwrap();
    let born_count = with_member.observe_symbolic(&description).unwrap();
    assert_eq!(born_count.delta, 1);
    assert_eq!(born_count.entry_owned_members, 0);
    let (without_member, _) = with_member
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert_eq!(
        without_member.observe_symbolic(&description).unwrap().delta,
        0
    );
    let wrong = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(940_113)),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(imported.observe_symbolic(&wrong).is_none());
    let mut wrong_fact = definition.clone();
    wrong_fact.facts.clear();
    let arbitrary = entry
        .import_checked_control_wrapper(&state, &selected, &wrong_fact, &PureFactContext::new())
        .unwrap();
    let arbitrary_count = arbitrary
        .observe_symbolic(&description)
        .unwrap()
        .entry_count;
    assert!(matches!(arbitrary_count, Bitvector32Term::Variable(_)));
    assert_ne!(arbitrary_count, Bitvector32Term::Constant(0));
    assert_eq!(
        arbitrary_count,
        entry
            .import_checked_control_wrapper(&state, &selected, &wrong_fact, &PureFactContext::new())
            .unwrap()
            .observe_symbolic(&description)
            .unwrap()
            .entry_count
    );
    assert!(!arbitrary.checked_empty_population(&description));
    assert!(
        entry
            .import_checked_control_wrapper(&state, &selected, &definition, &PureFactContext::new())
            .is_ok()
    );
    let missing = CState::new().with_population_creation_tracking();
    assert!(
        entry
            .import_checked_control_wrapper(
                &missing,
                &selected,
                &definition,
                &PureFactContext::new()
            )
            .is_err()
    );
}

#[test]
fn helper_call_transfers_authority_and_member_without_changing_total() {
    let block = PointerBlock::Heap(940_106);
    let description = member_description(block.clone());
    let caller = CreationEvents::new().created(block.clone());
    let (caller, _) = caller.checked_establish(&block, &description).unwrap();
    let (caller, _) = caller
        .checked_member_exchange(&block, &description, true)
        .unwrap();
    let callee = caller.enter_call();
    assert!(!callee.owns_population_authority(&description));
    let entry = callee
        .transfer_call_fact(&caller, &callee, &description, true)
        .unwrap()
        .transfer_call_fact(&caller, &callee, &description, false)
        .unwrap();
    assert_eq!(entry.observe(&block, "reference"), Ok(1));
    assert!(entry.owns_population_authority(&description));
    assert!(
        !entry
            .return_to(&caller)
            .owns_population_authority(&description)
    );
    assert_eq!(
        entry.finish_call(&caller),
        Err(CreationRefusal::OutstandingOwnership)
    );
    let returned = entry
        .transfer_call_fact(&callee, &caller, &description, false)
        .unwrap()
        .transfer_call_fact(&callee, &caller, &description, true)
        .unwrap();
    let resumed = returned.finish_call(&caller).unwrap();
    assert!(resumed.owns_population_authority(&description));
    assert!(!returned.owns_population_authority(&description));
    assert_eq!(resumed.observe(&block, "reference"), Ok(1));
    assert_eq!(returned.finish_call(&caller).unwrap(), resumed);
    assert_ne!(resumed.enter_call(), callee);
    assert_eq!(
        resumed.transfer_call_fact(&callee, &caller, &description, false),
        Err(CreationRefusal::MissingMembers)
    );
}

#[test]
fn checked_member_exchange_conserves_exact_authority_total() {
    let block = PointerBlock::Heap(940_105);
    let description = member_description(block.clone());
    let created = CreationEvents::new().created(block.clone());
    assert_eq!(
        created.observe(&block, "reference"),
        Err(CreationRefusal::MissingAuthority)
    );
    assert_eq!(
        created
            .checked_member_exchange(&block, &description, true)
            .err(),
        Some(CreationRefusal::MissingAuthority)
    );
    let established = created.establish(&block, "reference").unwrap();
    assert_eq!(established.observe(&block, "reference"), Ok(0));
    assert_eq!(
        established
            .checked_member_exchange(&block, &description, false)
            .err(),
        Some(CreationRefusal::MissingMembers)
    );
    let (one, birth) = established
        .checked_member_exchange(&block, &description, true)
        .unwrap();
    assert!(birth.matches(&established, &one, &description, true));
    assert!(!birth.matches(&established, &one, &description, false));
    assert!(!birth.matches(&created, &one, &description, true));
    assert_eq!(one.observe(&block, "reference"), Ok(1));
    assert_eq!(
        one.retire_authority(&block, "reference"),
        Err(CreationRefusal::OutstandingMembers)
    );
    let (zero, death) = one
        .checked_member_exchange(&block, &description, false)
        .unwrap();
    assert!(death.matches(&one, &zero, &description, false));
    assert_eq!(zero.observe(&block, "reference"), Ok(0));
    assert_eq!(
        zero.checked_member_exchange(&block, &description, false)
            .err(),
        Some(CreationRefusal::MissingMembers)
    );
    assert_eq!(
        zero.retire_authority(&block, "reference")
            .unwrap()
            .observe(&block, "reference"),
        Err(CreationRefusal::MissingAuthority)
    );
}

#[test]
fn checked_member_exchange_requires_exact_field_free_anchor_and_holder() {
    let block = PointerBlock::Heap(940_106);
    let established = CreationEvents::new()
        .created(block.clone())
        .establish(&block, "reference")
        .unwrap();
    let base = member_description(block.clone());
    let offset = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(4),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let wrong_block = PointerBlock::Heap(940_107);
    let fielded = ResourceDescription::new(
        "reference".into(),
        base.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::Integer)]).unwrap(),
    );
    for invalid in [&offset, &fielded] {
        assert_eq!(
            established
                .checked_member_exchange(&block, invalid, true)
                .err(),
            Some(CreationRefusal::InvalidMember)
        );
    }
    assert_eq!(
        established
            .checked_member_exchange(&wrong_block, &base, true)
            .err(),
        Some(CreationRefusal::InvalidMember)
    );
    let callee = established.enter_call();
    assert_eq!(
        callee.observe(&block, "reference"),
        Err(CreationRefusal::MissingAuthority)
    );
    assert_eq!(
        callee.checked_member_exchange(&block, &base, true).err(),
        Some(CreationRefusal::MissingAuthority)
    );
}

#[test]
fn opaque_nested_numeric_custody_transfer_and_return() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_opaque_contract_population(&description, 2)
        .unwrap();
    assert!(entry.tracks_population(&description));
    let child = entry.enter_call();
    assert!(matches!(
        child.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingAuthority)
    ));
    let sent = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap();
    assert_eq!(
        sent,
        child
            .transfer_call_fact(&entry, &child, &description, true)
            .unwrap()
    );
    assert!(sent.owns_population_authority(&description));
    assert!(
        !sent
            .return_to(&entry)
            .owns_population_authority(&description)
    );
    assert!(matches!(
        sent.checked_member_exchange(&PointerBlock::ExternalArgument, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
    let sent = sent
        .transfer_call_fact(&entry, &child, &description, false)
        .unwrap();
    assert_eq!(
        sent.0
            .opaque_imports
            .get(&description)
            .unwrap()
            .owned_members,
        2
    );
    assert_eq!(
        sent.finish_call(&entry),
        Err(CreationRefusal::OutstandingOwnership)
    );
    let (spent, _) = sent
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert_eq!(
        spent
            .0
            .opaque_imports
            .get(&description)
            .unwrap()
            .owned_members,
        1
    );
    assert!(!spent.owns_population_member(&description));
    let returned = spent
        .transfer_call_fact(&child, &entry, &description, true)
        .unwrap();
    let returned = returned.finish_call(&entry).unwrap();
    assert!(returned.owns_population_authority(&description));
    assert!(returned.owns_population_member(&description));
    assert!(returned.spent_imported_member_since(&entry, &description));
    assert_eq!(
        returned
            .0
            .opaque_imports
            .get(&description)
            .unwrap()
            .owned_members,
        1
    );
}

#[test]
fn opaque_returned_authority_cannot_strand_members() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_opaque_contract_population(&description, 1)
        .unwrap();
    let child = entry.enter_call();
    let sent = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap()
        .transfer_call_fact(&entry, &child, &description, false)
        .unwrap();
    let authority_returned = sent
        .transfer_call_fact(&child, &entry, &description, true)
        .unwrap();
    assert_eq!(
        authority_returned.finish_call(&entry),
        Err(CreationRefusal::OutstandingOwnership)
    );
    assert!(matches!(
        authority_returned.checked_member_exchange(
            &PointerBlock::ExternalArgument,
            &description,
            false
        ),
        Err(CreationRefusal::MissingAuthority)
    ));
    let all_returned = authority_returned
        .transfer_call_fact(&child, &entry, &description, false)
        .unwrap()
        .finish_call(&entry)
        .unwrap();
    assert!(all_returned.owns_population_member(&description));
    assert_eq!(
        all_returned.imported_member_delta_since_entry(&description),
        None
    );
}

#[test]
fn opaque_symbolic_nested_transfer_refuses_splitting_and_preserves_global_total() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(Bitvector32Term::Constant(7)),
            Some(Bitvector32Term::Constant(3)),
            None,
        )
        .unwrap();
    let child = entry.enter_call();
    let authority_only = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap();
    assert_eq!(
        authority_only.transfer_call_fact_quantity(
            &entry,
            &child,
            &description,
            false,
            &Bitvector32Term::Constant(1),
            &PureFactContext::new()
        ),
        Err(CreationRefusal::InvalidQuantity)
    );
    let both = authority_only
        .transfer_call_fact_quantity(
            &entry,
            &child,
            &description,
            false,
            &Bitvector32Term::Constant(3),
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(both.owns_population_member(&description));
    assert_eq!(
        both.observe_symbolic(&description).unwrap().entry_count,
        Bitvector32Term::Constant(7)
    );
}

#[test]
fn proof_entry_keeps_opaque_assumptions_without_creator_privilege() {
    let description = member_description(PointerBlock::ExternalArgument);
    let imported = CreationEvents::new()
        .import_opaque_contract_population(&description, 1)
        .unwrap();
    let block = PointerBlock::Heap(777);
    let created = imported.created(block.clone());
    let proof = created.enter_proof_entry();
    assert!(proof.owns_population_authority(&description));
    assert!(!proof.created_here(&block));
    assert_eq!(
        proof.establish(&block, "reference"),
        Err(CreationRefusal::NotCreationEnvironment)
    );
}

#[test]
fn opaque_transfer_and_finish_index_scale_with_selected_population() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let description_at = |id| {
            ResourceDescription::new(
                "reference".into(),
                vec![
                    CValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(970_000 + id)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            )
        };
        let mut entry = CreationEvents::new();
        for id in 0..size {
            entry = entry
                .import_opaque_contract_population(&description_at(id), 1)
                .unwrap();
        }
        let selected = description_at(size / 2);
        let child = entry.enter_call();
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            let sent = child
                .transfer_call_fact(&entry, &child, &selected, true)
                .unwrap()
                .transfer_call_fact(&entry, &child, &selected, false)
                .unwrap();
            assert_eq!(
                sent.finish_call(&entry),
                Err(CreationRefusal::OutstandingOwnership)
            );
            let returned = sent
                .transfer_call_fact(&child, &entry, &selected, true)
                .unwrap()
                .transfer_call_fact(&child, &entry, &selected, false)
                .unwrap()
                .finish_call(&entry)
                .unwrap();
            assert!(returned.owns_population_authority(&selected));
            assert!(returned.owns_population_member(&selected));
        });
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 40, "{work:?}");
}

#[test]
fn checked_empty_retirement_survives_free_but_not_a_new_lifetime() {
    let block = PointerBlock::Heap(980_100);
    let description = member_description(block.clone());
    let created = CreationEvents::new().created(block.clone());
    assert!(!created.checked_empty_population(&description));
    let (established, _) = created.checked_establish(&block, &description).unwrap();
    assert!(!established.checked_empty_population(&description));
    let (retired, _) = established.checked_retire(&block, &description).unwrap();
    assert!(retired.checked_empty_population(&description));
    assert!(!retired.owns_population_authority(&description));
    assert!(
        retired
            .checked_member_exchange(&block, &description, true)
            .is_err()
    );
    let freed = retired.retired(&block).unwrap();
    assert!(freed.checked_empty_population(&description));
    let wrong_family = ResourceDescription::new(
        "other_reference".into(),
        description.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(!freed.checked_empty_population(&wrong_family));
    let wrong_offset = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::pointer(Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(4),
            })
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    assert!(!freed.checked_empty_population(&wrong_offset));
    let recreated = freed.created(block.clone());
    assert!(!recreated.checked_empty_population(&description));
}

#[test]
fn opaque_retirement_requires_global_count_proof_not_local_exhaustion() {
    let description = member_description(PointerBlock::ExternalArgument);
    let entry_count = Bitvector32Term::Variable(Variable(980_200));
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            1,
            Some(entry_count.clone()),
            None,
            None,
        )
        .unwrap();
    let (spent, _) = entry
        .checked_member_exchange(&PointerBlock::ExternalArgument, &description, false)
        .unwrap();
    assert!(!spent.checked_empty_population(&description));
    assert_eq!(
        spent
            .checked_retire_imported(&description, &PureFactContext::new())
            .unwrap_err(),
        CreationRefusal::UnknownTotal
    );
    let wrong_total = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(entry_count.clone()),
            Box::new(Bitvector32Term::Constant(2)),
        ),
        true,
    ));
    assert!(
        spent
            .checked_retire_imported(&description, &wrong_total)
            .is_err()
    );
    let right_total = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(entry_count),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    ));
    let (retired, _) = spent
        .checked_retire_imported(&description, &right_total)
        .unwrap();
    assert!(retired.checked_empty_population(&description));
    assert!(!retired.owns_population_authority(&description));
}

#[test]
fn imported_retirement_supports_empty_and_complete_numeric_populations() {
    let description = member_description(PointerBlock::ExternalArgument);
    for quantity in [0, 1, 3, 2147483647] {
        let events = CreationEvents::new()
            .import_opaque_contract_population_inner(
                &description,
                quantity,
                Some(Bitvector32Term::Constant(quantity)),
                None,
                None,
            )
            .unwrap();
        let spent = if quantity == 0 {
            events
        } else {
            events
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    false,
                    &Bitvector32Term::Constant(quantity),
                    &PureFactContext::new(),
                )
                .unwrap()
                .0
        };
        let (retired, _) = spent
            .checked_retire_imported(&description, &PureFactContext::new())
            .unwrap();
        assert!(retired.checked_empty_population(&description));
        assert!(!retired.owns_population_authority(&description));
    }
}

#[test]
fn imported_symbolic_retirement_requires_spent_custody_and_global_zero() {
    let description = member_description(PointerBlock::ExternalArgument);
    let quantity = Bitvector32Term::Variable(Variable(980_210));
    let total = Bitvector32Term::Variable(Variable(980_211));
    let assumptions = PureFactContext::new().assume_condition(
        crate::kernel::ConditionTerm::signed_greater_equal(
            quantity.clone(),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let held = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(total.clone()),
            Some(quantity.clone()),
            None,
        )
        .unwrap();
    let total_zero = assumptions.clone().assume_condition(
        crate::kernel::ConditionTerm::Bitvector32Equal(
            Box::new(total.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    assert_eq!(
        held.check_imported_retirement(&description, &total_zero),
        Err(CreationRefusal::OutstandingMembers)
    );
    let spent = held
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            false,
            &quantity,
            &assumptions,
        )
        .unwrap()
        .0;
    assert_eq!(
        spent.check_imported_retirement(&description, &assumptions),
        Err(CreationRefusal::UnknownTotal)
    );
    let all_owned = assumptions.assume_condition(
        crate::kernel::ConditionTerm::Bitvector32Equal(Box::new(total), Box::new(quantity)),
        true,
    );
    let (retired, _) = spent
        .checked_retire_imported(&description, &all_owned)
        .unwrap();
    assert!(retired.checked_empty_population(&description));
    assert!(!retired.owns_population_authority(&description));
    assert!(retired.observe_symbolic(&description).is_none());
    assert_eq!(
        retired.imported_member_delta_since_entry(&description),
        spent.imported_member_delta_since_entry(&description),
    );
    assert!(
        retired
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &description,
                true,
                &Bitvector32Term::Constant(1),
                &all_owned,
            )
            .is_err()
    );
    assert_eq!(
        retired.check_imported_retirement(&description, &all_owned),
        Err(CreationRefusal::MissingAuthority)
    );
}

#[test]
fn checked_empty_lookup_scales_over_unrelated_retired_populations() {
    let mut work = Vec::new();
    for size in [64_u64, 256, 1024] {
        let mut events = CreationEvents::new();
        for id in 0..size {
            let block = PointerBlock::Heap(990_000 + id);
            let description = member_description(block.clone());
            events = events.created(block.clone());
            events = events.checked_establish(&block, &description).unwrap().0;
            events = events.checked_retire(&block, &description).unwrap().0;
            events = events.retired(&block).unwrap();
        }
        let selected = member_description(PointerBlock::Heap(990_000 + size / 2));
        let ((), measured) = crate::persistent::measure_persistent_work(|| {
            assert!(events.checked_empty_population(&selected));
        });
        work.push(measured);
    }
    assert!(work[2] < work[0].saturating_mul(2) + 10, "{work:?}");
}

#[test]
fn opaque_numeric_count_keeps_multiple_births_and_deaths() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            2,
            Some(Bitvector32Term::Constant(7)),
            None,
            None,
        )
        .unwrap();
    let mut born = entry.clone();
    for expected in 1..=2 {
        born = born
            .checked_member_exchange(&block, &description, true)
            .unwrap()
            .0;
        assert_eq!(born.observe_symbolic(&description).unwrap().delta, expected);
    }
    let mut restored = born;
    for expected in [1, 0] {
        restored = restored
            .checked_member_exchange(&block, &description, false)
            .unwrap()
            .0;
        assert_eq!(
            restored.observe_symbolic(&description).unwrap().delta,
            expected
        );
    }
    for expected in [-1, -2] {
        restored = restored
            .checked_member_exchange(&block, &description, false)
            .unwrap()
            .0;
        assert_eq!(
            restored.observe_symbolic(&description).unwrap().delta,
            expected
        );
    }
    assert!(matches!(
        restored.checked_member_exchange(&block, &description, false),
        Err(CreationRefusal::MissingMembers)
    ));
}

#[test]
fn opaque_numeric_count_delta_survives_exact_call_custody() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let mut caller = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            1,
            Some(Bitvector32Term::Constant(7)),
            None,
            None,
        )
        .unwrap();
    for _ in 0..2 {
        caller = caller
            .checked_member_exchange(&block, &description, true)
            .unwrap()
            .0;
    }
    assert_eq!(caller.observe_symbolic(&description).unwrap().delta, 2);
    let child = caller.enter_call();
    let sent = child
        .transfer_call_fact(&caller, &child, &description, true)
        .unwrap()
        .transfer_call_fact(&caller, &child, &description, false)
        .unwrap();
    assert_eq!(sent.observe_symbolic(&description).unwrap().delta, 2);
    let returned = sent
        .transfer_call_fact(&child, &caller, &description, false)
        .unwrap()
        .transfer_call_fact(&child, &caller, &description, true)
        .unwrap()
        .finish_call(&caller)
        .unwrap();
    assert_eq!(returned.observe_symbolic(&description).unwrap().delta, 2);
}

#[test]
fn opaque_numeric_count_observation_uses_exact_magnitude_and_overflow_guard() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let [AlgebraicValue::C(pointer)] = description.arguments() else {
        panic!("pointer anchor")
    };
    let count = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::Value(pointer.clone()))],
    };
    let evaluate = |events: CreationEvents| {
        let mut state =
            CState::new()
                .with_population_creation_tracking()
                .with_resource_context(ResourceContext::new().unchecked_with_fact(
                    CResourceFact::own(CResource::PopulationAuthority(description.clone())),
                ));
        Arc::make_mut(&mut state.population_effects).creation = Some(events);
        crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            &state,
            &count,
            &PureFactContext::new(),
            &BTreeMap::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    };
    let import = |entry_count| {
        CreationEvents::new()
            .import_opaque_contract_population_inner(
                &description,
                2,
                Some(Bitvector32Term::Constant(entry_count)),
                None,
                None,
            )
            .unwrap()
    };
    let mut born = import(7);
    let mut spent = import(7);
    for _ in 0..2 {
        born = born
            .checked_member_exchange(&block, &description, true)
            .unwrap()
            .0;
        spent = spent
            .checked_member_exchange(&block, &description, false)
            .unwrap()
            .0;
    }
    assert_eq!(
        evaluate(born)[0].value,
        CValue::Int32(Bitvector32Term::Constant(9))
    );
    assert_eq!(
        evaluate(spent)[0].value,
        CValue::Int32(Bitvector32Term::Constant(5))
    );
    let mut overflow = import((i32::MAX - 1) as u32);
    for _ in 0..2 {
        overflow = overflow
            .checked_member_exchange(&block, &description, true)
            .unwrap()
            .0;
    }
    assert!(
        evaluate(overflow)[0]
            .obligations
            .iter()
            .any(|obligation| obligation.context() == Some("count(reference) fits in int32"))
    );
}

#[test]
fn count_alias_uses_only_a_checked_owned_authority_anchor() {
    let description = member_description(PointerBlock::ExternalArgument);
    let [AlgebraicValue::C(CValue::Pointer(anchor))] = description.arguments() else {
        panic!("pointer anchor")
    };
    let alias = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(9_850_100))),
            byte_width: 4,
        },
    };
    let count = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::Value(CValue::pointer(alias.clone())))],
    };
    let events = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            2,
            Some(Bitvector32Term::Constant(7)),
            None,
            None,
        )
        .unwrap();
    let mut state = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                CResource::PopulationAuthority(description.clone()),
            )),
        );
    Arc::make_mut(&mut state.population_effects).creation = Some(events);
    let equal = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(alias, anchor.pointer().clone()),
        true,
    );
    let evaluate = |state: &CState, assumptions: &PureFactContext| {
        crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            state,
            &count,
            assumptions,
            &BTreeMap::new(),
            &mut ExecutionBudget::default(),
        )
    };
    assert_eq!(
        evaluate(&state, &equal).unwrap()[0].value,
        CValue::Int32(Bitvector32Term::Constant(7))
    );
    assert!(
        evaluate(&state, &PureFactContext::new()).is_err(),
        "an unproved pointer alias cannot borrow the authority"
    );
    assert!(
        evaluate(
            &state.clone().with_resource_context(ResourceContext::new()),
            &equal
        )
        .is_err(),
        "pointer equality cannot supply missing ownership"
    );
    let mut foreign = state;
    Arc::make_mut(&mut foreign.population_effects).creation = Some(CreationEvents::new());
    assert!(
        evaluate(&foreign, &equal).is_err(),
        "an ownership head without authenticated ledger authority cannot supply a count"
    );
}

#[test]
fn count_alias_lookup_does_not_scan_unrelated_authority_heads() {
    let description = member_description(PointerBlock::ExternalArgument);
    let [AlgebraicValue::C(CValue::Pointer(anchor))] = description.arguments() else {
        panic!("pointer anchor")
    };
    let alias = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(9_850_101))),
            byte_width: 4,
        },
    };
    let count = SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![Some(SpecExpression::Value(CValue::pointer(alias.clone())))],
    };
    let equal = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(alias, anchor.pointer().clone()),
        true,
    );
    let samples = [64usize, 256, 1024].map(|size| {
        let events = CreationEvents::new()
            .import_opaque_contract_population_inner(
                &description,
                2,
                Some(Bitvector32Term::Constant(7)),
                None,
                None,
            )
            .unwrap();
        let mut resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
            CResource::PopulationAuthority(description.clone()),
        ));
        for index in 0..size {
            let other =
                member_description(PointerBlock::Symbolic(Variable(9_860_000 + index as u64)));
            resources = resources
                .unchecked_with_fact(CResourceFact::own(CResource::PopulationAuthority(other)));
        }
        let mut state = CState::new()
            .with_population_creation_tracking()
            .with_resource_context(resources);
        Arc::make_mut(&mut state.population_effects).creation = Some(events);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
                &state,
                &count,
                &equal,
                &BTreeMap::new(),
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        });
        assert_eq!(paths[0].value, CValue::Int32(Bitvector32Term::Constant(7)));
        work
    });
    assert!(samples[0] > 0, "lookup must charge its work: {samples:?}");
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 128),
        "authority alias lookup must grow at most logarithmically: {samples:?}"
    );
}

#[test]
fn allocation_companion_transfers_cleanup_without_creation_privilege() {
    let block = PointerBlock::Heap(990_811);
    let caller = CreationEvents::new().created(block.clone());
    let helper = caller.enter_call();
    let held = helper
        .transfer_call_anchor(&caller, &helper, &block)
        .unwrap();
    assert_eq!(
        held,
        helper
            .transfer_call_anchor(&caller, &helper, &block)
            .unwrap()
    );
    assert!(!held.created_here(&block));
    assert_eq!(
        held.establish(&block, "reference"),
        Err(CreationRefusal::NotCreationEnvironment)
    );
    assert!(
        !held
            .retired(&block)
            .unwrap()
            .finish_call(&caller)
            .unwrap()
            .tracks_storage_anchor(&block)
    );
}

#[test]
fn borrowed_allocation_companion_returns_its_cleanup_obligation() {
    let block = PointerBlock::Heap(990_812);
    let caller = CreationEvents::new().created(block.clone());
    let helper = caller.enter_call();
    let held = helper
        .transfer_call_anchor(&caller, &helper, &block)
        .unwrap();
    assert_eq!(
        held.finish_call(&caller),
        Err(CreationRefusal::OutstandingOwnership)
    );
    let returned = held
        .transfer_call_anchor(&held, &caller, &block)
        .unwrap()
        .finish_call(&caller)
        .unwrap();
    assert!(returned.created_here(&block));
    assert!(returned.retired(&block).is_ok());
}

#[test]
fn allocation_companion_cannot_free_storage_with_live_population() {
    let block = PointerBlock::Heap(990_813);
    let caller = CreationEvents::new()
        .created(block.clone())
        .establish(&block, "reference")
        .unwrap();
    let helper = caller.enter_call();
    let held = helper
        .transfer_call_anchor(&caller, &helper, &block)
        .unwrap();
    assert_eq!(
        held.retired(&block),
        Err(CreationRefusal::OutstandingAuthority)
    );
    let unrelated = CreationEvents::new();
    assert!(
        held.transfer_call_anchor(&unrelated, &caller, &block)
            .is_err()
    );
}

mod wildcard_scope_tests {
    use super::*;

    fn description(block: &PointerBlock, keys: &[u32]) -> ResourceDescription {
        let mut arguments = vec![
            CValue::pointer(Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            })
            .into(),
        ];
        arguments.extend(keys.iter().map(|key| AlgebraicValue::C(int32(*key))));
        ResourceDescription::new(
            "slot".into(),
            arguments.into(),
            ResourceFieldSchema::new(vec![]).unwrap(),
        )
    }
    fn scope(block: &PointerBlock, arity: usize) -> ResourceDescription {
        description(block, &[])
            .with_population_arity(arity)
            .unwrap()
    }

    fn opaque_scope(index: u32) -> (ResourceDescription, ResourceDescription) {
        let anchor = CValue::pointer(Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(i64::from(index) * 4),
        });
        let scope = ResourceDescription::new(
            "slot".into(),
            vec![anchor.clone().into()].into(),
            ResourceFieldSchema::new(vec![]).unwrap(),
        )
        .with_population_arity(2)
        .unwrap();
        let member = ResourceDescription::new(
            "slot".into(),
            vec![anchor.into(), int32(7).into()].into(),
            ResourceFieldSchema::new(vec![]).unwrap(),
        );
        (scope, member)
    }

    #[test]
    fn wildcard_helper_borrows_exact_member_without_asserting_total() {
        let (scope, member) = opaque_scope(1);
        let entry = CreationEvents::new();
        let imported = entry
            .import_opaque_wildcard_population(&scope, &member)
            .unwrap();
        let total = imported.observe_symbolic(&scope).unwrap().entry_count;
        assert!(matches!(total, Bitvector32Term::Variable(_)));
        assert!(imported.owns_imported_population_member(&member));
        assert!(!imported.owns_imported_population_member(&scope));
        assert_eq!(
            imported
                .import_opaque_wildcard_population(&scope, &member)
                .unwrap(),
            imported
        );
        let (wrong_pool, wrong_member) = opaque_scope(2);
        assert!(
            entry
                .import_opaque_wildcard_population(&scope, &wrong_member)
                .is_err()
        );
        assert!(!imported.owns_imported_population_member(&wrong_member));
        let mut different_arguments = member.arguments().to_vec();
        different_arguments[1] = int32(8).into();
        let different_member = ResourceDescription::new(
            "slot".into(),
            different_arguments.into(),
            member.schema().clone(),
        );
        assert!(
            imported
                .import_opaque_wildcard_population(&scope, &different_member)
                .is_err()
        );
        let helper = imported.enter_call();
        let held = imported
            .transfer_call_fact(&imported, &helper, &scope, true)
            .unwrap();
        assert!(held.observe_symbolic(&scope).is_none());
        assert!(
            held.transfer_call_fact(&imported, &helper, &different_member, false)
                .is_err()
        );
        let held = held
            .transfer_call_fact(&imported, &helper, &member, false)
            .unwrap()
            .return_to(&helper);
        assert!(held.observe_symbolic(&wrong_pool).is_none());
        assert_eq!(held.observe_symbolic(&scope).unwrap().entry_count, total);
        assert!(held.finish_call(&imported).is_err());
        assert!(
            held.checked_member_exchange(&PointerBlock::ExternalArgument, &member, true)
                .is_err()
        );
        let returned = held
            .transfer_call_fact(&helper, &imported, &member, false)
            .unwrap();
        let returned = returned
            .transfer_call_fact(&helper, &imported, &scope, true)
            .unwrap()
            .finish_call(&imported)
            .unwrap();
        assert_eq!(
            returned.observe_symbolic(&scope).unwrap().entry_count,
            total
        );
        assert!(returned.owns_imported_population_member(&member));
        assert!(
            returned
                .checked_establish(&PointerBlock::ExternalArgument, &scope)
                .is_err()
        );
    }

    #[test]
    fn wildcard_helper_transfer_does_not_scan_unrelated_imports() {
        let samples = [16_u32, 64, 256, 1024].map(|size| {
            let (scope, member) = opaque_scope(0);
            let mut entry = CreationEvents::new()
                .import_opaque_wildcard_population(&scope, &member)
                .unwrap();
            for index in 1..=size {
                let (other, member) = opaque_scope(index);
                entry = entry
                    .import_opaque_wildcard_population(&other, &member)
                    .unwrap();
            }
            let helper = entry.enter_call();
            let ((held, work), indexed_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let held = entry
                        .transfer_call_fact(&entry, &helper, &scope, true)
                        .unwrap();
                    held.transfer_call_fact(&entry, &helper, &member, false)
                        .unwrap()
                })
            });
            let held = held.return_to(&helper);
            assert!(held.owns_imported_population_member(&member));
            assert!(held.observe_symbolic(&scope).is_some());
            assert!(work > 0);
            indexed_work
        });
        assert!(samples[0] > 0, "{samples:?}");
        for (index, work) in samples.iter().enumerate() {
            assert!(*work <= samples[0] + 64 * index, "{samples:?}");
        }
    }

    #[test]
    fn wildcard_helper_death_checks_identity_custody_and_single_transition() {
        let (scope, member) = opaque_scope(0);
        let entry = CreationEvents::new()
            .import_opaque_wildcard_population(&scope, &member)
            .unwrap();
        let count = entry.observe_symbolic(&scope).unwrap();
        assert!(matches!(count.entry_count, Bitvector32Term::Variable(_)));
        assert_eq!(count.entry_owned_members, 1);
        let death = |events: &CreationEvents, candidate: &ResourceDescription| {
            events.checked_member_exchange(&PointerBlock::ExternalArgument, candidate, false)
        };
        let mut arguments = member.arguments().to_vec();
        arguments[1] = int32(8).into();
        let different =
            ResourceDescription::new("slot".into(), arguments.into(), member.schema().clone());
        assert!(death(&entry, &different).is_err());
        assert!(death(&entry, &opaque_scope(1).1).is_err());
        let helper = entry.enter_call();
        let authority_away = entry
            .transfer_call_fact(&entry, &helper, &scope, true)
            .unwrap();
        assert!(death(&authority_away, &member).is_err());
        let member_away = entry
            .transfer_call_fact(&entry, &helper, &member, false)
            .unwrap();
        assert!(death(&member_away, &member).is_err());
        let (spent, certificate) = death(&entry, &member).unwrap();
        assert!(certificate.matches(&entry, &spent, &member, false));
        assert!(!certificate.matches(&entry, &spent, &different, false));
        assert!(!certificate.matches(&entry, &spent, &member, true));
        assert!(!spent.owns_imported_population_member(&member));
        let after = spent.observe_symbolic(&scope).unwrap();
        assert_eq!(after.entry_count, count.entry_count);
        assert_eq!(after.delta, -1);
        assert_eq!(
            spent.imported_member_delta_since_entry(&member),
            Some((false, Bitvector32Term::Constant(1)))
        );
        assert!(
            spent
                .imported_member_delta_since_entry(&different)
                .is_none()
        );
        assert!(death(&spent, &member).is_err());
        assert!(
            spent
                .checked_member_exchange(&PointerBlock::ExternalArgument, &member, true)
                .is_err()
        );
        assert!(
            spent
                .checked_establish(&PointerBlock::ExternalArgument, &scope)
                .is_err()
        );
    }

    #[test]
    fn wildcard_helper_death_does_not_scan_unrelated_imports() {
        let samples = [16_u32, 64, 256, 1024].map(|size| {
            let (scope, member) = opaque_scope(0);
            let mut entry = CreationEvents::new()
                .import_opaque_wildcard_population(&scope, &member)
                .unwrap();
            for index in 1..=size {
                entry = entry
                    .import_opaque_wildcard_authority(&opaque_scope(index).0)
                    .unwrap();
            }
            let (spent, work) = crate::persistent::measure_persistent_work(|| {
                entry
                    .checked_member_exchange(&PointerBlock::ExternalArgument, &member, false)
                    .unwrap()
                    .0
            });
            assert_eq!(spent.observe_symbolic(&scope).unwrap().delta, -1);
            assert_eq!(spent.observe_symbolic(&opaque_scope(1).0).unwrap().delta, 0);
            work
        });
        assert!(samples[0] > 0, "{samples:?}");
        for (index, work) in samples.iter().enumerate() {
            assert!(*work <= samples[0] + 32 * index, "{samples:?}");
        }
    }

    #[test]
    fn empty_opaque_population_entails_zero_for_every_exact_member() {
        let (scope, member) = opaque_scope(0);
        let entry = CreationEvents::new()
            .import_opaque_wildcard_authority(&scope)
            .unwrap();
        let count = entry.observe_symbolic(&scope).unwrap().entry_count;
        let empty = PureFactContext::new().assume_condition(
            ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(0)),
            true,
        );
        assert_eq!(
            entry
                .observe_exact_member(&member, &empty)
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(0)
        );
        let nonempty = PureFactContext::new().assume_condition(
            ConditionTerm::equal(count, Bitvector32Term::Constant(1)),
            true,
        );
        assert!(matches!(
            entry
                .observe_exact_member(&member, &nonempty)
                .unwrap()
                .entry_count,
            Bitvector32Term::Variable(_)
        ));
        let child = entry.enter_call();
        let away = entry
            .transfer_call_fact(&entry, &child, &scope, true)
            .unwrap();
        assert!(away.observe_exact_member(&member, &empty).is_err());
    }

    #[test]
    fn exclusive_wildcard_members_keep_exact_custody_through_a_call() {
        let (scope, first) = opaque_scope(0);
        let different = |index| {
            let mut arguments = first.arguments().to_vec();
            arguments[1] = int32(index).into();
            ResourceDescription::new(
                first.family().into(),
                arguments.into(),
                first.schema().clone(),
            )
        };
        let second = different(8);
        let wrong = different(9);
        let entry = CreationEvents::new()
            .import_opaque_wildcard_authority(&scope)
            .unwrap();
        let count = entry.observe_symbolic(&scope).unwrap().entry_count;
        let bounds = PureFactContext::new().assume_condition(
            ConditionTerm::signed_greater_equal(
                Bitvector32Term::Constant(i32::MAX as u32 - 3),
                count,
            ),
            true,
        );
        let birth = |events: &CreationEvents, member: &ResourceDescription| {
            events
                .checked_exclusive_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    member,
                    true,
                    &Bitvector32Term::Constant(1),
                    &bounds,
                )
                .unwrap()
                .0
        };
        let one = birth(&entry, &first);
        let two = birth(&one, &second);
        assert_eq!(two.observe_symbolic(&scope).unwrap().delta, 2);
        assert!(two.owns_imported_population_member(&first));
        assert!(two.owns_imported_population_member(&second));
        assert!(!two.owns_imported_population_member(&wrong));
        assert!(
            two.checked_member_exchange(&PointerBlock::ExternalArgument, &wrong, false)
                .is_err()
        );
        assert!(two.observe_exact_member(&wrong, &bounds).is_err());
        assert_eq!(
            two.observe_exact_member(&first, &bounds)
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(1)
        );
        let child = two.enter_call();
        let sent_first = child
            .transfer_call_fact(&two, &child, &scope, true)
            .unwrap()
            .transfer_call_fact(&two, &child, &first, false)
            .unwrap();
        let sent_second = child
            .transfer_call_fact(&two, &child, &scope, true)
            .unwrap()
            .transfer_call_fact(&two, &child, &second, false)
            .unwrap();
        assert_ne!(
            sent_first, sent_second,
            "memoization must include exact member identity"
        );
        assert!(sent_first.owns_imported_population_member(&first));
        assert!(!sent_first.owns_imported_population_member(&second));
        assert!(
            sent_first
                .checked_member_exchange(&PointerBlock::ExternalArgument, &second, false)
                .is_err()
        );
        let spent = sent_first
            .checked_member_exchange(&PointerBlock::ExternalArgument, &first, false)
            .unwrap()
            .0;
        assert!(
            spent
                .checked_member_exchange(&PointerBlock::ExternalArgument, &first, false)
                .is_err()
        );
        let returned = spent
            .transfer_call_fact(&child, &two, &scope, true)
            .unwrap()
            .finish_call(&two)
            .unwrap();
        assert!(!returned.owns_imported_population_member(&first));
        assert!(returned.owns_imported_population_member(&second));
        assert_eq!(returned.observe_symbolic(&scope).unwrap().delta, 1);
        assert_eq!(
            returned
                .observe_exact_member(&first, &bounds)
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(0)
        );
        let three = birth(&returned, &wrong);
        assert!(
            three.observe_exact_member(&first, &bounds).is_err(),
            "a later unresolved birth cannot preserve an old exact absence"
        );
        assert_eq!(
            three
                .observe_exact_member(&second, &bounds)
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(1)
        );
    }

    #[test]
    fn exclusive_member_update_and_transfer_scale_over_neighboring_members() {
        let samples = [16_u32, 64, 256, 1024].map(|size| {
            let (scope, first) = opaque_scope(0);
            let at = |index| {
                let mut arguments = first.arguments().to_vec();
                arguments[1] = int32(index).into();
                ResourceDescription::new(
                    first.family().into(),
                    arguments.into(),
                    first.schema().clone(),
                )
            };
            let mut events = CreationEvents::new()
                .import_opaque_wildcard_authority(&scope)
                .unwrap();
            let bounds = PureFactContext::new().assume_condition(
                ConditionTerm::signed_greater_equal(
                    Bitvector32Term::Constant(i32::MAX as u32 - size - 1),
                    events.observe_symbolic(&scope).unwrap().entry_count,
                ),
                true,
            );
            for index in 0..size {
                events = events
                    .checked_exclusive_member_exchange_quantity(
                        &PointerBlock::ExternalArgument,
                        &at(index),
                        true,
                        &Bitvector32Term::Constant(1),
                        &bounds,
                    )
                    .unwrap()
                    .0;
            }
            let selected = at(size / 2);
            let child = events.enter_call();
            let ((), work) = crate::persistent::measure_persistent_work(|| {
                let sent = child
                    .transfer_call_fact(&events, &child, &scope, true)
                    .unwrap()
                    .transfer_call_fact(&events, &child, &selected, false)
                    .unwrap();
                let spent = sent
                    .checked_member_exchange(&PointerBlock::ExternalArgument, &selected, false)
                    .unwrap()
                    .0;
                let returned = spent
                    .transfer_call_fact(&child, &events, &scope, true)
                    .unwrap()
                    .finish_call(&events)
                    .unwrap();
                assert!(!returned.owns_imported_population_member(&selected));
                assert!(returned.owns_imported_population_member(&at(0)));
                assert_eq!(
                    returned.observe_symbolic(&scope).unwrap().delta,
                    size as i32 - 1
                );
            });
            work
        });
        assert!(samples[0] > 0, "{samples:?}");
        for (index, work) in samples.iter().enumerate() {
            assert!(*work <= samples[0] + 80 * index, "{samples:?}");
        }
    }

    #[test]
    fn wildcard_helper_birth_and_consumption_check_bound_identity_and_custody() {
        let (scope, member) = opaque_scope(0);
        let entry = CreationEvents::new()
            .import_opaque_wildcard_authority(&scope)
            .unwrap();
        let count = entry.observe_symbolic(&scope).unwrap();
        assert!(matches!(count.entry_count, Bitvector32Term::Variable(_)));
        assert_eq!(count.entry_owned_members, 0);
        assert!(!entry.owns_imported_population_member(&member));
        let bounded = PureFactContext::new().assume_condition(
            crate::kernel::ConditionTerm::signed_add_overflows(
                count.entry_count.clone(),
                Bitvector32Term::Constant(1),
            ),
            false,
        );
        let birth = |events: &CreationEvents,
                     candidate: &ResourceDescription,
                     assumptions: &PureFactContext| {
            events.checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                candidate,
                true,
                &Bitvector32Term::Constant(1),
                assumptions,
            )
        };
        assert!(birth(&entry, &member, &PureFactContext::new()).is_err());
        let (wrong_scope, wrong_member) = opaque_scope(1);
        assert!(birth(&entry, &wrong_member, &bounded).is_err());
        let other = entry
            .import_opaque_wildcard_authority(&wrong_scope)
            .unwrap();
        assert!(birth(&other, &wrong_member, &bounded).is_err());
        let (issued, certificate) = birth(&entry, &member, &bounded).unwrap();
        assert!(certificate.matches(&entry, &issued, &member, true));
        assert!(!certificate.matches(&entry, &issued, &wrong_member, true));
        assert_eq!(issued.observe_symbolic(&scope).unwrap().delta, 1);
        assert!(issued.owns_imported_population_member(&member));
        assert_eq!(
            issued.imported_member_delta_since_entry(&member),
            Some((true, Bitvector32Term::Constant(1)))
        );
        assert!(
            issued
                .imported_member_delta_since_entry(&wrong_member)
                .is_none()
        );
        let mut arguments = member.arguments().to_vec();
        arguments[1] = int32(8).into();
        let different =
            ResourceDescription::new("slot".into(), arguments.into(), member.schema().clone());
        assert!(
            issued
                .imported_member_delta_since_entry(&different)
                .is_none()
        );
        assert!(birth(&issued, &different, &bounded).is_err());
        assert!(
            issued
                .checked_member_exchange(&PointerBlock::ExternalArgument, &different, false)
                .is_err()
        );
        let (returned, death) = issued
            .checked_member_exchange(&PointerBlock::ExternalArgument, &member, false)
            .unwrap();
        assert!(death.matches(&issued, &returned, &member, false));
        assert!(!death.matches(&issued, &returned, &different, false));
        let restored = returned.observe_symbolic(&scope).unwrap();
        assert_eq!(restored.entry_count, count.entry_count);
        assert_eq!(restored.delta, 0);
        assert!(!returned.owns_imported_population_member(&member));
        assert!(
            returned
                .checked_member_exchange(&PointerBlock::ExternalArgument, &member, false)
                .is_err()
        );

        assert!(
            issued
                .checked_establish(&PointerBlock::ExternalArgument, &scope)
                .is_err()
        );
    }

    #[test]
    fn wildcard_helper_birth_does_not_scan_unrelated_imports() {
        let samples = [16_u32, 64, 256, 1024].map(|size| {
            let (scope, member) = opaque_scope(0);
            let mut entry = CreationEvents::new()
                .import_opaque_wildcard_authority(&scope)
                .unwrap();
            for index in 1..=size {
                entry = entry
                    .import_opaque_wildcard_authority(&opaque_scope(index).0)
                    .unwrap();
            }
            let bounded = PureFactContext::new().assume_condition(
                crate::kernel::ConditionTerm::signed_add_overflows(
                    entry.observe_symbolic(&scope).unwrap().entry_count,
                    Bitvector32Term::Constant(1),
                ),
                false,
            );
            let (issued, work) = crate::persistent::measure_persistent_work(|| {
                entry
                    .checked_member_exchange_quantity(
                        &PointerBlock::ExternalArgument,
                        &member,
                        true,
                        &Bitvector32Term::Constant(1),
                        &bounded,
                    )
                    .unwrap()
                    .0
            });
            assert_eq!(issued.observe_symbolic(&scope).unwrap().delta, 1);
            assert_eq!(
                issued.observe_symbolic(&opaque_scope(1).0).unwrap().delta,
                0
            );
            work
        });
        assert!(samples[0] > 0, "{samples:?}");
        for (index, work) in samples.iter().enumerate() {
            assert!(*work <= samples[0] + 32 * index, "{samples:?}");
        }
    }

    #[test]
    fn local_numeric_batch_preserves_exact_wildcard_counts() {
        let pool = PointerBlock::Heap(991_202);
        let scope = scope(&pool, 2);
        let selected = description(&pool, &[1]);
        let other = description(&pool, &[2]);
        let empty = CreationEvents::new()
            .created(pool.clone())
            .checked_establish(&pool, &scope)
            .unwrap()
            .0;
        let facts = PureFactContext::new();
        let issued = empty
            .checked_member_exchange_quantity(
                &pool,
                &selected,
                true,
                &Bitvector32Term::Constant(3),
                &facts,
            )
            .unwrap()
            .0;
        let spent = issued
            .checked_member_exchange_quantity(
                &pool,
                &selected,
                false,
                &Bitvector32Term::Constant(2),
                &facts,
            )
            .unwrap()
            .0;
        assert_eq!(spent.observe(&pool, scope.family()), Ok(1));
        assert_eq!(
            spent
                .observe_exact_member(&selected, &facts)
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(1)
        );
        assert_eq!(
            spent
                .observe_exact_member(&other, &facts)
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(0)
        );
        assert!(
            spent
                .checked_member_exchange_quantity(
                    &pool,
                    &other,
                    false,
                    &Bitvector32Term::Constant(1),
                    &facts,
                )
                .is_err()
        );
    }

    #[test]
    fn exact_counts_preserve_multiplicity_and_require_current_authority() {
        let pool = PointerBlock::Heap(950_001);
        let scope = scope(&pool, 3);
        let (empty, _) = CreationEvents::new()
            .created(pool.clone())
            .checked_establish(&pool, &scope)
            .unwrap();
        let first = description(&pool, &[1, 10]);
        let second = description(&pool, &[2, 20]);
        let assumptions = PureFactContext::new();
        let count = |events: &CreationEvents, member: &ResourceDescription| {
            events
                .observe_exact_member(member, &assumptions)
                .unwrap()
                .entry_count
        };
        assert_eq!(count(&empty, &first), Bitvector32Term::Constant(0));
        let (one, _) = empty.checked_member_exchange(&pool, &first, true).unwrap();
        let (two, _) = one.checked_member_exchange(&pool, &first, true).unwrap();
        let (three, _) = two.checked_member_exchange(&pool, &second, true).unwrap();
        assert_eq!(count(&three, &first), Bitvector32Term::Constant(2));
        assert_eq!(count(&three, &second), Bitvector32Term::Constant(1));
        let (spent, _) = three.checked_member_exchange(&pool, &first, false).unwrap();
        assert_eq!(count(&spent, &first), Bitvector32Term::Constant(1));
        assert_eq!(count(&spent, &second), Bitvector32Term::Constant(1));
        let helper = spent.enter_call();
        let transferred = spent
            .transfer_call_fact(&spent, &helper, &scope, true)
            .unwrap();
        assert!(
            transferred
                .observe_exact_member(&first, &assumptions)
                .is_err()
        );
        let held = transferred.return_to(&helper);
        assert_eq!(count(&held, &first), Bitvector32Term::Constant(1));
    }

    #[test]
    fn exact_helper_count_is_arbitrary_and_survives_checked_consumption() {
        let (scope, member) = opaque_scope(0);
        let entry = CreationEvents::new()
            .import_opaque_wildcard_population(&scope, &member)
            .unwrap();
        let assumptions = PureFactContext::new();
        let exact = entry.observe_exact_member(&member, &assumptions).unwrap();
        let total = entry.observe_symbolic(&scope).unwrap();
        assert!(matches!(exact.entry_count, Bitvector32Term::Variable(_)));
        assert_ne!(exact.entry_count, total.entry_count);
        assert_eq!(exact.entry_owned_members, 1);
        assert_eq!(exact.delta, 0);
        let (spent, _) = entry
            .checked_member_exchange(&PointerBlock::ExternalArgument, &member, false)
            .unwrap();
        let after = spent.observe_exact_member(&member, &assumptions).unwrap();
        assert_eq!(after.entry_count, exact.entry_count);
        assert_eq!(after.delta, -1);
        assert_eq!(
            entry
                .observe_exact_member(&member, &assumptions)
                .unwrap()
                .delta,
            0
        );
        let (_, foreign) = opaque_scope(1);
        assert!(spent.observe_exact_member(&foreign, &assumptions).is_err());
    }

    #[test]
    fn exact_counts_do_not_treat_unresolved_indices_as_absent() {
        let pool = PointerBlock::Heap(950_002);
        let scope = scope(&pool, 2);
        let (empty, _) = CreationEvents::new()
            .created(pool.clone())
            .checked_establish(&pool, &scope)
            .unwrap();
        let known = description(&pool, &[7]);
        let mut arguments = known.arguments().to_vec();
        arguments[1] = AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
            Variable::allocate_fresh().unwrap(),
        )));
        let unknown =
            ResourceDescription::new("slot".into(), arguments.into(), known.schema().clone());
        let (one, _) = empty
            .checked_member_exchange(&pool, &unknown, true)
            .unwrap();
        assert!(
            one.observe_exact_member(&known, &PureFactContext::new())
                .is_err()
        );
        let (zero, _) = one.checked_member_exchange(&pool, &unknown, false).unwrap();
        assert_eq!(
            zero.observe_exact_member(&known, &PureFactContext::new())
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(0)
        );
    }

    #[test]
    fn exact_count_identity_ignores_pointer_casts_and_qualifiers() {
        let pool = PointerBlock::Heap(950_004);
        let scope = scope(&pool, 2);
        let (empty, _) = CreationEvents::new()
            .created(pool.clone())
            .checked_establish(&pool, &scope)
            .unwrap();
        let mut arguments = description(&pool, &[0]).arguments().to_vec();
        let pointer = CValue::pointer(Pointer {
            block: PointerBlock::Heap(950_005),
            offset: PointerOffsetTerm::Constant(4),
        });
        arguments[1] = pointer.clone().into();
        let member = ResourceDescription::new(
            "slot".into(),
            arguments.clone().into(),
            scope.schema().clone(),
        );
        let (one, _) = empty.checked_member_exchange(&pool, &member, true).unwrap();
        let CValue::Pointer(pointer) = pointer else {
            unreachable!()
        };
        arguments[1] = CValue::Pointer(
            pointer
                .with_type(CType::VoidPointer)
                .with_pointee_constant(true),
        )
        .into();
        let cast =
            ResourceDescription::new("slot".into(), arguments.into(), scope.schema().clone());
        assert_eq!(
            one.observe_exact_member(&cast, &PureFactContext::new())
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(1)
        );
        let (zero, _) = one.checked_member_exchange(&pool, &cast, false).unwrap();
        assert_eq!(
            zero.observe_exact_member(&member, &PureFactContext::new())
                .unwrap()
                .entry_count,
            Bitvector32Term::Constant(0)
        );
    }

    #[test]
    fn exact_count_never_reports_zero_for_an_unindexed_batch() {
        let pool = PointerBlock::Heap(950_006);
        let scope = scope(&pool, 2);
        let (empty, _) = CreationEvents::new()
            .created(pool.clone())
            .checked_establish(&pool, &scope)
            .unwrap();
        let member = description(&pool, &[7]);
        let quantity = Bitvector32Term::Variable(Variable::allocate_fresh().unwrap());
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    quantity.clone(),
                    Bitvector32Term::Constant(i32::MAX as u32),
                ),
                true,
            );
        let (batch, _) = empty
            .checked_member_exchange_quantity(&pool, &member, true, &quantity, &facts)
            .unwrap();
        assert_eq!(
            batch
                .observe_exact_member(&member, &PureFactContext::new())
                .err(),
            Some(CreationRefusal::UnknownTotal)
        );
    }

    #[test]
    fn exact_count_lookup_and_update_do_not_scan_neighboring_members() {
        let samples = [16, 64, 256].map(|size| {
            let pool = PointerBlock::Heap(950_003);
            let scope = scope(&pool, 2);
            let (mut events, _) = CreationEvents::new()
                .created(pool.clone())
                .checked_establish(&pool, &scope)
                .unwrap();
            for index in 0..size {
                events = events
                    .checked_member_exchange(&pool, &description(&pool, &[index]), true)
                    .unwrap()
                    .0;
            }
            let selected = description(&pool, &[0]);
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                assert_eq!(
                    events
                        .observe_exact_member(&selected, &PureFactContext::new())
                        .unwrap()
                        .entry_count,
                    Bitvector32Term::Constant(1)
                );
                let (spent, _) = events
                    .checked_member_exchange(&pool, &selected, false)
                    .unwrap();
                assert_eq!(
                    spent
                        .observe_exact_member(&selected, &PureFactContext::new())
                        .unwrap()
                        .entry_count,
                    Bitvector32Term::Constant(0)
                );
            });
            work
        });
        assert!(samples[0] > 0, "{samples:?}");
        for (index, work) in samples.iter().enumerate() {
            assert!(*work <= samples[0] + 64 * index, "{samples:?}");
        }
    }

    #[test]
    fn wildcard_scope_checks_signature_and_conserves_aggregate_total() {
        let pool = PointerBlock::Heap(920_001);
        let authority = scope(&pool, 3);
        let entry = CreationEvents::new().created(pool.clone());
        let (empty, _) = entry.checked_establish(&pool, &authority).unwrap();
        let first = description(&pool, &[1, 10]);
        let second = description(&pool, &[2, 20]);
        let (one, witness) = empty.checked_member_exchange(&pool, &first, true).unwrap();
        assert!(witness.matches(&empty, &one, &first, true));
        assert!(!witness.matches(&empty, &one, &second, true));
        let (two, _) = one.checked_member_exchange(&pool, &second, true).unwrap();
        assert_eq!(
            two.observe_term(&pool, "slot").unwrap(),
            Bitvector32Term::Constant(2)
        );
        assert_eq!(two.governing_authority(&first), Some(authority.clone()));
        assert!(two.checked_establish(&pool, &authority).is_err());
        assert!(two.checked_retire(&pool, &authority).is_err());
        assert!(
            two.checked_member_exchange(&pool, &description(&pool, &[1]), true)
                .is_err()
        );
        assert!(
            two.checked_member_exchange(&pool, &authority, true)
                .is_err()
        );
        let foreign = PointerBlock::Heap(920_002);
        assert!(
            two.checked_member_exchange(&foreign, &description(&foreign, &[1, 10]), true)
                .is_err()
        );
        let (one, _) = two.checked_member_exchange(&pool, &second, false).unwrap();
        let (zero, _) = one.checked_member_exchange(&pool, &first, false).unwrap();
        let (retired, _) = zero.checked_retire(&pool, &authority).unwrap();
        assert!(retired.checked_empty_population(&authority));
        assert!(!retired.checked_empty_population(&description(&pool, &[])));
        assert!(!retired.checked_empty_population(&scope(&pool, 2)));
        assert!(retired.checked_establish(&pool, &authority).is_err());
    }

    #[test]
    fn wildcard_scope_lookup_and_exchange_ignore_unrelated_pools() {
        let samples = [16_u64, 64, 256, 1024].map(|size| {
            let pool = PointerBlock::Heap(930_000);
            let mut events = CreationEvents::new().created(pool.clone());
            events = events.checked_establish(&pool, &scope(&pool, 2)).unwrap().0;
            for index in 1..=size {
                let other = PointerBlock::Heap(930_000 + index);
                events = events
                    .created(other.clone())
                    .checked_establish(&other, &scope(&other, 2))
                    .unwrap()
                    .0;
            }
            let member = description(&pool, &[1]);
            let ((next, _), work) = crate::instrumentation::measure_deterministic_work(|| {
                events
                    .checked_member_exchange(&pool, &member, true)
                    .unwrap()
            });
            assert_eq!(
                next.observe_term(&pool, "slot").unwrap(),
                Bitvector32Term::Constant(1)
            );
            assert_eq!(
                next.observe_term(&PointerBlock::Heap(930_001), "slot")
                    .unwrap(),
                Bitvector32Term::Constant(0)
            );
            work
        });
        assert!(samples[0] > 0, "{samples:?}");
        for (index, work) in samples.iter().enumerate() {
            assert!(*work <= samples[0] + 8 * index, "{samples:?}");
        }
    }
}

#[test]
fn retired_symbolic_batch_receipt_survives_helper_return_without_live_rights() {
    let description = member_description(PointerBlock::ExternalArgument);
    let quantity = Bitvector32Term::Variable(Variable(980_220));
    let assumptions = PureFactContext::new().assume_condition(
        crate::kernel::ConditionTerm::signed_greater_equal(
            quantity.clone(),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(quantity.clone()),
            Some(quantity.clone()),
            None,
        )
        .unwrap();
    let child = entry.enter_call();
    let authority = child
        .transfer_call_fact(&entry, &child, &description, true)
        .unwrap();
    let held = authority
        .transfer_call_fact_quantity(&entry, &child, &description, false, &quantity, &assumptions)
        .unwrap();
    let spent = held
        .checked_member_exchange_quantity(
            &PointerBlock::ExternalArgument,
            &description,
            false,
            &quantity,
            &assumptions,
        )
        .unwrap()
        .0;
    assert_eq!(
        spent.finish_call(&entry).unwrap_err(),
        CreationRefusal::OutstandingOwnership
    );
    let retired = spent
        .checked_retire_imported(&description, &assumptions)
        .unwrap()
        .0;
    let returned = retired.finish_call(&entry).unwrap();
    assert!(returned.retired_imported_authority_since(&entry, &description));
    assert_eq!(
        returned.imported_member_delta_since_entry(&description),
        Some((false, quantity))
    );
    assert!(returned.checked_empty_population(&description));
    assert!(!returned.owns_population_authority(&description));
    assert!(!returned.owns_population_member(&description));
    assert!(returned.observe_symbolic(&description).is_none());
    assert!(
        returned
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &description,
                true,
                &Bitvector32Term::Constant(1),
                &assumptions
            )
            .is_err()
    );
    assert_eq!(
        returned
            .checked_retire_imported(&description, &assumptions)
            .unwrap_err(),
        CreationRefusal::MissingAuthority
    );
}

#[test]
fn helper_cleanup_must_retire_each_control_population_at_global_zero() {
    let slots = member_description(PointerBlock::ExternalArgument);
    let private = ResourceDescription::new(
        "private".into(),
        slots.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    )
    .with_population_arity(2)
    .unwrap();
    let assumptions = PureFactContext::new();
    for private_total in [0, 1] {
        let entry = CreationEvents::new()
            .import_opaque_contract_population_inner(
                &slots,
                3,
                Some(Bitvector32Term::Constant(3)),
                None,
                None,
            )
            .unwrap()
            .import_opaque_contract_population_with_member(
                &private,
                0,
                Some(Bitvector32Term::Constant(private_total)),
                None,
                None,
                OpaqueMemberInputs::Quantity(None),
            )
            .unwrap();
        let child = entry.enter_call();
        let held = child
            .transfer_call_fact(&entry, &child, &slots, true)
            .unwrap()
            .transfer_call_fact(&entry, &child, &private, true)
            .unwrap()
            .transfer_call_fact_quantity(
                &entry,
                &child,
                &slots,
                false,
                &Bitvector32Term::Constant(3),
                &assumptions,
            )
            .unwrap();
        let spent = held
            .checked_member_exchange_quantity(
                &PointerBlock::ExternalArgument,
                &slots,
                false,
                &Bitvector32Term::Constant(3),
                &assumptions,
            )
            .unwrap()
            .0;
        let retired_slots = spent
            .checked_retire_imported(&slots, &assumptions)
            .unwrap()
            .0;
        assert_eq!(
            retired_slots.finish_call(&entry).unwrap_err(),
            CreationRefusal::OutstandingOwnership
        );
        let result = retired_slots.checked_retire_imported(&private, &assumptions);
        if private_total == 0 {
            let returned = result.unwrap().0.finish_call(&entry).unwrap();
            assert!(returned.checked_empty_population(&slots));
            assert!(returned.checked_empty_population(&private));
            assert!(!returned.owns_population_authority(&slots));
            assert!(!returned.owns_population_authority(&private));
        } else {
            assert_eq!(result.unwrap_err(), CreationRefusal::UnknownTotal);
        }
    }
}

#[test]
fn local_named_wildcard_members_count_occurrences_not_field_values() {
    let block = PointerBlock::Heap(940_502);
    let anchor = CValue::pointer(Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    });
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let scope = ResourceDescription::new(
        "ticket".into(),
        vec![anchor.clone().into()].into(),
        schema.clone(),
    )
    .with_population_arity(2)
    .unwrap();
    let created = CreationEvents::new().created(block.clone());
    let (empty, _) = created.checked_establish(&block, &scope).unwrap();
    let member = |tag, serial| {
        ResourceInstance::new(
            Variable::allocate_fresh().unwrap(),
            "ticket".into(),
            vec![anchor.clone().into(), int32(tag).into()].into(),
            schema.clone(),
            vec![int32(serial).into()].into(),
        )
        .unwrap()
    };
    let first = member(7, 1);
    let second = member(7, 2);
    let absent = member(8, 99);
    let one = empty
        .checked_instance_exchange(&ResourceReference::from_instance(&first), true)
        .unwrap();
    let two = one
        .checked_instance_exchange(&ResourceReference::from_instance(&second), true)
        .unwrap();
    let assumptions = PureFactContext::new();
    let exact = |events: &CreationEvents, instance: &ResourceInstance| {
        events
            .observe_exact_member(&ResourceDescription::from_instance(instance), &assumptions)
            .unwrap()
            .entry_count
            .as_const()
            .unwrap()
    };
    assert_eq!(two.observe(&block, "ticket"), Ok(2));
    assert_eq!(exact(&two, &first), 2);
    assert_eq!(exact(&two, &absent), 0);
    assert_eq!(
        two.checked_retire(&block, &scope).err(),
        Some(CreationRefusal::OutstandingMembers)
    );
    let one = two
        .checked_instance_exchange(&ResourceReference::from_instance(&first), false)
        .unwrap();
    assert_eq!(exact(&one, &second), 1);
    let zero = one
        .checked_instance_exchange(&ResourceReference::from_instance(&second), false)
        .unwrap();
    assert_eq!(exact(&zero, &first), 0);
    zero.checked_retire(&block, &scope).unwrap();
}

#[test]
fn local_numeric_batch_splits_and_requires_owned_authority() {
    let block = PointerBlock::Heap(991_200);
    let description = member_description(block.clone());
    let created = CreationEvents::new().created(block.clone());
    let exchange = |state: &CreationEvents, produce: bool, amount: u32| {
        state.checked_member_exchange_quantity(
            &block,
            &description,
            produce,
            &Bitvector32Term::Constant(amount),
            &PureFactContext::new(),
        )
    };
    assert!(exchange(&created, true, 0).is_err());
    let empty = created.checked_establish(&block, &description).unwrap().0;
    let three = exchange(&empty, true, 3).unwrap().0;
    assert_eq!(three.observe(&block, description.family()), Ok(3));
    assert!(three.checked_retire(&block, &description).is_err());
    let (two, certificate) = exchange(&three, false, 1).unwrap();
    assert!(certificate.matches(&three, &two, &description, false));
    assert!(!certificate.matches(&empty, &two, &description, false));
    assert_eq!(two.observe(&block, description.family()), Ok(2));
    assert!(exchange(&two, false, 3).is_err());
    let zero = exchange(&two, false, 2).unwrap().0;
    assert_eq!(zero.observe(&block, description.family()), Ok(0));
    assert!(exchange(&zero, false, 1).is_err());
    for produce in [false, true] {
        let unchanged = exchange(&zero, produce, 0).unwrap().0;
        assert_eq!(unchanged.observe(&block, description.family()), Ok(0));
    }
    let retired = zero.checked_retire(&block, &description).unwrap().0;
    assert!(exchange(&retired, true, 0).is_err());
    let maximum = exchange(&empty, true, i32::MAX as u32).unwrap().0;
    assert!(exchange(&maximum, true, 1).is_err());
    assert!(exchange(&empty, true, u32::MAX).is_err());
}

#[test]
fn local_numeric_batch_work_does_not_grow_with_quantity() {
    let block = PointerBlock::Heap(991_201);
    let description = member_description(block.clone());
    let empty = CreationEvents::new()
        .created(block.clone())
        .checked_establish(&block, &description)
        .unwrap()
        .0;
    let work = [2, 64, 65536, i32::MAX as u32].map(|amount| {
        let (issued, measured) = crate::persistent::measure_persistent_work(|| {
            empty
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &Bitvector32Term::Constant(amount),
                    &PureFactContext::new(),
                )
                .unwrap()
                .0
        });
        assert_eq!(issued.observe(&block, description.family()), Ok(amount));
        let (spent, consume_work) = crate::persistent::measure_persistent_work(|| {
            issued
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    false,
                    &Bitvector32Term::Constant(amount),
                    &PureFactContext::new(),
                )
                .unwrap()
                .0
        });
        assert_eq!(spent.observe(&block, description.family()), Ok(0));
        (measured, consume_work)
    });
    assert!(work[0].0 > 0 && work[0].1 > 0, "{work:?}");
    assert!(work.iter().all(|n| *n == work[0]), "{work:?}");
}

#[test]
fn authority_contract_entry_retains_only_authenticated_member_bounds() {
    let block = PointerBlock::ExternalArgument;
    let description = ResourceDescription::new(
        "reference".into(),
        vec![
            CValue::typed_pointer(
                Pointer {
                    block,
                    offset: PointerOffsetTerm::Constant(0),
                },
                CType::Int32Pointer,
            )
            .into(),
        ]
        .into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let authority = CResourceFact::own(CResource::PopulationAuthority(description.clone()));
    let member = CResourceFact::own(CResource::Composite {
        name: description.family().into(),
        arguments: description.arguments().to_vec().into(),
    });
    let member_spec = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "reference".into(),
        vec![c_variable("p")],
        vec![CType::Int32Pointer],
    );
    let authority_spec = CResourceSpec::new(
        CResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(member_spec.clone()),
                schema: description.schema().clone(),
            }),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let function = c_function(
        CType::Void,
        "inspect",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_void_value()),
    )
    .with_resource_summary(vec![authority_spec, member_spec.clone()], vec![])
    .with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
        "reference",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![],
        vec![],
    )]);
    let AlgebraicValue::C(pointer) = &description.arguments()[0] else {
        unreachable!();
    };
    let member_only_function = function
        .clone()
        .with_resource_summary(vec![member_spec], vec![]);
    for tracked_quantity in [0, 1] {
        let state = CState::new()
            .with_population_creation_tracking()
            .with_resource_context(
                ResourceContext::new().unchecked_with_facts([authority.clone(), member.clone()]),
            )
            .import_opaque_population(&authority, tracked_quantity)
            .unwrap();
        let count = state
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .observe_symbolic(&description)
            .unwrap()
            .entry_count;
        let entry =
            c_function_contract_entry(&state, &function, &[CExpression::Value(pointer.clone())])
                .unwrap();
        let lower_bound = Proposition::ConditionIs(
            // `states` is an exact lookup. Match the count evaluator's
            // canonical orientation, rather than asking it to prove `1 <= n`.
            ConditionTerm::signed_greater_equal(count.clone(), Bitvector32Term::Constant(1)),
            true,
        );
        assert_eq!(entry.states(&lower_bound), tracked_quantity == 1);
        assert!(
            !entry.states(&Proposition::ConditionIs(
                ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(1)),
                true
            )),
            "one locally owned member does not imply an exact global count"
        );
        let without_authority =
            state.with_resource_context(ResourceContext::new().unchecked_with_fact(member.clone()));
        let entry_without_authority = c_function_contract_entry(
            &without_authority,
            &member_only_function,
            &[CExpression::Value(pointer.clone())],
        )
        .unwrap();
        assert!(
            !entry_without_authority.states(&lower_bound),
            "ledger membership without owned authority does not authorize a count fact"
        );
    }
}

#[test]
fn named_authority_import_is_read_only_and_lookup_scales() {
    check_named_authority_import(None);
}

#[test]
fn wildcard_named_authority_import_is_read_only_and_lookup_scales() {
    for arity in [2, 3] {
        check_named_authority_import(Some(arity));
    }
}

fn check_named_authority_import(arity: Option<usize>) {
    let base = member_description(PointerBlock::ExternalArgument);
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let mut description = ResourceDescription::new(
        "ticket".into(),
        base.arguments().to_vec().into(),
        schema.clone(),
    );
    if let Some(arity) = arity {
        description = description.with_population_arity(arity).unwrap();
    }
    let mut pattern = ResourceDescription::new(
        "ticket".into(),
        description.arguments().to_vec().into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    if let Some(arity) = arity {
        pattern = pattern.with_population_arity(arity).unwrap();
    }
    let mut instance_arguments = description.arguments().to_vec();
    if let Some(arity) = arity {
        for key in 0..arity - 1 {
            instance_arguments.push(int32(7 + key as u32).into());
        }
    }
    let instance = ResourceInstance::new(
        Variable::allocate_fresh().unwrap(),
        "ticket".into(),
        instance_arguments.into(),
        schema,
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let reference = ResourceReference::from_instance(&instance);
    let authority = CResourceFact::own(CResource::PopulationAuthority(description.clone()));
    let resources = ResourceContext::new().unchecked_with_facts([
        authority.clone(),
        CResourceFact::own(CResource::Instance(instance.clone())),
    ]);
    let state = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(resources);
    let imported = if arity.is_some() {
        state.import_opaque_wildcard_authority(&authority).unwrap()
    } else {
        state.import_opaque_population_inputs(&authority).unwrap()
    };
    assert_eq!(imported.resources(), state.resources());
    assert_eq!(
        imported.owned_resource_instance(instance.identity()),
        Some(&instance)
    );
    assert!(
        state
            .clone()
            .with_resource_context(ResourceContext::new())
            .import_opaque_population_inputs(&authority)
            .is_err()
    );
    let doubled = CResourceFact::own_quantity(
        CResource::PopulationAuthority(description.clone()),
        Bitvector32Term::Constant(2),
    );
    assert!(
        state
            .clone()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(doubled.clone()))
            .import_opaque_population_inputs(&doubled)
            .is_err()
    );
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let mut source = CreationEvents::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("unrelated_{index}"),
                description.arguments().to_vec().into(),
                description.schema().clone(),
            );
            source = source
                .import_observable_named_authority(&unrelated)
                .unwrap();
        }
        // Same family, different explicit anchor: field recovery must not
        // select the first imported population merely by family or block.
        let other_pattern = pattern.map_values(|_| {
            AlgebraicValue::C(CValue::typed_pointer(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(4),
                },
                CType::Int32Pointer,
            ))
        });
        let mut other_description = ResourceDescription::new(
            "ticket".into(),
            other_pattern.arguments().to_vec().into(),
            description.schema().clone(),
        );
        if let Some(arity) = arity {
            other_description = other_description.with_population_arity(arity).unwrap();
        }
        source = source
            .import_observable_named_authority(&other_description)
            .unwrap();
        assert_eq!(
            source.population_type_description(&other_pattern),
            other_description
        );
        let (entry, measured) = crate::persistent::measure_persistent_work(|| {
            let entry = source
                .import_observable_named_authority(&description)
                .unwrap();
            assert_eq!(entry.population_type_description(&pattern), description);
            entry
        });
        work.push(measured);
        let exact = ResourceDescription::new(
            description.family().into(),
            instance.arguments().to_vec().into(),
            description.schema().clone(),
        );
        let exact_count = arity.map(|_| {
            let observed = entry
                .observe_exact_member(&exact, &PureFactContext::new())
                .unwrap();
            assert!(matches!(observed.entry_count, Bitvector32Term::Variable(_)));
            assert_eq!(observed.delta, 0);
            assert_eq!(observed.entry_owned_members, 0);
            assert_eq!(
                entry
                    .observe_exact_member(&exact, &PureFactContext::new())
                    .unwrap()
                    .entry_count,
                observed.entry_count
            );
            observed.entry_count
        });
        let count = entry.observe_symbolic(&description).unwrap();
        assert!(matches!(count.entry_count, Bitvector32Term::Variable(_)));
        assert_eq!(count.entry_owned_members, 0);
        assert_eq!(count.delta, 0);
        assert!(!entry.owns_population_member(&description));
        assert_eq!(
            entry
                .import_observable_named_authority(&description)
                .unwrap(),
            entry
        );
        assert_eq!(
            entry.checked_instance_exchange(&reference, false).err(),
            Some(CreationRefusal::InvalidMember)
        );
        assert_eq!(
            entry.checked_instance_exchange(&reference, true).err(),
            Some(CreationRefusal::InvalidMember)
        );
        for produce in [false, true] {
            assert_eq!(
                entry
                    .checked_member_exchange_quantity(
                        &PointerBlock::ExternalArgument,
                        &description,
                        produce,
                        &Bitvector32Term::Constant(1),
                        &PureFactContext::new(),
                    )
                    .err(),
                Some(CreationRefusal::InvalidMember)
            );
        }
        let mut wrong_schema = ResourceDescription::new(
            "ticket".into(),
            description.arguments().to_vec().into(),
            ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::UInt8))])
                .unwrap(),
        );
        if let Some(arity) = arity {
            wrong_schema = wrong_schema.with_population_arity(arity).unwrap();
        }
        assert_eq!(
            entry.import_observable_named_authority(&wrong_schema).err(),
            Some(CreationRefusal::OpaqueImportConflict)
        );
        assert_eq!(entry.population_type_description(&pattern), description);
        let helper = entry.enter_call();
        let moved = entry
            .transfer_call_fact(&entry, &helper, &description, true)
            .unwrap();
        assert!(moved.observe_symbolic(&description).is_none());
        assert_eq!(moved.population_type_description(&pattern), description);
        let held = moved.return_to(&helper);
        assert_eq!(
            held.observe_symbolic(&description).unwrap().entry_count,
            count.entry_count
        );
        assert!(
            held.transfer_call_fact(&entry, &helper, &description, true)
                .is_err()
        );
        assert!(
            held.transfer_call_fact(&entry, &helper, &description, false)
                .is_err()
        );
        let returned = held
            .transfer_call_fact(&helper, &entry, &description, true)
            .unwrap()
            .finish_call(&entry)
            .unwrap();
        if let Some(exact_count) = exact_count {
            assert_eq!(
                returned
                    .observe_exact_member(&exact, &PureFactContext::new())
                    .unwrap()
                    .entry_count,
                exact_count
            );
        }
        assert_eq!(
            returned.observe_symbolic(&description).unwrap().entry_count,
            count.entry_count
        );
    }
    assert!(work[0] > 0 && work[2] <= work[0] + 256, "{work:?}");
    assert!(
        CreationEvents::new()
            .import_observable_contract_population(&description, 0)
            .is_err()
    );
    assert!(
        CreationEvents::new()
            .created(PointerBlock::Heap(941_020))
            .import_observable_named_authority(&description)
            .is_err()
    );
}

#[test]
fn exact_symbolic_births_use_numeric_custody_and_scale() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let quantity = Bitvector32Term::Variable(Variable(990_001));
    let samples = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("exact-unrelated-{index}"),
                description.arguments().to_vec().into(),
                description.schema().clone(),
            );
            entry = entry
                .import_opaque_contract_population_inner(
                    &unrelated,
                    0,
                    Some(Bitvector32Term::Constant(0)),
                    None,
                    None,
                )
                .unwrap();
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(991_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );
        }
        entry = entry
            .import_opaque_contract_population_inner(
                &description,
                0,
                Some(Bitvector32Term::Constant(0)),
                None,
                None,
            )
            .unwrap();
        facts = facts.assume_condition(
            ConditionTerm::equal(quantity.clone(), Bitvector32Term::Constant(1_000_000_000)),
            true,
        );
        PureFactContext::reset_exact_constant_fact_visits();
        let (born, work) = crate::instrumentation::measure_deterministic_work(|| {
            let first = entry
                .checked_member_exchange_quantity(&block, &description, true, &quantity, &facts)
                .unwrap()
                .0;
            first
                .checked_member_exchange_quantity(&block, &description, true, &quantity, &facts)
                .unwrap()
                .0
        });
        assert_eq!(PureFactContext::exact_constant_fact_visits(), 2);
        assert_eq!(
            born.observe_symbolic(&description).unwrap().delta,
            2_000_000_000
        );
        assert!(
            born.0
                .opaque_imports
                .get(&description)
                .unwrap()
                .symbolic_delta
                .is_none()
        );
        assert!(
            born.checked_member_exchange_quantity(&block, &description, true, &quantity, &facts,)
                .is_err(),
            "a third billion must not wrap the population"
        );
        let child = born.enter_call();
        let sent = child
            .transfer_call_fact(&born, &child, &description, true)
            .unwrap()
            .transfer_call_fact_quantity(&born, &child, &description, false, &quantity, &facts)
            .unwrap();
        let spent = sent
            .checked_member_exchange_quantity(&block, &description, false, &quantity, &facts)
            .unwrap()
            .0;
        let returned = spent
            .transfer_call_fact(&child, &born, &description, true)
            .unwrap()
            .finish_call(&born)
            .unwrap();
        assert_eq!(
            returned.observe_symbolic(&description).unwrap().delta,
            1_000_000_000
        );
        assert!(returned.owns_population_member(&description));
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn exact_symbolic_birth_does_not_infer_custody_from_bounds() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let quantity = Bitvector32Term::Variable(Variable(990_002));
    let entry = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            0,
            Some(Bitvector32Term::Constant(0)),
            None,
            None,
        )
        .unwrap();
    let bounds = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(Bitvector32Term::Constant(10), quantity.clone()),
            true,
        );
    let first = entry
        .checked_member_exchange_quantity(&block, &description, true, &quantity, &bounds)
        .unwrap()
        .0;
    assert!(
        first
            .0
            .opaque_imports
            .get(&description)
            .unwrap()
            .symbolic_delta
            .is_some()
    );
    assert_eq!(
        first
            .checked_member_exchange_quantity(&block, &description, true, &quantity, &bounds,)
            .unwrap_err(),
        CreationRefusal::InvalidQuantity
    );
    let negative = PureFactContext::new().assume_condition(
        ConditionTerm::equal(quantity.clone(), Bitvector32Term::Constant(u32::MAX)),
        true,
    );
    assert!(
        entry
            .checked_member_exchange_quantity(&block, &description, true, &quantity, &negative,)
            .is_err()
    );
}

#[test]
fn numeric_member_birth_overflow_is_not_missing_custody() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let full = CreationEvents::new()
        .import_opaque_contract_population_inner(
            &description,
            i32::MAX as u32,
            Some(Bitvector32Term::Constant(i32::MAX as u32)),
            None,
            None,
        )
        .unwrap();
    assert_eq!(
        full.checked_member_exchange_quantity(
            &block,
            &description,
            true,
            &Bitvector32Term::Constant(1),
            &PureFactContext::new(),
        )
        .unwrap_err(),
        CreationRefusal::PopulationCountOverflow
    );
    assert!(full.owns_population_member(&description));
    assert_eq!(
        full.observe_symbolic(&description).unwrap().entry_count,
        Bitvector32Term::Constant(i32::MAX as u32)
    );
}

#[test]
fn opaque_repeated_symbolic_births_compose_and_return_without_scanning_unrelated_state() {
    let block = PointerBlock::ExternalArgument;
    let description = member_description(block.clone());
    let first_quantity = Bitvector32Term::Variable(Variable(992_001));
    let second_quantity = Bitvector32Term::Variable(Variable(992_002));
    let total = Bitvector32Term::add(first_quantity.clone(), second_quantity.clone());
    let samples = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("repeated-symbolic-unrelated-{index}"),
                description.arguments().to_vec().into(),
                description.schema().clone(),
            );
            entry = entry
                .import_opaque_contract_population_inner(
                    &unrelated,
                    0,
                    Some(Bitvector32Term::Constant(0)),
                    None,
                    None,
                )
                .unwrap();
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(993_000 + index)),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );
        }
        entry = entry
            .import_opaque_contract_population_inner(
                &description,
                0,
                Some(Bitvector32Term::Constant(0)),
                None,
                None,
            )
            .unwrap();
        for quantity in [&first_quantity, &second_quantity] {
            facts = facts.assume_condition(
                ConditionTerm::signed_greater_equal(quantity.clone(), Bitvector32Term::Constant(0)),
                true,
            );
        }
        let child = entry.enter_call();
        let authorized = child
            .transfer_call_fact(&entry, &child, &description, true)
            .unwrap();
        let first = authorized
            .checked_member_exchange_quantity(&block, &description, true, &first_quantity, &facts)
            .unwrap()
            .0;
        assert_eq!(
            first
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &second_quantity,
                    &facts,
                )
                .unwrap_err(),
            CreationRefusal::InvalidQuantity,
            "nonnegative quantities alone do not establish a non-wrapping total"
        );
        let current = Bitvector32Term::add(Bitvector32Term::Constant(0), first_quantity.clone());
        facts = facts.assume_condition(
            ConditionTerm::signed_add_overflows(current, second_quantity.clone()),
            false,
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let born = first
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &second_quantity,
                    &facts,
                )
                .unwrap()
                .0;
            assert_eq!(
                born.observe_symbolic(&description).unwrap().symbolic_delta,
                Some((true, total.clone()))
            );
            assert_eq!(
                born.0.opaque_holders.get(&child.0.opaque_actor),
                Some(&2),
                "the coalesced batch is one right beside the authority"
            );
            assert_eq!(
                born.transfer_call_fact_quantity(
                    &child,
                    &entry,
                    &description,
                    false,
                    &first_quantity,
                    &facts,
                )
                .unwrap_err(),
                CreationRefusal::InvalidQuantity,
                "a coalesced batch cannot silently split"
            );
            let sent = born
                .transfer_call_fact_quantity(&child, &entry, &description, false, &total, &facts)
                .unwrap();
            assert!(
                sent.checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &second_quantity,
                    &facts,
                )
                .is_err(),
                "authority alone cannot extend another actor's batch"
            );
            assert_eq!(
                sent.transfer_call_fact_quantity(
                    &child,
                    &entry,
                    &description,
                    false,
                    &total,
                    &facts,
                )
                .unwrap_err(),
                CreationRefusal::MissingMembers
            );
            let returned = sent
                .transfer_call_fact(&child, &entry, &description, true)
                .unwrap()
                .finish_call(&entry)
                .unwrap();
            assert!(returned.owns_population_authority(&description));
            assert!(returned.owns_population_member(&description));
            assert_eq!(
                returned
                    .observe_symbolic(&description)
                    .unwrap()
                    .symbolic_delta,
                Some((true, total.clone()))
            );
            facts = facts.assume_condition(
                ConditionTerm::signed_greater_equal(total.clone(), Bitvector32Term::Constant(0)),
                true,
            );
            assert!(
                returned
                    .checked_member_exchange_quantity(
                        &block,
                        &description,
                        false,
                        &first_quantity,
                        &facts,
                    )
                    .is_err(),
                "a whole batch cannot be partially retired"
            );
            let consumer = returned.enter_call();
            assert!(
                consumer
                    .checked_member_exchange_quantity(&block, &description, false, &total, &facts,)
                    .is_err(),
                "consumption requires transferred authority"
            );
            let authorized = consumer
                .transfer_call_fact(&returned, &consumer, &description, true)
                .unwrap()
                .transfer_call_fact_quantity(
                    &returned,
                    &consumer,
                    &description,
                    false,
                    &total,
                    &facts,
                )
                .unwrap();
            let spent = authorized
                .checked_member_exchange_quantity(&block, &description, false, &total, &facts)
                .unwrap()
                .0;
            assert_eq!(
                spent.observe_symbolic(&description).unwrap().symbolic_delta,
                None
            );
            assert_eq!(
                spent.0.opaque_holders.get(&consumer.0.opaque_actor),
                Some(&1)
            );
            assert!(
                spent
                    .checked_member_exchange_quantity(&block, &description, false, &total, &facts,)
                    .is_err(),
                "retirement cannot be repeated"
            );
            let finished = spent
                .transfer_call_fact(&consumer, &returned, &description, true)
                .unwrap()
                .finish_call(&returned)
                .unwrap();
            assert!(finished.owns_population_authority(&description));
            assert!(!finished.owns_population_member(&description));
        });
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn imported_named_consumption_counts_identities_and_ignores_unrelated_state() {
    let anchor = CValue::pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    });
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let description = ResourceDescription::new(
        "ticket".into(),
        vec![anchor.clone().into()].into(),
        schema.clone(),
    );
    let member = |identity| {
        ResourceInstance::new(
            Variable(identity),
            "ticket".into(),
            vec![anchor.clone().into()].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap()
    };
    let left = member(996_001);
    let right = member(996_002);
    let work = [16, 64, 256].map(|size| {
        let mut entry = CreationEvents::new();
        for index in 0..size {
            let unrelated = ResourceDescription::new(
                format!("unrelated-named-{index}"),
                description.arguments().to_vec().into(),
                schema.clone(),
            );
            entry = entry.import_observable_named_authority(&unrelated).unwrap();
        }
        let entry = entry
            .import_observable_named_authority(&description)
            .unwrap();
        let count = entry.observe_symbolic(&description).unwrap().entry_count;
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            assert!(
                entry
                    .enter_call()
                    .checked_imported_instance_consumption(&left)
                    .is_err(),
                "an actor without authority cannot record a death"
            );
            let one = entry.checked_imported_instance_consumption(&left).unwrap();
            assert_eq!(
                one,
                entry.checked_imported_instance_consumption(&left).unwrap(),
                "rechecking one checked rewrite has a stable successor identity"
            );
            assert_eq!(
                one.observe_symbolic(&description).unwrap().symbolic_delta,
                Some((false, Bitvector32Term::Constant(1)))
            );
            assert_eq!(
                one.checked_imported_instance_consumption(&left)
                    .unwrap_err(),
                CreationRefusal::MissingMembers
            );
            let two = one.checked_imported_instance_consumption(&right).unwrap();
            let observed = two.observe_symbolic(&description).unwrap();
            assert_eq!(observed.entry_count, count);
            assert_eq!(observed.entry_owned_members, 2);
            assert_eq!(
                two.0
                    .opaque_imports
                    .get(&description)
                    .unwrap()
                    .owned_members,
                0,
                "a numeric lower bound does not grant member custody"
            );
            assert_eq!(
                observed.symbolic_delta,
                Some((false, Bitvector32Term::Constant(2)))
            );
            assert!(
                !two.owns_population_member(&description),
                "named deaths grant no anonymous custody"
            );
            assert_eq!(
                entry.0.opaque_holders.get(&entry.0.opaque_actor),
                two.0.opaque_holders.get(&two.0.opaque_actor)
            );
        });
        work
    });
    assert!(work[0] > 0);
    for (index, sample) in work.iter().enumerate() {
        assert!(*sample <= work[0] + 96 * index, "{work:?}");
    }
}

#[test]
fn imported_named_lifecycle_keeps_entry_bounds_and_scales_with_unrelated_imports() {
    for wildcard in [false, true] {
        let anchor = CValue::pointer(Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        });
        let schema =
            ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let mut scope = ResourceDescription::new(
            "ticket".into(),
            vec![anchor.clone().into()].into(),
            schema.clone(),
        );
        if wildcard {
            scope = scope.with_population_arity(2).unwrap();
        }
        let member = |identity, tag| {
            let mut arguments = vec![anchor.clone().into()];
            if wildcard {
                arguments.push(int32(tag).into());
            }
            ResourceInstance::new(
                Variable(identity),
                "ticket".into(),
                arguments.into(),
                schema.clone(),
                vec![int32(7).into()].into(),
            )
            .unwrap()
        };
        let born = member(997_001, 7);
        let first = member(997_002, 7);
        let second = member(997_003, 7);
        let exact = ResourceDescription::from_instance(&first);
        let work = [16, 64, 256].map(|size| {
            let mut entry = CreationEvents::new();
            for index in 0..size {
                let unrelated = ResourceDescription::new(
                    format!("other-{index}"),
                    scope.arguments().to_vec().into(),
                    schema.clone(),
                );
                entry = entry.import_observable_named_authority(&unrelated).unwrap();
            }
            let entry = entry.import_observable_named_authority(&scope).unwrap();
            let count = entry.observe_symbolic(&scope).unwrap().entry_count;
            let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
                ConditionTerm::signed_add_overflows(count.clone(), Bitvector32Term::Constant(1)),
                false,
            ));
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                assert!(
                    entry
                        .checked_imported_instance_exchange(&born, true, &PureFactContext::new())
                        .is_err()
                );
                assert!(
                    entry
                        .enter_call()
                        .checked_imported_instance_exchange(&born, true, &assumptions)
                        .is_err()
                );
                let one = entry
                    .checked_imported_instance_exchange(&born, true, &assumptions)
                    .unwrap();
                assert_eq!(
                    one,
                    entry
                        .checked_imported_instance_exchange(&born, true, &assumptions)
                        .unwrap()
                );
                assert!(
                    one.checked_imported_instance_exchange(&born, true, &assumptions)
                        .is_err()
                );
                assert!(!one.owns_population_member(&scope));
                let zero = one.checked_imported_instance_consumption(&born).unwrap();
                assert_eq!(
                    zero.observe_symbolic(&scope).unwrap().combined_delta(),
                    None
                );
                assert_eq!(
                    zero.observe_symbolic(&scope).unwrap().entry_owned_members,
                    0,
                    "a born occurrence is not an entry occurrence"
                );
                assert!(zero.checked_imported_instance_consumption(&born).is_err());
                assert!(
                    zero.checked_imported_instance_exchange(&born, true, &assumptions)
                        .is_err()
                );
                let spent = zero
                    .checked_imported_instance_consumption(&first)
                    .unwrap()
                    .checked_imported_instance_consumption(&second)
                    .unwrap();
                let observed = spent.observe_symbolic(&scope).unwrap();
                assert_eq!(observed.entry_count, count);
                assert_eq!(observed.entry_owned_members, 2);
                assert_eq!(
                    observed.combined_delta(),
                    Some((false, Bitvector32Term::Constant(2)))
                );
                if wildcard {
                    let exact_count = spent
                        .observe_exact_member(&exact, &PureFactContext::new())
                        .unwrap();
                    assert_eq!(exact_count.delta, -2);
                    assert_eq!(exact_count.entry_owned_members, 2);
                    assert_eq!(
                        spent
                            .observe_exact_member(
                                &ResourceDescription::from_instance(&member(997_004, 8)),
                                &PureFactContext::new()
                            )
                            .unwrap()
                            .delta,
                        0
                    );
                }
                assert_eq!(
                    entry.0.opaque_holders.get(&entry.0.opaque_actor),
                    spent.0.opaque_holders.get(&spent.0.opaque_actor)
                );
            });
            work
        });
        assert!(work[0] > 0);
        for (index, sample) in work.iter().enumerate() {
            assert!(*sample <= work[0] + 160 * index, "{work:?}");
        }
    }
}

#[test]
fn imported_named_exact_counts_refuse_unresolved_neighbor_effects() {
    let anchor = CValue::pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    });
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let scope = ResourceDescription::new(
        "ticket".into(),
        vec![anchor.clone().into()].into(),
        schema.clone(),
    )
    .with_population_arity(2)
    .unwrap();
    let member = |identity, tag| {
        ResourceInstance::new(
            Variable(identity),
            "ticket".into(),
            vec![
                anchor.clone().into(),
                CValue::Int32(Bitvector32Term::Variable(Variable(tag))).into(),
            ]
            .into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap()
    };
    let first = member(998_001, 998_101);
    let second = member(998_002, 998_102);
    let entry = CreationEvents::new()
        .import_observable_named_authority(&scope)
        .unwrap();
    let one = entry.checked_imported_instance_consumption(&first).unwrap();
    assert_eq!(
        one.observe_exact_member(
            &ResourceDescription::from_instance(&first),
            &PureFactContext::new()
        )
        .unwrap()
        .delta,
        -1
    );
    assert!(
        one.observe_exact_member(
            &ResourceDescription::from_instance(&second),
            &PureFactContext::new()
        )
        .is_err()
    );
    let two = one.checked_imported_instance_consumption(&second).unwrap();
    assert_eq!(
        two.observe_symbolic(&scope).unwrap().combined_delta(),
        Some((false, Bitvector32Term::Constant(2)))
    );
    assert!(
        two.observe_exact_member(
            &ResourceDescription::from_instance(&first),
            &PureFactContext::new()
        )
        .is_err(),
        "the unresolved indices may alias"
    );
}

#[test]
fn imported_named_death_receipts_are_indexed_beside_growing_related_members() {
    let anchor = CValue::pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    });
    let schema =
        ResourceFieldSchema::new(vec![("serial".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let description = ResourceDescription::new(
        "ticket".into(),
        vec![anchor.clone().into()].into(),
        schema.clone(),
    );
    let member = |identity| {
        ResourceInstance::new(
            Variable(identity),
            "ticket".into(),
            vec![anchor.clone().into()].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap()
    };
    let work = [16, 64, 256].map(|size| {
        let mut state = CreationEvents::new()
            .import_observable_named_authority(&description)
            .unwrap();
        for index in 0..size {
            state = state
                .checked_imported_instance_consumption(&member(999_001 + index))
                .unwrap();
        }
        let (next, work) = crate::persistent::measure_persistent_work(|| {
            state
                .checked_imported_instance_consumption(&member(999_999))
                .unwrap()
        });
        assert_eq!(
            next.observe_symbolic(&description)
                .unwrap()
                .entry_owned_members,
            size as u32 + 1
        );
        assert!(
            next.consumed_imported_instance(&description, Variable(999_001))
                .is_some()
        );
        work
    });
    assert!(work[0] > 0);
    for (index, sample) in work.iter().enumerate() {
        assert!(*sample <= work[0] + 64 * index, "{work:?}");
    }
}

#[test]
fn diverged_paths_that_create_the_same_storage_record_the_same_state() {
    // Reduced from the moved-child `match ... ensuring` of
    // `examples/rbtree-erase/rbtree_erase_spine.click`: each arm declares the
    // same call-result local after the arms' ledgers have diverged, so each
    // mints its own anchor for it. The branch join must see one state.
    let start = CreationEvents::new();
    let scratch = PointerBlock::Heap(940_120);
    let shared = PointerBlock::Heap(940_121);
    let retired_scratch = start
        .created(scratch.clone())
        .retired(&scratch)
        .expect("an unused lifetime ends");
    assert_ne!(retired_scratch, start);
    let left = retired_scratch.created(shared.clone());
    let right = start.created(shared.clone());
    assert_ne!(left, right);
    assert!(!left.records_same_state_as(&right));
    assert!(left.records_same_state_up_to_fresh_anchors(&right));
    assert!(right.records_same_state_up_to_fresh_anchors(&left));

    // An anchor with an established population is named by its registration
    // and population, so the two are no longer the same state.
    let left_established = left
        .establish(&shared, "reference")
        .expect("the creating path establishes an empty population");
    let right_established = right
        .establish(&shared, "reference")
        .expect("the creating path establishes an empty population");
    assert!(!left_established.records_same_state_up_to_fresh_anchors(&right_established));

    // Different storage is a different state, whatever its anchors.
    let other = start.created(PointerBlock::Heap(940_122));
    assert!(!left.records_same_state_up_to_fresh_anchors(&other));
    assert!(
        !left.records_same_state_up_to_fresh_anchors(&right.created(PointerBlock::Heap(940_123)))
    );
}
