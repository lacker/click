// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::LoanRefusalCategory;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType};
use std::sync::Arc;

/// A completed frontier fork must share all sibling data, independently of
/// the number of paths or facts stored on each path.
#[test]
fn completed_candidate_forks_share_source_state_and_all_path_storage() {
    for (path_count, fact_count) in [(4, 4), (64, 4), (1024, 4), (4, 64), (4, 1024)] {
        let function = program_function(
            ProgramType::Int32,
            "candidate_storage",
            vec![program_parameter("x", ProgramType::Int32)],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let paths = (0..path_count)
            .map(|_| {
                let facts = (0..fact_count)
                    .map(|index| {
                        ExecutionPureFact::new(Proposition::ConditionIs(
                            ConditionTerm::signed_less_than(
                                MachineTerm::Variable(Variable(950_000 + index)),
                                MachineTerm::constant(0),
                            ),
                            true,
                        ))
                    })
                    .collect();
                (
                    FunctionOutcome::Return {
                        value: int32(0).into(),
                        state: Box::new(ExecutionState::new()),
                    },
                    facts,
                    Vec::new(),
                )
            })
            .collect();
        let original = program_function_execution_candidates_from_outcomes(
            ExecutionState::new(),
            function,
            vec![crate::kernel::program_expression::int32_literal(0)],
            paths,
        );
        let fork = original.clone();
        assert!(std::ptr::eq(original.state(), fork.state()));
        assert!(std::ptr::eq(original.function(), fork.function()));
        assert!(std::ptr::eq(original.arguments(), fork.arguments()));
        assert!(std::ptr::eq(original.paths(), fork.paths()));
        for (original_path, fork_path) in original.paths().iter().zip(fork.paths()) {
            assert_eq!(original_path.facts().len(), fact_count as usize);
            assert!(std::ptr::eq(original_path.facts(), fork_path.facts()));
        }
        assert_eq!(original, fork);
        drop(original);
        assert_eq!(fork.paths().len(), path_count);
        assert_eq!(fork.paths()[0].facts().len(), fact_count as usize);
        let different = program_function_execution_candidates_from_outcomes(
            ExecutionState::new(),
            fork.function().clone(),
            vec![crate::kernel::program_expression::int32_literal(0)],
            Vec::new(),
        );
        assert_ne!(
            fork, different,
            "sharing must preserve complete candidate equality"
        );
    }
}

/// Distinct frontier publications keep the same candidate records, not merely
/// the same underlying facts. Vary record count and payload size separately.
#[test]
fn terminal_candidate_publications_retain_records_and_payloads() {
    for (path_count, payload_size) in [(8, 8), (32, 8), (128, 8), (8, 128), (8, 1024)] {
        let function = program_function(
            ProgramType::Int32,
            "retained_candidates",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let proposition = Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(970_000)),
                MachineTerm::constant(0),
            ),
            true,
        );
        let obligations = vec![ProofObligation::new(proposition.clone()); payload_size];
        let original = program_function_execution_candidates_from_outcomes(
            ExecutionState::new(),
            function,
            vec![],
            (0..path_count)
                .map(|index| {
                    (
                        FunctionOutcome::Return {
                            value: int32(index as u32).into(),
                            state: Box::new(ExecutionState::new()),
                        },
                        vec![ExecutionPureFact::new(proposition.clone()); payload_size],
                        obligations.clone(),
                    )
                })
                .collect(),
        );
        let mut publications = Vec::new();
        for prefix in 1..=path_count {
            let retained = original.paths()[..prefix]
                .iter()
                .map(|path| {
                    program_function_execution_candidate_with_additional_facts(
                        path,
                        &ExecutionFacts::new(),
                    )
                })
                .collect();
            let publication = program_function_execution_candidates_from_retained_paths(
                ExecutionState::new(),
                original.function().clone(),
                vec![],
                retained,
            );
            for (source, target) in original.paths().iter().zip(publication.paths()) {
                assert!(Arc::ptr_eq(&source.data, &target.data));
                assert!(std::ptr::eq(source.outcome(), target.outcome()));
                assert!(std::ptr::eq(source.obligations(), target.obligations()));
            }
            publications.push(publication);
        }
        let records = publications
            .iter()
            .flat_map(|publication| publication.paths())
            .map(|path| Arc::as_ptr(&path.data) as usize)
            .collect::<BTreeSet<_>>();
        assert_eq!(records.len(), path_count);
        drop(original);
        assert_eq!(publications.last().unwrap().paths().len(), path_count);
        assert_eq!(
            publications.last().unwrap().paths()[0].obligations().len(),
            payload_size
        );
    }
}

#[test]
fn extending_a_candidate_retains_payload_and_classifies_only_new_facts() {
    let state = ExecutionState::new();
    let public = ExecutionPureFact::certified(Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(971_000)),
            MachineTerm::constant(0),
        ),
        true,
    ));
    let effect = ExecutionPureFact::internal(Proposition::MemoryMutatesOnly {
        before: state.memory().clone(),
        after: state.memory().clone(),
        writes: vec![],
    });
    let original = program_function_execution_candidates_from_outcomes_with_loan_evidence(
        state.clone(),
        program_function(
            ProgramType::Int32,
            "extended_candidate",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
        vec![],
        vec![(
            FunctionOutcome::Return {
                value: int32(0).into(),
                state: Box::new(state),
            },
            [public.clone(), effect.clone()].into(),
            vec![ProofObligation::new(public.proposition().clone())],
            crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        )],
    );
    let source = &original.paths()[0];
    let new_public = ExecutionPureFact::new(Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(971_001)),
            MachineTerm::constant(1),
        ),
        false,
    ));
    let private = ExecutionPureFact::internal(new_public.proposition().clone());
    let public_effect = ExecutionPureFact::certified(effect.proposition().clone());
    for additional in [
        [new_public.clone(), private.clone()].into(),
        [new_public.clone(), private, public_effect.clone()].into(),
    ] {
        let extended =
            program_function_execution_candidate_with_additional_facts(source, &additional);
        assert!(std::ptr::eq(source.outcome(), extended.outcome()));
        assert!(std::ptr::eq(source.obligations(), extended.obligations()));
        assert!(std::ptr::eq(&source.facts()[0], &extended.facts()[0]));
        assert_eq!(source.facts().len(), 1);
        assert_eq!(extended.facts()[1], new_public);
        assert!(extended.facts()[0].is_certified());
        let mut combined = source.execution_facts();
        combined.extend_shared(&additional);
        let rebuilt = program_function_execution_candidates_from_outcomes_with_loan_evidence(
            original.state().clone(),
            original.function().clone(),
            original.arguments().to_vec(),
            vec![(
                source.outcome().clone(),
                combined,
                source.obligations().to_vec(),
                source.loan_evidence().clone(),
            )],
        );
        assert_eq!(
            &extended,
            &rebuilt.paths()[0],
            "retention preserves the original classification and ordering"
        );
        let republished = program_function_execution_candidate_with_additional_facts(
            &extended,
            &ExecutionFacts::new(),
        );
        let rebuilt_again = program_function_execution_candidates_from_outcomes_with_loan_evidence(
            original.state().clone(),
            original.function().clone(),
            original.arguments().to_vec(),
            vec![(
                extended.outcome().clone(),
                extended.execution_facts(),
                extended.obligations().to_vec(),
                extended.loan_evidence().clone(),
            )],
        );
        assert_eq!(&republished, &rebuilt_again.paths()[0]);
        assert!(std::ptr::eq(extended.outcome(), republished.outcome()));
        let retained_private = extended
            .effect_facts()
            .iter()
            .find(|fact| !fact.is_public())
            .unwrap();
        assert!(std::ptr::eq(&source.effect_facts()[0], retained_private));
    }
    let extended =
        program_function_execution_candidate_with_additional_facts(source, &[public_effect].into());
    drop(original);
    assert_eq!(extended.obligations().len(), 1);
}

/// Each returned path reads its guards, but stores only its own suffix.
#[test]
#[ignore = "nightly: 3.4s in the parallel gate"]
fn early_return_paths_share_guard_fact_storage() {
    let mut samples = Vec::new();
    for returns in [8, 16, 32, 64] {
        let mut body = program_return(crate::kernel::program_expression::int32_literal(u32::MAX));
        for value in (0..returns).rev() {
            body = program_seq(
                program_if(
                    crate::kernel::program_expression::equal(
                        crate::kernel::program_expression::variable("x"),
                        crate::kernel::program_expression::int32_literal(value),
                    ),
                    program_return(crate::kernel::program_expression::int32_literal(value)),
                    program_skip(),
                ),
                body,
            );
        }
        let function = program_function(
            ProgramType::Int32,
            "shared_guards",
            vec![program_parameter("x", ProgramType::Int32)],
            body,
        );
        let execution = prove_symbolic_program_function_execution_paths(
            ExecutionState::new(),
            function,
            vec![ProgramExpression::Value(int32(MachineTerm::Variable(
                Variable(960_000),
            )))],
            PureFactContext::new(),
        );
        assert!(
            execution.limit().is_none(),
            "{returns} returns: {:?}",
            execution.limit()
        );
        assert_eq!(execution.paths().len(), returns as usize + 1);
        let unique = execution
            .paths()
            .iter()
            .flat_map(|path| path.facts().iter())
            .map(|fact| fact as *const ExecutionPureFact as usize)
            .collect::<std::collections::BTreeSet<_>>()
            .len();
        let occurrences: usize = execution
            .paths()
            .iter()
            .map(|path| path.facts().len())
            .sum();
        samples.push((returns, unique, occurrences));
        // The later path retains every earlier false guard, never an earlier
        // arm's true guard. Equality and order remain observable to callers.
        let last = execution.paths().last().unwrap();
        assert_eq!(last.facts().len(), returns as usize);
        assert!(
            last.facts()
                .iter()
                .all(|fact| matches!(fact.proposition(), Proposition::ConditionIs(_, false)))
        );
    }
    eprintln!("early-return stored facts: {samples:?}");
    for (returns, unique, occurrences) in &samples {
        assert!(
            *unique <= 3 * *returns as usize,
            "path facts must share their guard prefixes: {samples:?}"
        );
        assert!(
            occurrences > unique,
            "the fixture must actually exercise shared prefixes"
        );
    }
}

fn borrowed_input_view_function(name: &str) -> ProgramFunction {
    program_function(
        ProgramType::Void,
        name,
        vec![],
        program_return(program_void_value()),
    )
    .with_resource_summary(
        vec![ResourceSpec::token(
            ResourceAccessMode::View,
            "borrowed_input".into(),
            vec![],
            vec![],
        )],
        vec![],
    )
}

#[test]
fn borrowed_contract_input_roots_only_the_exact_principal_view() {
    let viewed = ResourceFact::view_token("borrowed_input".into(), vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let occurrence = resources.occurrences_for_fact(&viewed)[0];
    let state = ExecutionState::new().with_resource_context(resources);
    let rooted = execution_state_with_borrowed_contract_inputs(
        state,
        &borrowed_input_view_function("read_borrowed_input"),
        &[],
        &PureFactContext::new(),
    )
    .expect("a checked principal input view receives external shared authority");

    assert!(rooted.loan_ledger().is_some());
    assert!(rooted.loan_participant().is_some());
    assert_eq!(
        rooted
            .loan_view_bindings()
            .get(&occurrence)
            .map(|binding| &binding.viewed),
        Some(&viewed)
    );
    assert!(rooted.loan_bindings_are_consistent());
}

/// Every proof unit of one function shares one installed root: a second
/// install on the same entry state returns the same ledger identity, while a
/// changed entry state gets a fresh one.
#[test]
fn borrowed_contract_input_roots_are_shared_across_proof_units_of_one_function() {
    let viewed = ResourceFact::view_token("borrowed_input".into(), vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let state = ExecutionState::new().with_resource_context(resources);
    let function = borrowed_input_view_function("shared_root_reader");
    let first = execution_state_with_borrowed_contract_inputs(
        state.clone(),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect("first install");
    let second = execution_state_with_borrowed_contract_inputs(
        state.clone(),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect("second install on the same entry state");
    assert_eq!(first.loan_ledger(), second.loan_ledger());
    assert_eq!(first.loan_participant(), second.loan_participant());
    assert_eq!(first, second);

    let other_resources = ResourceContext::new().unchecked_with_facts([
        viewed.clone(),
        ResourceFact::own_token("extra".into(), vec![]),
    ]);
    let changed = execution_state_with_borrowed_contract_inputs(
        ExecutionState::new().with_resource_context(other_resources),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect("install on a changed entry state");
    assert_ne!(first.loan_ledger(), changed.loan_ledger());
}

/// An owned clause that provably overlaps a viewed clause of the same
/// contract is a partition no caller can supply; the root installer refuses
/// it instead of proving a vacuous body under it.
#[test]
fn borrowed_contract_input_refuses_an_owned_clause_inside_a_viewed_range() {
    let pointer = crate::kernel::Pointer {
        block: "buffer".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let viewed = ResourceFact::view_memory(MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(2),
    ));
    let owned = ResourceFact::own_memory(MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(1),
        MachineTerm::constant(2),
    ));
    let state = ExecutionState::new()
        .with_memory(Memory::new().with_block(pointer.block.clone(), 8))
        .with_resource_context(
            ResourceContext::new().unchecked_with_facts([viewed.clone(), owned.clone()]),
        );
    let function = program_function(
        ProgramType::Int32,
        "overlapping_reader",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![
            ResourceSpec::viewed_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(2),
            )),
            ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(1),
                crate::kernel::program_expression::int32_literal(2),
            )),
        ],
        vec![],
    );
    let refusal = execution_state_with_borrowed_contract_inputs(
        state,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(pointer))],
        &PureFactContext::new(),
    )
    .expect_err("an owned clause inside the viewed range is refused at entry");
    assert_eq!(refusal.category(), LoanRefusalCategory::ProvenOverlap);
}

#[test]
fn borrowed_contract_input_rejects_derived_or_ambiguous_views() {
    let viewed = ResourceFact::view_token("borrowed_input".into(), vec![]);
    let owner = ResourceFact::own_token("owner".into(), vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let owner_occurrence = resources.owned_occurrences_for_fact(&owner)[0];
    let derived = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
        owner_occurrence,
        &owner,
        [viewed.clone()],
        &Memory::new(),
    );
    let function = borrowed_input_view_function("reject_derived_input");
    let refusal = execution_state_with_borrowed_contract_inputs(
        ExecutionState::new().with_resource_context(derived),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect_err("a projection derived from owned authority is not an external root");
    assert_eq!(refusal.category(), LoanRefusalCategory::Missing);

    let duplicate = ResourceContext::new().unchecked_with_facts([viewed.clone(), viewed]);
    let refusal = execution_state_with_borrowed_contract_inputs(
        ExecutionState::new().with_resource_context(duplicate),
        &function,
        &[],
        &PureFactContext::new(),
    )
    .expect_err("equal principal occurrences are ambiguous authority anchors");
    assert_eq!(refusal.category(), LoanRefusalCategory::Missing);
}

/// The aggregate-copy path is the same shape at a wider width: the copy's
/// target is owned, its source is readable, and the lent range inside the
/// target refuses the whole-struct write at the ledger (R01 aggregate case;
/// docs/internals/stable-views.md).
#[test]
fn owner_authorized_aggregate_copy_into_a_lent_range_is_refused() {
    let target = Pointer {
        block: "target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let source = Pointer {
        block: "source".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owned_target = own_memory_fact(target.clone(), 0, 2);
    let owned_source = own_memory_fact(source.clone(), 0, 2);
    let viewed = view_memory_fact(target.clone(), 1, 2);
    let resources =
        ResourceContext::new().unchecked_with_facts([owned_target, owned_source, viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().expect("a fresh participant");
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .expect("a checked contract input root");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("the input root applies");
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    let state = ExecutionState::new()
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    let layout = AggregateLayout::new(
        8,
        4,
        vec![
            AggregateField::new("a", 0, ProgramType::Int32),
            AggregateField::new("b", 4, ProgramType::Int32),
        ],
    );
    let function = program_function(
        ProgramType::Void,
        "copy_struct_over_lent_field",
        vec![
            program_parameter("s", ProgramType::Int32Pointer),
            program_parameter("t", ProgramType::Int32Pointer),
        ],
        program_copy_aggregate(
            crate::kernel::program_expression::variable("s"),
            crate::kernel::program_expression::variable("t"),
            layout,
        ),
    );
    let arguments = vec![
        crate::kernel::program_expression::pointer_value(target.clone()),
        crate::kernel::program_expression::pointer_value(source),
    ];
    let theorem = prove_symbolic_program_function_execution_with_environment(
        state,
        function,
        arguments,
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("an owner-authorized aggregate copy over a lent field has a checked outcome");
    let Proposition::ProgramFunctionExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected a function execution proposition");
    };
    let FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(diagnostic)) = outcome else {
        panic!("expected a loan refusal, got {outcome:?}");
    };
    assert_eq!(diagnostic.category(), LoanRefusalCategory::ActiveDependency);
    assert_eq!(
        diagnostic.operation(),
        crate::kernel::LoanRefusalOperation::MemoryAccess
    );
    assert_eq!(
        diagnostic.subject().conflicting_resource_fact(),
        Some(&view_memory_fact(target, 1, 2))
    );
}

/// The loan barrier exists for exactly one shape: a write the ordinary
/// owned-authority check already accepted, landing inside a concretely lent
/// range. An unowned write never reaches it, because the missing-ownership
/// check now runs first.
#[test]
fn owner_authorized_write_into_a_lent_range_is_refused() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owned = own_memory_fact(pointer.clone(), 0, 2);
    let viewed = view_memory_fact(pointer.clone(), 0, 1);
    let resources = ResourceContext::new().unchecked_with_facts([owned, viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().expect("a fresh participant");
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .expect("a checked contract input root");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("the input root applies");
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    let state = ExecutionState::new()
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    let function = program_function(
        ProgramType::Void,
        "write_owned_lent_cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_store(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(9),
        ),
    );
    let pointer_for_assertions = pointer.clone();
    let arguments = vec![crate::kernel::program_expression::pointer_value(pointer)];
    let theorem = prove_symbolic_program_function_execution_with_environment(
        state,
        function,
        arguments,
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("an owner-authorized write into a lent range has a checked outcome");
    let Proposition::Implies(requirement, execution) = theorem.proposition() else {
        panic!("the write must remain conditional on loan separation");
    };
    let Proposition::ResourceSeparate { left, right } = requirement.as_ref() else {
        panic!("expected the explicit loan separation premise");
    };
    assert!(!PureFactContext::new().proves_resource_separate(left, right));
    assert_eq!(
        right.as_ref(),
        view_memory_fact(pointer_for_assertions, 0, 1).resource()
    );
    assert!(matches!(
        execution.as_ref(),
        Proposition::ProgramFunctionExecutes {
            outcome: FunctionOutcome::Return { .. },
            ..
        }
    ));
}

/// D2 law 2 is an access restriction, not an equality check: a store of the
/// value the lent cell already holds is refused exactly like a store of a
/// different one. The cell is pre-populated with the stored value, so the
/// only difference from
/// `owner_authorized_write_into_a_lent_range_is_refused` is that the write
/// would change nothing (R01's same-value negative; docs/internals/stable-views.md).
#[test]
fn owner_authorized_same_value_store_into_a_lent_range_is_refused() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owned = own_memory_fact(pointer.clone(), 0, 2);
    let viewed = view_memory_fact(pointer.clone(), 0, 1);
    let resources = ResourceContext::new().unchecked_with_facts([owned, viewed.clone()]);
    let support = resources.occurrences_for_fact(&viewed)[0];
    let ledger = crate::kernel::loans::LoanLedger::new();
    let participant = ledger.fresh_participant().expect("a fresh participant");
    let opening = ledger
        .borrowed_contract_input(participant, support, viewed.clone(), None)
        .expect("a checked contract input root");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("the input root applies");
    let bindings = crate::kernel::loans::LoanViewBindings::default().with_inserted(
        support,
        crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        },
    );
    // The cell already holds 9; the body stores 9 into it.
    let populated = Memory::new()
        .with_block(pointer.block.clone(), 8)
        .store(pointer.clone(), int32(9));
    let state = ExecutionState::new()
        .with_memory(populated.clone())
        .with_resource_context(resources)
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(participant))
        .with_loan_view_bindings(bindings);
    let function = program_function(
        ProgramType::Void,
        "store_the_same_value_into_a_lent_cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_store(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(9),
        ),
    );
    let pointer_for_assertions = pointer.clone();
    let arguments = vec![crate::kernel::program_expression::pointer_value(pointer)];
    let theorem = prove_symbolic_program_function_execution_with_environment(
        state,
        function,
        arguments,
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("a same-value store into a lent range has a checked outcome");
    let Proposition::Implies(requirement, execution) = theorem.proposition() else {
        panic!("the write must remain conditional on loan separation");
    };
    let Proposition::ResourceSeparate { left, right } = requirement.as_ref() else {
        panic!("expected the explicit loan separation premise");
    };
    assert!(!PureFactContext::new().proves_resource_separate(left, right));
    assert_eq!(
        right.as_ref(),
        view_memory_fact(pointer_for_assertions, 0, 1).resource()
    );
    assert!(matches!(
        execution.as_ref(),
        Proposition::ProgramFunctionExecutes {
            outcome: FunctionOutcome::Return { .. },
            ..
        }
    ));
}

#[test]
fn certified_program_entry_claims_do_not_authorize_ordinary_calls() {
    let function = program_function(
        ProgramType::Int32,
        "main",
        vec![],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_program_entry()
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        function.clone(),
        vec![],
        vec![],
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let claims = program_verified_function_contract_claims(&function, &execution).unwrap();
    assert!(!claims.is_empty());
    assert!(program_verified_function_rule(function, &claims).is_none());
}

#[test]
fn local_declaration_allocates_stack_object_for_address_of() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new();
    let statement = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(5)),
            program_return(crate::kernel::program_expression::load(
                crate::kernel::program_expression::addr_of("x"),
            )),
        ),
    );
    let final_state = ExecutionState::new().with_local("x", int32(5)).with_memory(
        Memory::new()
            .with_declared_scalar_block("local:x".into(), 4, ProgramType::Int32)
            .store(local_pointer, int32(5)),
    );
    let final_state = final_state.with_resource_context(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(Memory::local_pointer("x"), 0.into(), 4.into(), 1),
        )),
    );
    let mut final_state = final_state;
    final_state.locals.set_uninitialized_with_all_qualifiers(
        "x",
        ProgramType::Int32,
        Memory::local_pointer("x"),
        false,
        false,
        false,
        false,
    );
    final_state
        .locals
        .set_typed("x", int32(5), ProgramType::Int32);
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("local declaration/address-of should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(state),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(5).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn addressable_parameter_gets_a_fresh_callee_stack_slot() {
    let function = program_function(
        ProgramType::Int32,
        "addressable_parameter",
        vec![program_parameter("n", ProgramType::Int32)],
        program_seq(
            program_declare("p", ProgramType::Int32Pointer),
            program_seq(
                program_assign("p", crate::kernel::program_expression::addr_of("n")),
                program_return(crate::kernel::program_expression::variable("n")),
            ),
        ),
    );
    let caller_state = program_function_entry_state(
        &ExecutionState::new(),
        &function,
        &[crate::kernel::program_expression::int32_literal(3)],
    )
    .expect("parameter entry state");
    let caller_slot = caller_state
        .locals()
        .slot("n")
        .expect("parameter slot")
        .clone();
    assert!(caller_slot.block.starts_with("local:frame:0:"));
    assert_eq!(
        caller_state.memory().cells.get(&caller_slot),
        Some(int32(3))
    );

    let nested_state = program_function_entry_state(
        &caller_state,
        &function,
        &[crate::kernel::program_expression::int32_literal(4)],
    )
    .expect("nested parameter entry state");
    let nested_slot = nested_state
        .locals()
        .slot("n")
        .expect("nested parameter slot")
        .clone();
    assert_ne!(caller_slot, nested_slot);
    assert_eq!(
        nested_state.memory().cells.get(&caller_slot),
        Some(int32(3))
    );
    assert_eq!(
        nested_state.memory().cells.get(&nested_slot),
        Some(int32(4))
    );
}

#[test]
fn symbolic_execution_stops_without_needed_overflow_fact() {
    let left = Variable(20);
    let right = Variable(21);
    let state = ExecutionState::new()
        .with_local("left", int32(MachineTerm::Variable(left)))
        .with_local("right", int32(MachineTerm::Variable(right)));
    let statement = program_return(crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("left"),
        crate::kernel::program_expression::variable("right"),
    ));

    assert!(prove_symbolic_program_execution(state, statement, PureFactContext::new()).is_none());
}

#[test]
fn symbolic_execution_reports_branch_facts() {
    let a = Variable(24);
    let b = Variable(25);
    let a_bits = MachineTerm::Variable(a);
    let b_bits = MachineTerm::Variable(b);
    let condition = program_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = program_max_state(int32(a_bits), int32(b_bits));
    let execution = prove_symbolic_program_execution_paths(
        state.clone(),
        program_max_body(),
        PureFactContext::new(),
    );

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition.clone(), true)),
            Box::new(Proposition::ProgramStatementExecutes {
                state: Box::new(state.clone()),
                statement: Box::new(program_max_body()),
                outcome: StatementOutcome::Return {
                    value: int32(MachineTerm::Variable(b)).into(),
                    state: Box::new(state.clone()),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition.clone(), false)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, false)),
            Box::new(Proposition::ProgramStatementExecutes {
                state: Box::new(state.clone()),
                statement: Box::new(program_max_body()),
                outcome: StatementOutcome::Return {
                    value: int32(MachineTerm::Variable(a)).into(),
                    state: Box::new(state),
                },
            }),
        )
    );
}

#[test]
fn symbolic_execution_reports_overflow_facts() {
    let left = Variable(26);
    let right = Variable(27);
    let left_bits = MachineTerm::Variable(left);
    let right_bits = MachineTerm::Variable(right);
    let state = ExecutionState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = program_return(crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("left"),
        crate::kernel::program_expression::variable("right"),
    ));
    let domain = Proposition::signed_arithmetic_domain(
        MachineIntegerType::Int32,
        MachineBinaryOp::Add,
        &left_bits,
        &right_bits,
    );
    let execution = prove_symbolic_program_execution_paths(
        state.clone(),
        statement.clone(),
        PureFactContext::new(),
    );

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::new(domain.clone())]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(domain.clone()),
            Box::new(Proposition::ProgramStatementExecutes {
                state: Box::new(state.clone()),
                statement: Box::new(statement.clone()),
                outcome: StatementOutcome::Return {
                    value: int32(binary_node!(
                        Int32,
                        Add,
                        Box::new(left_bits),
                        Box::new(right_bits)
                    ))
                    .into(),
                    state: Box::new(state.clone()),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::new(Proposition::Not(Box::new(
            domain.clone()
        )))]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::Not(Box::new(domain))),
            Box::new(Proposition::ProgramStatementExecutes {
                state: Box::new(state.clone()),
                statement: Box::new(statement),
                outcome: StatementOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow),
            }),
        )
    );
}

#[test]
fn symbolic_execution_uses_no_overflow_fact() {
    let left = Variable(22);
    let right = Variable(23);
    let left_bits = MachineTerm::Variable(left);
    let right_bits = MachineTerm::Variable(right);
    let state = ExecutionState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = program_return(crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("left"),
        crate::kernel::program_expression::variable("right"),
    ));
    let no_overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
    let assumptions = PureFactContext::new().assume_condition(no_overflow.clone(), false);
    let theorem = prove_symbolic_program_execution(state.clone(), statement.clone(), assumptions)
        .expect("no-overflow fact should let symbolic add execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(no_overflow, false)),
            Box::new(Proposition::ProgramStatementExecutes {
                state: Box::new(state.clone()),
                statement: Box::new(statement),
                outcome: StatementOutcome::Return {
                    value: int32(binary_node!(
                        Int32,
                        Add,
                        Box::new(left_bits),
                        Box::new(right_bits)
                    ))
                    .into(),
                    state: Box::new(state),
                },
            }),
        )
    );
}

#[test]
fn symbolic_add_uses_exact_intervals_to_rule_out_overflow() {
    let left = Variable(24);
    let right = Variable(25);
    let left_bits = MachineTerm::Variable(left);
    let right_bits = MachineTerm::Variable(right);
    let state = ExecutionState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = program_return(crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("left"),
        crate::kernel::program_expression::variable("right"),
    ));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(left_bits, MachineTerm::constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(right_bits.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(right_bits.clone(), MachineTerm::constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(right_bits, MachineTerm::constant(1)),
            false,
        );

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                binary_node!(
                    Int32,
                    Add,
                    Box::new(MachineTerm::Variable(left)),
                    Box::new(MachineTerm::Variable(right)),
                ),
                MachineTerm::constant(2),
            ),
            true,
        )
    ));

    prove_symbolic_program_execution(state, statement, assumptions)
        .expect("exact reconstructed intervals should rule out signed addition overflow");
}

#[test]
fn symbolic_increment_uses_int_max_bound_to_rule_out_overflow() {
    let x = Variable(65);
    let x_bits = MachineTerm::Variable(x);
    let state = ExecutionState::new().with_local("x", int32(x_bits.clone()));
    let statement = program_return(crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable("x"),
        crate::kernel::program_expression::int32_literal(1),
    ));
    let x_lt_int_max =
        ConditionTerm::signed_less_than(x_bits.clone(), MachineTerm::constant(i32::MAX as u32));
    let assumptions = PureFactContext::new().assume_condition(x_lt_int_max.clone(), true);
    let theorem = prove_symbolic_program_execution(state.clone(), statement.clone(), assumptions)
        .expect("x < INT_MAX should prove x + 1 does not overflow");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(x_lt_int_max, true)),
            Box::new(Proposition::ProgramStatementExecutes {
                state: Box::new(state.clone()),
                statement: Box::new(statement),
                outcome: StatementOutcome::Return {
                    value: int32(binary_node!(
                        Int32,
                        Add,
                        Box::new(x_bits),
                        Box::new(MachineTerm::constant(1)),
                    ))
                    .into(),
                    state: Box::new(state),
                },
            }),
        )
    );
}

#[test]
fn symbolic_increment_uses_any_strict_upper_bound_to_rule_out_overflow() {
    let x_bits = MachineTerm::Variable(Variable(651));
    let upper_bits = MachineTerm::Variable(Variable(652));
    let assumption = ConditionTerm::signed_less_than(x_bits.clone(), upper_bits);
    let assumptions = PureFactContext::new().assume_condition(assumption, true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            x_bits,
            MachineTerm::constant(1),
        )),
        Some(false)
    );
}

#[test]
fn signed_addition_uses_both_operand_intervals_to_rule_out_overflow() {
    let left = MachineTerm::Variable(Variable(653));
    let right = MachineTerm::Variable(Variable(654));
    let million = MachineTerm::constant(1_000_000);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), left.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(left.clone(), million.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), right.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(right.clone(), million),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(left, right)),
        Some(false)
    );
}

#[test]
fn signed_addition_uses_negative_operand_intervals_to_rule_out_overflow() {
    let left = MachineTerm::Variable(Variable(655));
    let right = MachineTerm::Variable(Variable(656));
    let negative_million = MachineTerm::constant((-1_000_000i32) as u32);
    let zero = MachineTerm::constant(0);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(negative_million.clone(), left.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(left.clone(), zero.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(negative_million, right.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(right.clone(), zero), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(left, right)),
        Some(false)
    );
}

#[test]
fn signed_addition_ranges_nested_additions_only_when_each_level_is_safe() {
    let left = MachineTerm::Variable(Variable(657));
    let middle = MachineTerm::Variable(Variable(658));
    let right = MachineTerm::Variable(Variable(659));
    let upper = MachineTerm::constant(700_000_000);
    let mut assumptions = PureFactContext::new();
    for term in [&left, &middle, &right] {
        assumptions = assumptions
            .assume_condition(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), term.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(term.clone(), upper.clone()),
                true,
            );
    }
    let partial = MachineTerm::add(left, middle);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(partial.clone(), right)),
        Some(false)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            partial,
            MachineTerm::constant(800_000_000),
        )),
        None
    );
}

#[test]
fn signed_addition_matches_interval_facts_across_unchanged_states() {
    let cell = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(660)), 4),
    };
    let before = Memory::new();
    let after = before.clone().with_block("local:temporary", 4);
    let before_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before),
        Box::new(cell.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let after_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(after),
        Box::new(cell),
        crate::kernel::LoadKind::Int32,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), before_load.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(before_load, MachineTerm::constant(1_000_000)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            after_load.clone(),
            after_load,
        )),
        Some(false)
    );
}

#[test]
fn pointer_store_through_local_address_updates_named_lvalue() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let statement = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_store(
                crate::kernel::program_expression::addr_of("x"),
                crate::kernel::program_expression::int32_literal(5),
            ),
            program_return(crate::kernel::program_expression::variable("x")),
        ),
    );
    let final_state = ExecutionState::new().with_local("x", int32(5)).with_memory(
        Memory::new()
            .with_declared_scalar_block("local:x".into(), 4, ProgramType::Int32)
            .store(local_pointer, int32(5)),
    );
    let final_state = final_state.with_resource_context(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(Memory::local_pointer("x"), 0.into(), 4.into(), 1),
        )),
    );
    let mut final_state = final_state;
    final_state.locals.set_uninitialized_with_all_qualifiers(
        "x",
        ProgramType::Int32,
        Memory::local_pointer("x"),
        false,
        false,
        false,
        false,
    );
    final_state
        .locals
        .set_typed("x", int32(5), ProgramType::Int32);
    let theorem = prove_symbolic_program_execution(
        ExecutionState::new(),
        statement.clone(),
        PureFactContext::new(),
    )
    .expect("pointer store through local address should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementExecutes {
            state: Box::new(ExecutionState::new()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(5).into(),
                state: Box::new(final_state),
            },
        }
    );
}

#[test]
fn memory_load_store_are_native_theorems() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = int32(7);
    let theorem = prove_memory_load_after_store_same(Memory::new(), pointer.clone(), value.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::MemoryLoads {
            memory: Memory::new().store(pointer.clone(), value.clone()),
            pointer,
            outcome: ExpressionOutcome::Value(value),
        }
    );
}

#[test]
fn store_preserves_distinct_memory_cell_frame() {
    let stored_pointer = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let loaded_pointer = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().store(loaded_pointer.clone(), int32(42));
    let theorem = prove_memory_load_after_store_other(
        memory.clone(),
        stored_pointer.clone(),
        int32(9),
        loaded_pointer.clone(),
    )
    .expect("store to distinct pointer should preserve loaded cell");

    assert_eq!(
        theorem.proposition(),
        &Proposition::MemoryLoads {
            memory: memory.store(stored_pointer, int32(9)),
            pointer: loaded_pointer,
            outcome: ExpressionOutcome::Value(int32(42)),
        }
    );
}

#[test]
fn missing_memory_load_is_native_undefined_behavior() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let theorem = prove_memory_load(Memory::new(), pointer.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::MemoryLoads {
            memory: Memory::new(),
            pointer,
            outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
        }
    );
}

#[test]
fn contract_certification_checks_every_spec_lowering_path() {
    let base = Pointer {
        block: "local:contract-path-probe".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let queried = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Variable(Variable(900_001)),
    };
    let memory = Memory::new()
        .with_block(base.block.clone(), 8)
        .store(base, int32(0));
    let state = ExecutionState::new().with_memory(memory);
    let q = SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("q"));
    let function = program_function(
        ProgramType::Int32,
        "contract_path_probe",
        vec![program_parameter("q", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::MemoryLoadable {
            memory: SpecMemory::Current,
            base: q.clone(),
            start: SpecExpression::Value(int32(0)),
            end: SpecExpression::Value(int32(1)),
            element_width: 4,
        }],
        vec![SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(q),
                value_type: ProgramType::Int32,
            },
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        vec![],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        state,
        function.clone(),
        vec![crate::kernel::program_expression::pointer_value(queried)],
        vec![],
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let unverified = program_unverified_function_contract_claims(&function, &execution)
        .expect("the complete frontier should remain checkable");

    assert_eq!(unverified, vec![FunctionContractClaimKey::Ensure(0)]);
}

#[test]
fn function_execution_theorem_retains_non_assumable_verification_conditions() {
    let verification_condition = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let theorem = Theorem::new(wrap_proof_facts(
        conclusion,
        &PureFactContext::new(),
        &[],
        &[ProofObligation::verification_condition(
            verification_condition.clone(),
        )],
    ));

    assert!(matches!(
        theorem.proposition(),
        Proposition::Implies(condition, _)
            if condition.as_ref() == &verification_condition
    ));
}

#[test]
fn symbolic_path_can_only_certify_its_exact_function_specification() {
    let function = program_function(
        ProgramType::Int32,
        "exact_path",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let execution = prove_symbolic_program_function_execution_paths(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        PureFactContext::new(),
    );
    let false_specification = program_function_specification(
        ExecutionState::new(),
        Vec::new(),
        Vec::new(),
        FunctionOutcome::Return {
            value: int32(1).into(),
            state: Box::new(ExecutionState::new()),
        },
    );

    assert!(
        prove_program_function_satisfies_specification_from_symbolic_path(
            function,
            false_specification,
            &execution.paths()[0],
        )
        .is_none()
    );
}

#[test]
fn verified_function_rule_applies_contract_without_executing_body() {
    let helper = program_function(
        ProgramType::Int32,
        "opaque_helper",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(99)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "x",
            )),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let statement = program_seq(
        program_call_then_assign(
            0,
            "result",
            "opaque_helper",
            vec![crate::kernel::program_expression::int32_literal(5)],
        ),
        program_return(crate::kernel::program_expression::variable("result")),
    );
    let execution = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new()
            .with_population_creation_tracking()
            .with_local("result", int32(0)),
        statement.clone(),
        PureFactContext::new(),
        environment.clone(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution
        .paths()
        .first()
        .expect("opaque call should produce one path");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Return { value, .. },
        ..
    } = proposition
    else {
        panic!("opaque call should produce an abstract return branch")
    };
    assert!(*value.native() != int32(99));
    let propositions = path
        .facts()
        .iter()
        .map(|fact| fact.proposition().clone())
        .collect::<Vec<_>>();
    assert!(
        path.facts().iter().any(ExecutionPureFact::is_certified),
        "verified-call ensures should be marked as kernel-certified facts"
    );
    let assumptions = assumptions_with_propositions(&PureFactContext::new(), &propositions);
    let ProgramValue::Int32(result) = value.clone().into_native() else {
        panic!("opaque helper should return int32")
    };
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(result.clone()),
                right: Box::new(MachineTerm::constant(5))
            },
            true,
        )
    ));

    let body_execution = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new()
            .with_population_creation_tracking()
            .with_local("result", int32(0)),
        statement,
        PureFactContext::new(),
        environment,
        ExecutionSemantics::EXECUTE_BODIES,
    );
    let mut proposition = body_execution.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        Proposition::ProgramStatementExecutes {
            outcome: StatementOutcome::Return { value, .. },
            ..
        } if *value.native() == int32(99)
    ));
}

#[test]
fn verified_function_rule_coerces_null_constants_in_contract_views() {
    let p_is_null = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("p")),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
    };
    let returns_one = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_CONTRACT_RESULT_NAME,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            1,
        )),
    };
    let helper = program_function(
        ProgramType::Int32,
        "pointer_is_null",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::int32_literal(1)),
    )
    .with_contract(
        vec![p_is_null],
        vec![returns_one],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let execution = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new().with_population_creation_tracking(),
        program_call_then_assign(
            1,
            "result",
            "pointer_is_null",
            vec![crate::kernel::program_expression::int32_literal(0)],
        ),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque null call path");

    assert!(
        path.obligations().is_empty(),
        "typed null precondition should be discharged: {:#?}",
        path.obligations()
    );
    assert!(path.facts().iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::ConditionIs(
                ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::Equal, left: _, right },
                true
            ) if right.as_const() == Some(1)
        )
    }));
}

#[test]
fn verified_function_rule_does_not_publish_one_spec_alias_path() {
    let stored = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let queried = Pointer {
        block: stored.block.clone(),
        offset: PointerOffsetTerm::Variable(Variable(900_002)),
    };
    let q = SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("q"));
    let reflexive_load = SpecProposition::Comparison {
        left: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(q.clone()),
            value_type: ProgramType::Int32,
        },
        operator: ComparisonOperator::Equal,
        right: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(q),
            value_type: ProgramType::Int32,
        },
    };
    let helper = program_function(
        ProgramType::Int32,
        "opaque_alias_probe",
        vec![program_parameter("q", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![reflexive_load],
        Vec::new(),
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let execution = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new()
            .with_population_creation_tracking()
            .with_memory(Memory::new().with_block("heap", 8).store(stored, int32(0))),
        program_call_then_assign(
            2,
            "result",
            "opaque_alias_probe",
            vec![crate::kernel::program_expression::pointer_value(queried)],
        ),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque call path");

    assert!(
        path.obligations().is_empty(),
        "unexpected obligations: {:#?}",
        path.obligations()
    );
    assert!(!path.facts().iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), _)
        )
    }));
}

#[test]
fn opaque_pointer_result_can_alias_its_argument() {
    let argument = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let helper = program_function(
        ProgramType::Int32Pointer,
        "opaque_identity_pointer",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::variable("p")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "p",
            )),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let execution = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new()
            .with_population_creation_tracking()
            .with_local("result", ProgramValue::pointer(Pointer::null())),
        program_call_then_assign(
            3,
            "result",
            "opaque_identity_pointer",
            vec![crate::kernel::program_expression::pointer_value(
                argument.clone(),
            )],
        ),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque call path");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Normal(state),
        ..
    } = proposition
    else {
        panic!("opaque pointer call should return normally")
    };
    let local_native_output_1801 = state.locals().get_native("result");
    let Some(ProgramValue::Pointer(result)) = local_native_output_1801.as_deref() else {
        panic!("call result should be a pointer")
    };

    assert!(result.has_symbolic_block());
    assert!(!result.blocks_proven_distinct(&argument));
    let assumptions = assumptions_with_propositions(
        &PureFactContext::new(),
        &path
            .facts()
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>(),
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::pointer_equal(result.pointer().clone(), argument),
            true,
        )
    ));
}

#[test]
fn verified_immutable_calls_allocate_distinct_results() {
    let helper = program_function(
        ProgramType::Int32,
        "opaque_identity",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::variable("x")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "x",
            )),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let statement = program_seq(
        program_call_then_assign(
            4,
            "first",
            "opaque_identity",
            vec![crate::kernel::program_expression::int32_literal(5)],
        ),
        program_seq(
            program_call_then_assign(
                5,
                "second",
                "opaque_identity",
                vec![crate::kernel::program_expression::int32_literal(7)],
            ),
            program_return(crate::kernel::program_expression::variable("second")),
        ),
    );
    let execution = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new()
            .with_population_creation_tracking()
            .with_local("first", int32(0))
            .with_local("second", int32(0)),
        statement,
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("calls should execute");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Return { value, state },
        ..
    } = proposition
    else {
        panic!("calls should return normally")
    };

    let local_native_output_1879 = state.locals().get_native("first");
    let first = local_native_output_1879.as_deref().expect("first result");
    let local_native_output_1880 = state.locals().get_native("second");
    let second = local_native_output_1880.as_deref().expect("second result");
    assert_ne!(first, second);
    assert_eq!(value.native().as_ref(), second);
}

#[test]
fn separate_statement_verification_calls_preserve_fresh_identity_progress() {
    let helper = program_function(
        ProgramType::Int32,
        "opaque_identity",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::variable("x")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "x",
            )),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let mut budget = ExecutionBudget::default();

    let (first_execution, _) =
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            ExecutionState::new().with_population_creation_tracking().with_local("first", int32(0)).with_local("second", int32(0)),
            program_call_then_assign(6, "first", "opaque_identity", vec![crate::kernel::program_expression::int32_literal(5)]),
            PureFactContext::new(),
            environment.clone(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    let first_next = budget.next_kernel_variable();
    let first_path = first_execution.paths().first().expect("first call path");
    let mut first_proposition = first_path.theorem().proposition();
    while let Proposition::Implies(_, body) = first_proposition {
        first_proposition = body;
    }
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Normal(first_state),
        ..
    } = first_proposition
    else {
        panic!("first call should return normally")
    };
    let local_native_output_1937 = first_state.locals().get_native("first");
    let first_value = local_native_output_1937.as_deref().expect("first result");

    let (second_execution, _) =
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            *first_state.clone(),
            program_call_then_assign(7, "second", "opaque_identity", vec![crate::kernel::program_expression::int32_literal(7)]),
            PureFactContext::new(),
            environment,
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    let second_path = second_execution.paths().first().expect("second call path");
    let mut second_proposition = second_path.theorem().proposition();
    while let Proposition::Implies(_, body) = second_proposition {
        second_proposition = body;
    }
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Normal(second_state),
        ..
    } = second_proposition
    else {
        panic!("second call should return normally")
    };
    let local_native_output_1960 = second_state.locals().get_native("second");
    let second_value = local_native_output_1960.as_deref().expect("second result");

    assert!(first_next > 0);
    assert!(budget.next_kernel_variable() > first_next);
    assert_ne!(first_value, second_value);
}

#[test]
fn verified_function_rule_requires_every_contract_claim_certificate() {
    let function = program_function(
        ProgramType::Int32,
        "two_claims",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
        ],
        Vec::new(),
        vec![
            FunctionContractClaim::ensure_proposition(0, 0),
            FunctionContractClaim::ensure_proposition(1, 1),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    let impostor = program_function(
        ProgramType::Int32,
        "two_claims",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(1)),
    );
    let impostor_execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        impostor,
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::Ensure(0),
            &impostor_execution,
        )
        .is_none()
    );

    let first = program_verified_function_contract_claim(
        &function,
        FunctionContractClaimKey::Ensure(0),
        &execution,
    )
    .expect("first claim should certify");

    assert!(
        program_verified_function_rule(function.clone(), std::slice::from_ref(&first)).is_none()
    );

    let second = program_verified_function_contract_claim(
        &function,
        FunctionContractClaimKey::Ensure(1),
        &execution,
    )
    .expect("second claim should certify");
    assert!(program_verified_function_rule(function, &[first, second]).is_some());
}

#[test]
fn verified_function_rule_rejects_unclaimed_contract_obligations() {
    let function = program_function(
        ProgramType::Int32,
        "unclaimed_ensure",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(1)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(
        program_unverified_function_contract_claims(&function, &execution)
            .expect("the complete frontier should remain diagnostic"),
        vec![FunctionContractClaimKey::Ensure(0)]
    );
    let body_safety = program_verified_function_contract_claim(
        &function,
        FunctionContractClaimKey::BodySafety,
        &execution,
    )
    .expect("the body-safety claim itself should still certify");
    assert!(program_verified_function_rule(function, &[body_safety]).is_none());
}

#[test]
fn declared_exceptional_path_certifies_its_payload_postcondition() {
    let normal_false = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(0)),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    };
    let exceptional_payload = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_EXCEPTIONAL_RESULT_NAME,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(7)),
    };
    let function = program_function(
        ProgramType::Int32,
        "certified_throw",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![exceptional_payload])
    .with_contract(
        Vec::new(),
        vec![normal_false],
        Vec::new(),
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_proposition(0, 0),
            FunctionContractClaim::exceptional_ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    let throw_outcome = FunctionOutcome::Throw {
        value: int32(7).into(),
        state: Box::new(ExecutionState::new()),
    };
    let goals = program_function_exceptional_ensure_goals(
        &function,
        0,
        &ExecutionState::new(),
        &[],
        &throw_outcome,
        &PureFactContext::new(),
    )
    .expect("the exceptional payload should lower at the throw boundary");
    assert_eq!(goals.len(), 1);
    assert!(
        matches!(
            goals[0].proposition(),
            Proposition::ConditionIs(ConditionTerm::Constant(true), true)
        ),
        "unexpected exceptional goal: {:?}",
        goals[0].proposition()
    );

    assert_eq!(
        program_unverified_function_contract_claims(&function, &execution)
            .expect("a declared exceptional path is a safe certification path"),
        Vec::<FunctionContractClaimKey>::new(),
    );
    let proofs = program_verified_function_contract_claims(&function, &execution)
        .expect("the payload postcondition should certify");
    assert_eq!(proofs.len(), 3);
    assert!(program_verified_function_rule(function, &proofs).is_some());
}

#[test]
fn verified_exceptional_rule_produces_isolated_outcome_paths() {
    let normal_ensure = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_CONTRACT_RESULT_NAME,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(5)),
    };
    let exceptional_ensure = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_EXCEPTIONAL_RESULT_NAME,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(7)),
    };
    let function = program_function(
        ProgramType::Int32,
        "modular_maybe_throw",
        vec![program_parameter("flag", ProgramType::Int32)],
        program_if(
            crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable("flag"),
                crate::kernel::program_expression::int32_literal(0),
            ),
            program_return(crate::kernel::program_expression::int32_literal(5)),
            ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
        ),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![exceptional_ensure])
    .with_contract(
        Vec::new(),
        vec![normal_ensure],
        Vec::new(),
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_proposition(0, 0),
            FunctionContractClaim::exceptional_ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new().with_population_creation_tracking(),
        function.clone(),
        vec![ProgramExpression::Value(ProgramValue::Int32(
            MachineTerm::Variable(Variable(700_001)),
        ))],
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let proofs = program_verified_function_contract_claims(&function, &execution)
        .expect("both outcome families should certify");
    let rule = program_verified_function_rule(function.clone(), &proofs)
        .expect("a certified exceptional direct rule should form");
    let environment = ExecutionEnvironment::new()
        .with_function(function)
        .with_verified_function_rule(rule);
    let (call_statement, call_value) = program_call_value(
        8,
        "modular_maybe_throw",
        vec![crate::kernel::program_expression::int32_literal(0)],
    );
    let call_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_local("call_result", int32(0))
        .with_local("after", int32(0));
    let call_root = crate::kernel::proof::ProofFacts::from_ordered(&[]);
    let call_paths = prove_symbolic_program_execution_paths_with_environment(
        call_state.clone(),
        call_statement.clone(),
        PureFactContext::new(),
        environment.clone(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let mut normal = None;
    let mut exceptional = None;
    for path in call_paths.paths() {
        match crate::kernel::api::proof_evidence_conclusion(path.theorem()) {
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Normal(_),
                ..
            } => normal = Some(path),
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Throw { .. },
                ..
            } => exceptional = Some(path),
            other => panic!("unexpected call successor: {other:?}"),
        }
    }
    let normal = normal.expect("normal successor");
    let exceptional = exceptional.expect("exceptional successor");
    let path_facts = |facts: &ExecutionFacts| {
        facts
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>()
    };
    let outcome_of =
        |theorem: &Theorem| match crate::kernel::api::proof_evidence_conclusion(theorem) {
            Proposition::ProgramStatementVerifies { outcome, .. } => outcome.clone(),
            other => panic!("unexpected call successor: {other:?}"),
        };
    let call_split = crate::kernel::proof::CheckedCallOutcomeSplit::from_certified_transitions(
        call_state.clone(),
        call_statement.clone(),
        &call_root,
        normal.theorem(),
        &outcome_of(normal.theorem()),
        &path_facts(normal.facts()),
        normal.obligations(),
        exceptional.theorem(),
        &outcome_of(exceptional.theorem()),
        &path_facts(exceptional.facts()),
        exceptional.obligations(),
    )
    .expect("the direct call must have exactly two checked outcome successors");
    assert!(call_split.validates(
        &call_state,
        &call_statement,
        &call_root,
        normal.theorem(),
        exceptional.theorem(),
    ));
    assert!(!call_split.validates(
        &call_state,
        &call_statement,
        &call_root,
        normal.theorem(),
        normal.theorem(),
    ));
    assert!(!call_split.validates(
        &call_state,
        &program_return(crate::kernel::program_expression::variable("call_result")),
        &call_root,
        normal.theorem(),
        exceptional.theorem(),
    ));
    let statement = program_seq(
        program_seq(call_statement, program_assign("call_result", call_value)),
        program_seq(
            program_assign("after", crate::kernel::program_expression::int32_literal(1)),
            program_return(crate::kernel::program_expression::variable("call_result")),
        ),
    );
    let modular = prove_symbolic_program_execution_paths_with_environment(
        call_state,
        statement,
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );

    assert_eq!(modular.paths().len(), 2);
    let mut saw_return = false;
    let mut saw_throw = false;
    for path in modular.paths() {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        let assumptions = assumptions_with_propositions(
            &PureFactContext::new(),
            &path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>(),
        );
        match proposition {
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Return { value, state },
                ..
            } => {
                saw_return = true;
                assert_eq!(
                    state.locals().get_native("after").as_deref(),
                    Some(&int32(1))
                );
                let ProgramValue::Int32(value) = value.clone().into_native() else {
                    panic!("normal result should be int32")
                };
                assert!(crate::kernel::search::ProofSearch::proves(
                    &(assumptions),
                    &Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(value.clone()),
                            right: Box::new(MachineTerm::constant(5))
                        },
                        true,
                    )
                ));
                assert!(!crate::kernel::search::ProofSearch::proves(
                    &(assumptions),
                    &Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(value.clone()),
                            right: Box::new(MachineTerm::constant(7))
                        },
                        true,
                    )
                ));
            }
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Throw { value, state },
                ..
            } => {
                saw_throw = true;
                assert_eq!(
                    state.locals().get_native("after").as_deref(),
                    Some(&int32(0))
                );
                assert_eq!(
                    state.locals().get_native("call_result").as_deref(),
                    Some(&int32(0))
                );
                let ProgramValue::Int32(value) = value.clone().into_native() else {
                    panic!("exceptional payload should be int32")
                };
                assert!(crate::kernel::search::ProofSearch::proves(
                    &(assumptions),
                    &Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(value.clone()),
                            right: Box::new(MachineTerm::constant(7))
                        },
                        true,
                    )
                ));
                assert!(!crate::kernel::search::ProofSearch::proves(
                    &(assumptions),
                    &Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(value.clone()),
                            right: Box::new(MachineTerm::constant(5))
                        },
                        true,
                    )
                ));
            }
            other => panic!("unexpected modular outcome: {other:?}"),
        }
    }
    assert!(saw_return && saw_throw);
}

#[test]
fn verified_exceptional_call_enters_int32_handler_with_only_exceptional_claims() {
    let function = program_function(
        ProgramType::Int32,
        "throwing_helper",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_EXCEPTIONAL_RESULT_NAME,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(7)),
    }])
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(99)),
        }],
        Vec::new(),
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_proposition(0, 0),
            FunctionContractClaim::exceptional_ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new().with_population_creation_tracking(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let proofs = program_verified_function_contract_claims(&function, &execution)
        .expect("the helper's exceptional claim should certify");
    let rule = program_verified_function_rule(function.clone(), &proofs)
        .expect("the fully checked helper should form a direct rule");
    let statement = program_try_catch_int32(
        program_seq(
            program_call("throwing_helper", Vec::new()),
            program_return(crate::kernel::program_expression::int32_literal(99)),
        ),
        "caught",
        program_return(crate::kernel::program_expression::variable("caught")),
    );
    let paths = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new().with_population_creation_tracking(),
        statement,
        PureFactContext::new(),
        ExecutionEnvironment::new()
            .with_function(function)
            .with_verified_function_rule(rule),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(paths.paths().len(), 2);
    let mut saw_normal = false;
    let mut saw_caught = false;
    for path in paths.paths() {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        let Proposition::ProgramStatementVerifies {
            outcome: StatementOutcome::Return { value, state },
            ..
        } = proposition
        else {
            panic!("both modular outcomes should return: {proposition:?}");
        };
        if state.locals().get("caught").is_none() {
            saw_normal = true;
            assert_eq!(value.native().as_ref(), &int32(99));
            continue;
        }
        saw_caught = true;
        assert_eq!(state.locals().get("caught"), Some(value));
        let ProgramValue::Int32(value) = value.clone().into_native() else {
            panic!("caught payload should be int32");
        };
        let assumptions = assumptions_with_propositions(
            &PureFactContext::new(),
            &path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>(),
        );
        assert!(crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(value.clone()),
                    right: Box::new(MachineTerm::constant(7))
                },
                true,
            )
        ));
        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(value.clone()),
                    right: Box::new(MachineTerm::constant(99))
                },
                true,
            )
        ));
    }
    assert!(saw_normal && saw_caught);
}

#[test]
fn declared_exceptional_channel_does_not_vanish_without_an_exceptional_ensure() {
    let function = program_function(
        ProgramType::Int32,
        "unconstrained_exceptional_channel",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_int32_exceptional_outcome()
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let certification = certify_contract_with_kernel_artifacts(
        ExecutionState::new().with_population_creation_tracking(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let proofs = program_verified_function_contract_claims(&function, &certification)
        .expect("the declared channel needs no invented exceptional guarantee");
    let rule = program_verified_function_rule(function.clone(), &proofs)
        .expect("the body-certified direct rule should form");
    let modular = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new().with_population_creation_tracking(),
        program_call("unconstrained_exceptional_channel", Vec::new()),
        PureFactContext::new(),
        ExecutionEnvironment::new()
            .with_function(function)
            .with_verified_function_rule(rule),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );

    assert_eq!(modular.paths().len(), 2);
    assert!(modular.paths().iter().any(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(
            proposition,
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Throw { .. },
                ..
            }
        )
    }));
}

#[test]
fn exceptional_direct_rule_boundary_excludes_mutable_effects() {
    let function = program_function(
        ProgramType::Int32,
        "effectful_throw",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        )],
        vec![FunctionContractClaim::effect(0)],
        true,
    );

    assert!(!function.verified_direct_contract_supported());
    assert!(FunctionContract::new("EffectfulThrow", function).is_none());
}

#[test]
fn exceptional_postconditions_apply_only_to_throw_outcomes() {
    let exceptional_false = SpecProposition::Comparison {
        left: SpecExpression::Value(int32(0)),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    };
    let function = program_function(
        ProgramType::Int32,
        "ordinary_return_with_exceptional_family",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(4)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![exceptional_false])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::exceptional_ensure_proposition(0, 0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(
        program_unverified_function_contract_claims(&function, &execution)
            .expect("the complete return path should remain checkable"),
        Vec::<FunctionContractClaimKey>::new(),
    );
}

#[test]
fn false_or_missing_exceptional_postconditions_do_not_certify() {
    let wrong_payload = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_EXCEPTIONAL_RESULT_NAME,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(8)),
    };
    let with_false_claim = program_function(
        ProgramType::Int32,
        "wrong_exceptional_payload",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![wrong_payload.clone()])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::exceptional_ensure_proposition(0, 0)],
        true,
    );
    let false_execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        with_false_claim.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    assert_eq!(
        program_unverified_function_contract_claims(&with_false_claim, &false_execution)
            .expect("the false exceptional claim should be diagnosed"),
        vec![FunctionContractClaimKey::ExceptionalEnsure(0)],
    );

    let without_claim = program_function(
        ProgramType::Int32,
        "missing_exceptional_claim",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![wrong_payload])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let missing_execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        without_claim.clone(),
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    assert_eq!(
        program_unverified_function_contract_claims(&without_claim, &missing_execution)
            .expect("the omitted exceptional claim should be diagnosed"),
        vec![FunctionContractClaimKey::ExceptionalEnsure(0)],
    );
    let body_safety = program_verified_function_contract_claim(
        &without_claim,
        FunctionContractClaimKey::BodySafety,
        &missing_execution,
    )
    .expect("the safe body remains independently certified");
    assert!(program_verified_function_rule(without_claim, &[body_safety]).is_none());
}

#[test]
fn exceptional_direct_rule_boundary_excludes_resource_transitions() {
    let function = program_function(
        ProgramType::Int32,
        "resourceful_throw",
        Vec::new(),
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_resource_summary(
        vec![ResourceSpec::token(
            ResourceAccessMode::View,
            "borrowed".into(),
            vec![],
            vec![],
        )],
        Vec::new(),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    );

    assert!(!function.verified_direct_contract_supported());
    assert!(FunctionContract::new("ResourcefulThrow", function).is_none());
}

#[test]
fn exceptional_postconditions_observe_the_throw_state() {
    let pointer = Pointer {
        block: "exceptional-output".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p = SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("p"));
    let loadable = SpecProposition::MemoryLoadable {
        memory: SpecMemory::Current,
        base: p.clone(),
        start: SpecExpression::Value(int32(0)),
        end: SpecExpression::Value(int32(1)),
        element_width: 4,
    };
    let claims_ten = SpecProposition::Comparison {
        left: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(p),
            value_type: ProgramType::Int32,
        },
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(10)),
    };
    let function = program_function(
        ProgramType::Int32,
        "wrong_exceptional_state",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        ProgramStatement::Throw(crate::kernel::program_expression::int32_literal(7)),
    )
    .with_int32_exceptional_outcome()
    .with_exceptional_ensures(vec![claims_ten])
    .with_contract(
        vec![loadable],
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::exceptional_ensure_proposition(0, 0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new().with_memory(
            Memory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(9)),
        ),
        function.clone(),
        vec![crate::kernel::program_expression::pointer_value(pointer)],
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(
        program_unverified_function_contract_claims(&function, &execution)
            .expect("the exceptional exit state should be available to claims"),
        vec![FunctionContractClaimKey::ExceptionalEnsure(0)],
    );
}

#[test]
fn contract_certification_does_not_accept_injected_opaque_predicate_facts() {
    let predicate = SpecProposition::Predicate {
        resource_state_dependent: true,
        name: "positive".to_string(),
        arguments: vec![SpecPredicateArgument::Value(
            SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
        )],
    };
    let positive_body = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_CONTRACT_RESULT_NAME,
        )),
        operator: ComparisonOperator::GreaterEqual,
        right: SpecExpression::Value(int32(1)),
    };
    let function = program_function(
        ProgramType::Int32,
        "injected_predicate",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![positive_body.clone()],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    )
    .with_predicate_unfoldings(vec![PredicateUnfolding::new(predicate, positive_body)]);
    let injected = Proposition::ForAll {
        name: Default::default(),
        var: Variable(991_001),
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::Predicate {
            name: "positive".to_string(),
            arguments: vec![Term::Bitvector32(MachineTerm::Variable(Variable(991_001)))],
        }),
    };
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        vec![injected],
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none(),
        "caller-supplied quantified predicate facts must not certify a false ensure"
    );
}

#[test]
fn contract_effect_claim_rejects_an_undecidable_guard() {
    let base = Pointer {
        block: PointerBlock::Concrete("heap:guarded-effect".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let flag = Variable(991_002);
    let function = program_function(
        ProgramType::Int32,
        "undecidable_guarded_effect",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("flag", ProgramType::Int32),
        ],
        program_seq(
            program_store(
                crate::kernel::program_expression::index(
                    crate::kernel::program_expression::variable("p"),
                    crate::kernel::program_expression::int32_literal(0),
                ),
                crate::kernel::program_expression::int32_literal(1),
            ),
            program_return(crate::kernel::program_expression::int32_literal(1)),
        ),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![
            MemorySegment::new(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(1),
            )
            .with_guard(SpecProposition::Comparison {
                left: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable("flag"),
                ),
                operator: ComparisonOperator::NotEqual,
                right: SpecExpression::Value(int32(0)),
            }),
        ],
        vec![FunctionContractClaim::effect(0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new().with_memory(Memory::new().with_block(base.block.clone(), 4)),
        function.clone(),
        vec![
            crate::kernel::program_expression::pointer_value(base),
            ProgramExpression::Value(ProgramValue::Int32(MachineTerm::Variable(flag))),
        ],
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::Effect(0),
            &execution,
        )
        .is_none(),
        "a guarded frame must be case-split or proven true before certification"
    );
}

#[test]
fn contract_effect_claim_rejects_interior_entry_live_heap_pointer_as_fresh() {
    let allocation_base = Pointer {
        block: PointerBlock::Heap(991_003),
        offset: PointerOffsetTerm::Constant(0),
    };
    let interior = Pointer {
        block: allocation_base.block.clone(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let function = program_function(
        ProgramType::Int32,
        "interior_entry_live_effect",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_seq(
            program_store(
                crate::kernel::program_expression::pointer_offset_bytes(
                    crate::kernel::program_expression::variable("p"),
                    8,
                ),
                crate::kernel::program_expression::int32_literal(1),
            ),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
    )
    .with_resource_summary(
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::pointer_offset_bytes(
                crate::kernel::program_expression::variable("p"),
                8,
            ),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        Vec::new(),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        vec![MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        )],
        vec![FunctionContractClaim::effect(0)],
        true,
    );
    let caller_state = ExecutionState::new()
        .with_memory(
            Memory::new()
                .with_heap_allocation_claim(allocation_base.clone(), HeapExtent::int32(16))
                .expect("the entry allocation should be live"),
        )
        .with_resource_context(own_memory_context(interior, 0, 1));
    let execution = certify_contract_with_kernel_artifacts(
        caller_state,
        function.clone(),
        vec![crate::kernel::program_expression::pointer_value(
            allocation_base,
        )],
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    assert!(
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::Effect(0),
            &execution,
        )
        .is_none(),
        "an interior pointer into an entry-live block must not bypass the mutable frame"
    );
}

#[test]
fn contract_certification_reuses_a_matching_kernel_checked_execution() {
    let function = program_function(
        ProgramType::Int32,
        "checked_once",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::Value(int32(0)),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let state = ExecutionState::new();
    let environment = ExecutionEnvironment::new();
    let semantics = ExecutionSemantics::EXECUTE_BODIES;
    let mode = FunctionContractExecutionMode::VerifyLoops;
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let checked = prove_checked_program_function_execution_with_environment(
        state.clone(),
        function.clone(),
        Vec::new(),
        PureFactContext::new(),
        environment.clone(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );

    let execution = prove_program_function_contract_execution_paths_with_checked_artifacts(
        state,
        function.clone(),
        Vec::new(),
        environment,
        semantics,
        mode,
        &[checked],
    );

    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "matching checked authority should avoid a second function-body execution"
    );
    assert!(program_verified_function_contract_claims(&function, &execution).is_some());

    let extra_assumption = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(919_000)),
            MachineTerm::constant(0),
        ),
        true,
    );
    let unchecked_boundary = prove_checked_program_function_execution_with_environment(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        extra_assumption,
        ExecutionEnvironment::new(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );
    let fallback = prove_program_function_contract_execution_paths_with_checked_artifacts(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        ExecutionEnvironment::new(),
        semantics,
        mode,
        &[unchecked_boundary],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "an artifact with an unproved entry known must not be reused, and certification must not execute the body instead"
    );
    assert_eq!(fallback.path_count(), 0);
    assert!(
        fallback
            .reuse_diagnostic()
            .is_some_and(|detail| detail.contains("a condition fact")),
        "{:?}",
        fallback.reuse_diagnostic()
    );
    assert!(program_verified_function_contract_claims(&function, &fallback).is_none());
}

#[test]
fn checked_view_certificate_initializes_a_pristine_loan_authority() {
    let base = Pointer {
        block: PointerBlock::Concrete("checked:initial-view".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let function = program_function(
        ProgramType::Int32,
        "checked_initial_view",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::load(
            crate::kernel::program_expression::variable("p"),
        )),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        Vec::new(),
    )
    .with_contract(Vec::new(), Vec::new(), Vec::new(), Vec::new(), true);
    let state = ExecutionState::new()
        .with_memory(
            Memory::new()
                .with_block(base.block.clone(), 4)
                .store(base.clone(), int32(7)),
        )
        .with_resource_context(own_memory_context(base.clone(), 0, 1));
    let environment = ExecutionEnvironment::new();
    let arguments = vec![crate::kernel::program_expression::pointer_value(base)];
    let checked = prove_checked_program_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
        environment.clone(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    assert_eq!(checked.paths().len(), 1);
    let execution = prove_program_function_contract_execution_paths_with_checked_artifacts(
        state,
        function,
        arguments,
        environment,
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
        &[checked],
    );
    assert_eq!(execution.path_count(), 1);
}

#[test]
fn contract_certification_refuses_split_entry_artifacts() {
    let input = MachineTerm::Variable(Variable(919_100));
    let branch = ConditionTerm::signed_less_than(input.clone(), MachineTerm::constant(0));
    let function = program_function(
        ProgramType::Int32,
        "checked_partition",
        vec![program_parameter("x", ProgramType::Int32)],
        program_if(
            crate::kernel::program_expression::less_than(
                crate::kernel::program_expression::variable("x"),
                crate::kernel::program_expression::int32_literal(0),
            ),
            program_return(crate::kernel::program_expression::int32_literal(1)),
            program_return(crate::kernel::program_expression::int32_literal(2)),
        ),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::NotEqual,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let state = ExecutionState::new();
    let arguments = vec![ProgramExpression::Value(int32(input))];
    let environment = ExecutionEnvironment::new();
    let semantics = ExecutionSemantics::EXECUTE_BODIES;
    let mode = FunctionContractExecutionMode::VerifyLoops;
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let checked_true = prove_checked_program_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new().assume_condition(branch.clone(), true),
        environment.clone(),
        semantics,
        mode,
    );
    let checked_false = prove_checked_program_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new().assume_condition(branch, false),
        environment.clone(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        2
    );

    let execution = prove_program_function_contract_execution_paths_with_checked_artifacts(
        state.clone(),
        function.clone(),
        arguments.clone(),
        environment.clone(),
        semantics,
        mode,
        &[checked_true.clone(), checked_false],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "two opposite entry cases are not one complete contract frontier, and certification must not execute the body instead"
    );
    assert_eq!(execution.path_count(), 0);
    assert!(execution.reuse_diagnostic().is_some());
    assert!(program_verified_function_contract_claims(&function, &execution).is_none());

    let fallback = prove_program_function_contract_execution_paths_with_checked_artifacts(
        state,
        function.clone(),
        arguments,
        environment,
        semantics,
        mode,
        &[checked_true],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "one side of an entry partition is not a complete contract frontier, and certification must not execute the body instead"
    );
    assert_eq!(fallback.path_count(), 0);
    assert!(fallback.reuse_diagnostic().is_some());
    assert!(program_verified_function_contract_claims(&function, &fallback).is_none());
}

#[test]
fn contract_certification_reuses_definitionally_equal_entry_resources() {
    let unit = ResourceFact::own_token("entry_unit".to_string(), vec![int32(7)]);
    let proof_resources = ResourceContext::new()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit.clone());
    let contract_resources = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit], &PureFactContext::new())
        .expect("the contract representation should normalize the two units");
    assert_ne!(proof_resources, contract_resources);
    assert!(resource_contexts_definitionally_equal_with_definitions(
        &[],
        &Memory::new(),
        &proof_resources,
        &Memory::new(),
        &contract_resources,
        &PureFactContext::new(),
    ));

    let function = program_function(
        ProgramType::Int32,
        "checked_resource_entry",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let proof_state = ExecutionState::new().with_resource_context(proof_resources.clone());
    let contract_state = ExecutionState::new().with_resource_context(contract_resources.clone());
    let environment = ExecutionEnvironment::new();
    let semantics = ExecutionSemantics::EXECUTE_BODIES;
    let mode = FunctionContractExecutionMode::VerifyLoops;
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let checked = prove_checked_program_function_execution_with_environment(
        proof_state,
        function.clone(),
        Vec::new(),
        PureFactContext::new(),
        environment.clone(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );

    let execution = prove_program_function_contract_execution_paths_with_checked_artifacts(
        contract_state,
        function.clone(),
        Vec::new(),
        environment,
        semantics,
        mode,
        &[checked],
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "definitionally equal ghost entry resources should not rerun the C body"
    );
    assert!(program_verified_function_contract_claims(&function, &execution).is_some());

    let recursive_function = function.clone().with_composite_resource_definitions(vec![
        CompositeResourceDefinition::new(
            "recursive_entry",
            Vec::new(),
            None,
            true,
            Vec::new(),
            Vec::new(),
        ),
    ]);
    let recursive_checked = prove_checked_program_function_execution_with_environment(
        ExecutionState::new().with_resource_context(proof_resources),
        recursive_function.clone(),
        Vec::new(),
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        semantics,
        mode,
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        1
    );
    let recursive_execution =
        prove_program_function_contract_execution_paths_with_checked_artifacts(
            ExecutionState::new().with_resource_context(contract_resources),
            recursive_function.clone(),
            Vec::new(),
            ExecutionEnvironment::new(),
            semantics,
            mode,
            &[recursive_checked],
        );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "recursive resource representations are not rebased without a kernel-issued entry origin, and certification must not execute the body instead"
    );
    assert_eq!(recursive_execution.path_count(), 0);
    assert!(
        recursive_execution
            .reuse_diagnostic()
            .is_some_and(|detail| detail.contains("different entry state")),
        "{:?}",
        recursive_execution.reuse_diagnostic()
    );
    assert!(
        program_verified_function_contract_claims(&recursive_function, &recursive_execution)
            .is_none()
    );
}

#[test]
fn contract_claim_rejects_same_source_function_with_a_different_contract() {
    let body = program_return(crate::kernel::program_expression::int32_literal(0));
    let uncontracted = program_function(
        ProgramType::Int32,
        "contract_identity",
        Vec::new(),
        body.clone(),
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        uncontracted,
        Vec::new(),
        Vec::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let stronger = program_function(ProgramType::Int32, "contract_identity", Vec::new(), body)
        .with_contract(
            Vec::new(),
            vec![SpecProposition::Comparison {
                left: SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::variable(C_CONTRACT_RESULT_NAME),
                ),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(int32(1)),
            }],
            Vec::new(),
            vec![FunctionContractClaim::ensure_proposition(0, 0)],
            true,
        );

    assert!(
        program_verified_function_contract_claim(
            &stronger,
            FunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none()
    );
}

#[test]
fn body_safety_claim_rejects_an_unproved_execution_condition() {
    let function = program_function(
        ProgramType::Int32,
        "unsafe_body",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let state = ExecutionState::new();
    let obligation = ProofObligation::verification_condition(Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true,
    ));
    let proposition = Proposition::ProgramFunctionExecutes {
        state: Box::new(state.clone()),
        function: Box::new(function.clone()),
        arguments: Vec::new(),
        outcome: FunctionOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state),
        },
    };
    let path = SymbolicExecutionPath {
        call_parameters: None,
        completion_origin: None,
        call_result: None,
        assumptions: PureFactContext::new(),
        post_assumptions: None,
        facts: Vec::new().into(),
        effect_facts: Vec::new().into(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &PureFactContext::new(),
            &[],
            &[obligation],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let execution = FunctionContractExecution {
        pointer_result: None,
        cases: vec![vec![ContractPathSet {
            closed_exit_obligations: vec![],
            completion_path_origins: Vec::new(),
            paths: vec![path],
            checked_resource_claims: vec![Vec::new()],
            checked_resource_transitions: vec![false],
            deferred_contract_exits: vec![false],
            deferred_contract_exit_errors: vec![None],
            checked_returned_resources: vec![ResourceContext::new()],
            boundary_transfers: vec![None],
            completion_origin_state: None,
        }]],
        reuse_diagnostic: None,
        reuse_unauthorized_premise: None,
        reuse_entry_resources: Vec::new(),
        reuse_context_facts: Vec::new(),
        checked_call_events: Default::default(),
        loop_semantics: LoopSemantics::Verify,
        checked_callees: None,
        applied_tactics: Default::default(),
    };

    assert!(
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::BodySafety,
            &execution,
        )
        .is_none()
    );
}

/// A claim is judged over each path set of a case in turn: a set whose
/// paths fail it does not decide the claim while another set certifies it,
/// every case needs a certifying set, and a case with no set certifies
/// nothing.
#[test]
fn contract_claims_are_judged_over_each_path_set_of_a_case() {
    let function = program_function(
        ProgramType::Int32,
        "alternatives",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let state = ExecutionState::new();
    let proposition = Proposition::ProgramFunctionExecutes {
        state: Box::new(state.clone()),
        function: Box::new(function.clone()),
        arguments: Vec::new(),
        outcome: FunctionOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state),
        },
    };
    let unproved = ProofObligation::verification_condition(Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            MachineTerm::Variable(Variable(91_200)),
            MachineTerm::constant(8),
        ),
        true,
    ));
    let failing = SymbolicExecutionPath {
        call_parameters: None,
        completion_origin: None,
        call_result: None,
        assumptions: PureFactContext::new(),
        post_assumptions: Some(PureFactContext::new()),
        facts: Vec::new().into(),
        effect_facts: Vec::new().into(),
        obligations: vec![unproved.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition.clone(),
            &PureFactContext::new(),
            &[],
            &[unproved],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let clean = SymbolicExecutionPath {
        call_parameters: None,
        completion_origin: None,
        call_result: None,
        assumptions: PureFactContext::new(),
        post_assumptions: Some(PureFactContext::new()),
        facts: Vec::new().into(),
        effect_facts: Vec::new().into(),
        obligations: Vec::new(),
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &PureFactContext::new(),
            &[],
            &[],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let set = |path: &SymbolicExecutionPath| ContractPathSet {
        closed_exit_obligations: vec![],
        completion_path_origins: Vec::new(),
        paths: vec![path.clone()],
        checked_resource_claims: vec![Vec::new()],
        checked_resource_transitions: vec![false],
        deferred_contract_exits: vec![false],
        deferred_contract_exit_errors: vec![None],
        checked_returned_resources: vec![ResourceContext::new()],
        boundary_transfers: vec![None],
        completion_origin_state: None,
    };
    let certified = |cases: Vec<Vec<ContractPathSet>>| {
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::BodySafety,
            &FunctionContractExecution {
                pointer_result: None,
                cases,
                reuse_diagnostic: None,
                reuse_unauthorized_premise: None,
                reuse_entry_resources: Vec::new(),
                reuse_context_facts: Vec::new(),
                checked_call_events: Default::default(),
                loop_semantics: LoopSemantics::Verify,
                checked_callees: None,
                applied_tactics: Default::default(),
            },
        )
        .is_some()
    };
    assert!(
        certified(vec![vec![set(&failing), set(&clean)]]),
        "a later path set certifies the claim the first fails"
    );
    assert!(certified(vec![vec![set(&clean), set(&failing)]]));
    assert!(!certified(vec![vec![set(&failing)]]));
    assert!(
        !certified(vec![vec![set(&clean)], vec![set(&failing)]]),
        "every case needs a certifying path set"
    );
    assert!(
        !certified(vec![vec![set(&clean)], Vec::new()]),
        "a case with no path set certifies nothing"
    );
}

#[test]
fn body_safety_claim_uses_path_facts_for_verification_conditions() {
    let function = program_function(
        ProgramType::Int32,
        "guarded_body",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![FunctionContractClaim::body_safety()],
        true,
    );
    let state = ExecutionState::new();
    let guard = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            MachineTerm::Variable(Variable(91_000)),
            MachineTerm::constant(8),
        ),
        true,
    );
    let fact = ExecutionPureFact::new(guard.clone());
    let obligation = ProofObligation::verification_condition(guard);
    let proposition = Proposition::ProgramFunctionExecutes {
        state: Box::new(state.clone()),
        function: Box::new(function.clone()),
        arguments: Vec::new(),
        outcome: FunctionOutcome::Return {
            value: int32(0).into(),
            state: Box::new(state),
        },
    };
    let path = SymbolicExecutionPath {
        call_parameters: None,
        completion_origin: None,
        call_result: None,
        assumptions: PureFactContext::new(),
        post_assumptions: None,
        facts: vec![fact.clone()].into(),
        effect_facts: Vec::new().into(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &PureFactContext::new(),
            &[fact],
            &[obligation],
        )),

        loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
    };
    let execution = FunctionContractExecution {
        pointer_result: None,
        cases: vec![vec![ContractPathSet {
            closed_exit_obligations: vec![],
            completion_path_origins: Vec::new(),
            paths: vec![path],
            checked_resource_claims: vec![Vec::new()],
            checked_resource_transitions: vec![false],
            deferred_contract_exits: vec![false],
            deferred_contract_exit_errors: vec![None],
            checked_returned_resources: vec![ResourceContext::new()],
            boundary_transfers: vec![None],
            completion_origin_state: None,
        }]],
        reuse_diagnostic: None,
        reuse_unauthorized_premise: None,
        reuse_entry_resources: Vec::new(),
        reuse_context_facts: Vec::new(),
        checked_call_events: Default::default(),
        loop_semantics: LoopSemantics::Verify,
        checked_callees: None,
        applied_tactics: Default::default(),
    };

    assert!(
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::BodySafety,
            &execution,
        )
        .is_some(),
        "a path guard established by symbolic execution must discharge a guarded safety condition"
    );
}

#[test]
fn effect_endpoint_comparison_ignores_function_local_cells() {
    let local = Pointer {
        block: "local:temporary".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = Memory::new().with_block("local:temporary", 4);
    let after = before.clone().store(local, int32(7));

    assert!(
        crate::kernel::api::program_effect_memories_definitionally_equal(
            &before,
            &after,
            &PureFactContext::new(),
        )
    );

    let external = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let changed_external = after.store(external, int32(9));
    assert!(
        !crate::kernel::api::program_effect_memories_definitionally_equal(
            &before,
            &changed_external,
            &PureFactContext::new(),
        )
    );
}

#[test]
fn effect_endpoint_allows_resource_allocation_bookkeeping() {
    let allocation = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(64),
    };
    let before = Memory::new();
    let after = before
        .clone()
        .with_heap_allocation_claim(allocation, HeapExtent::int32(16))
        .expect("a fresh symbolic allocation claim should be registerable");

    assert!(
        crate::kernel::api::program_effect_memory_advances_over_internal_heap_state(
            &before,
            &after,
            &before,
            &PureFactContext::new(),
        )
    );
}

#[test]
fn bool_cast_range_is_rule_c1_of_the_cast() {
    let flag = ConditionTerm::Variable(Variable(1));
    let cast = MachineTerm::bool_cast(MachineIntegerType::Int32, flag.clone());
    let equals = |constant| {
        Proposition::ConditionIs(
            ConditionTerm::equal(cast.clone(), MachineTerm::constant(constant)),
            true,
        )
    };
    let facts = program_bool_cast_range_facts(&ProgramValue::of_bool(flag.clone()))
        .expect("a `Bool` binder's cast has a range");
    assert_eq!(
        facts.last(),
        Some(&Proposition::Or(Box::new(equals(0)), Box::new(equals(1))))
    );
    // An integer that is a cast states its own range; a constant, a bare
    // word and a value that is not a cast state nothing.
    assert_eq!(
        program_bool_cast_range_facts(&int32(cast.clone())),
        Some(facts.clone())
    );
    assert_eq!(program_bool_cast_range_facts(&bool_value(5)), None);
    assert_eq!(
        program_bool_cast_range_facts(&ProgramValue::Bool(MachineTerm::Variable(Variable(2)))),
        None
    );
    assert_eq!(
        program_bool_cast_range_facts(&int32(MachineTerm::Variable(Variable(2)))),
        None
    );
}

#[test]
fn contract_claim_rejects_caller_supplied_false_entry_fact() {
    let function = program_function(
        ProgramType::Int32,
        "false_postcondition",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        ExecutionState::new(),
        function.clone(),
        Vec::new(),
        vec![Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )],
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        program_verified_function_contract_claim(
            &function,
            FunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none()
    );
}

#[test]
fn decision_memo_distinguishes_equal_shaped_fact_sets_by_content() {
    // The decide memo is keyed by fact-set content identity. Two fact sets
    // that answer the same condition differently must never share a memo
    // entry, no matter how the objects are allocated or reused, and asking
    // one right after the other (in both orders) must not leak either
    // answer to the other.
    let x = MachineTerm::Variable(Variable(1));
    let below = ConditionTerm::signed_less_than(x.clone(), MachineTerm::constant(10));
    let assumes_true = PureFactContext::new().assume_condition(below.clone(), true);
    let assumes_false = PureFactContext::new().assume_condition(below.clone(), false);

    for _ in 0..2 {
        assert_eq!(assumes_true.decide(&below), Some(true));
        assert_eq!(assumes_false.decide(&below), Some(false));
        assert_eq!(assumes_true.decide(&below), Some(true));
    }
}

#[test]
fn assumptions_clones_share_facts_and_cache_keys_are_content_stable() {
    let condition = ConditionTerm::signed_less_than(
        MachineTerm::Variable(Variable(9)),
        MachineTerm::constant(10),
    );
    let first = PureFactContext::new().assume_condition(condition.clone(), true);
    let clone = first.clone();
    let idempotent = clone.clone().assume_condition(condition.clone(), true);
    let rebuilt = PureFactContext::new().assume_condition(condition.clone(), true);
    let changed = PureFactContext::new().assume_condition(condition, false);

    assert!(first.shares_fact_storage_with(&clone));
    assert!(clone.shares_fact_storage_with(&idempotent));
    assert_eq!(first.memo_fingerprint(), rebuilt.memo_fingerprint());
    assert_ne!(first.memo_fingerprint(), changed.memo_fingerprint());
}

/// `int32 early() { if (0 < 1) { return 0; } return 1; }` with one retained
/// trace: a single statement theorem for the `if` whose outcome is
/// `outcome`. The condition is never evaluated by the proof object, so the
/// theorem's shape is what these tests exercise.
fn early_return_inputs(
    outcome: StatementOutcome,
) -> (
    FunctionExecutionCandidates,
    ProgramFunction,
    crate::kernel::proof::ExecutionEvidence,
) {
    let branch = program_if(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ),
        program_return(crate::kernel::program_expression::int32_literal(0)),
        ProgramStatement::Skip,
    );
    let function = program_function(
        ProgramType::Int32,
        "early",
        Vec::new(),
        program_seq(
            branch.clone(),
            program_return(crate::kernel::program_expression::int32_literal(1)),
        ),
    );
    let caller_state = ExecutionState::new();
    let entry_state = program_function_entry_state(&caller_state, &function, &[])
        .expect("a parameterless function binds its entry state");
    let (function_outcome, obligations) = program_function_outcome_from_statement_outcome(
        &caller_state,
        &function,
        outcome.clone(),
        Vec::new(),
        &PureFactContext::new(),
    );
    let candidates = program_function_execution_candidates_from_outcomes(
        caller_state,
        function.clone(),
        Vec::new(),
        vec![(function_outcome, Vec::new(), obligations)],
    );
    let theorem = Theorem::new(Proposition::ProgramStatementVerifies {
        state: Box::new(entry_state),
        statement: Box::new(branch),
        outcome,
    });
    let mut trace = crate::kernel::proof::ExecutionEvidence::default();
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Statement(
        theorem,
    ));
    (candidates, function, trace)
}

/// Records a trace's events on a fresh proof object one by one, as a
/// driver would (a theorem with the context event that follows it, the
/// candidate path's facts as each step's execution facts), and completes
/// it. The first record call the proof object refuses, or completion's
/// refusal, is the error.
fn complete_early_return(
    candidates: &FunctionExecutionCandidates,
    function: &ProgramFunction,
    trace: crate::kernel::proof::ExecutionEvidence,
) -> Result<CheckedFunctionExecution, &'static str> {
    use crate::kernel::proof::CheckedExecutionEvent;
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    let events = trace.to_vec();
    let execution_facts = candidates.paths()[0].facts();
    let mut index = 0;
    while index < events.len() {
        let context = match events.get(index + 1) {
            Some(CheckedExecutionEvent::Context(context)) => context.as_ref().clone(),
            _ => PureFactContext::new(),
        };
        match &events[index] {
            CheckedExecutionEvent::Statement(theorem) => core
                .record_statement_transition(
                    function,
                    &[],
                    theorem.clone(),
                    context,
                    execution_facts,
                    &[],
                )
                .map_err(|refusal| refusal.reason)?,
            CheckedExecutionEvent::Condition(theorem) => core
                .record_condition_transition(function, &[], theorem.clone(), context, &[], &[])
                .map_err(|refusal| refusal.reason)?,
            CheckedExecutionEvent::Context(_) => {}
            _ => return Err("the test records only theorems"),
        }
        index += 1;
    }
    core.checked_function_execution(
        candidates,
        function,
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        FunctionContractExecutionMode::VerifyLoops,
    )
}

#[test]
fn completion_accepts_a_return_that_leaves_source_behind_it() {
    let entry_state = program_function_entry_state(
        &ExecutionState::new(),
        &program_function(
            ProgramType::Int32,
            "early",
            Vec::new(),
            ProgramStatement::Skip,
        ),
        &[],
    )
    .expect("entry state");
    let returning = StatementOutcome::Return {
        value: int32(0).into(),
        state: Box::new(entry_state),
    };
    let (candidates, function, trace) = early_return_inputs(returning);
    let _ = crate::kernel::api::take_checked_function_body_execution_count();
    let completed = complete_early_return(&candidates, &function, trace)
        .expect("a returning `if` completes although `return 1` follows it in the source");
    assert_eq!(completed.paths().len(), 1);
    let mut conclusion = completed.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    assert!(
        matches!(
            conclusion,
            Proposition::ProgramFunctionVerifies { outcome, .. } if outcome == candidates.paths()[0].outcome()
        ),
        "the path theorem concludes the candidate's outcome: {conclusion:?}"
    );
    assert_eq!(
        crate::kernel::api::take_checked_function_body_execution_count(),
        0,
        "completion composes retained theorems; it never executes the body"
    );
}

#[test]
fn completion_refuses_a_trace_that_stops_before_the_path_ends() {
    let entry_state = program_function_entry_state(
        &ExecutionState::new(),
        &program_function(
            ProgramType::Int32,
            "early",
            Vec::new(),
            ProgramStatement::Skip,
        ),
        &[],
    )
    .expect("entry state");
    // A `Normal` outcome for the `if` leaves `return 1` unexecuted: no
    // retained theorem covers it, so the path has no completed outcome.
    let (candidates, function, trace) =
        early_return_inputs(StatementOutcome::Normal(Box::new(entry_state.clone())));
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("a trace does not reach a return")
    );

    // A trace that continues past its returning statement is refused too.
    let returning = StatementOutcome::Return {
        value: int32(0).into(),
        state: Box::new(entry_state.clone()),
    };
    let (candidates, function, mut trace) = early_return_inputs(returning);
    trace.push(crate::kernel::proof::CheckedExecutionEvent::Statement(
        Theorem::new(Proposition::ProgramStatementVerifies {
            state: Box::new(entry_state.clone()),
            statement: Box::new(program_return(
                crate::kernel::program_expression::int32_literal(1),
            )),
            outcome: StatementOutcome::Return {
                value: int32(1).into(),
                state: Box::new(entry_state),
            },
        }),
    ));
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence was recorded after the trace completed")
    );
}

/// `int32 skipping() { ; return 1; }`: a body whose first statement is the
/// `Skip` an empty `if` arm leaves behind, with the given retained trace.
fn skip_inputs(
    events: Vec<crate::kernel::proof::CheckedExecutionEvent>,
) -> (
    FunctionExecutionCandidates,
    ProgramFunction,
    crate::kernel::proof::ExecutionEvidence,
) {
    let function = program_function(
        ProgramType::Int32,
        "skipping",
        Vec::new(),
        program_seq(
            ProgramStatement::Skip,
            program_return(crate::kernel::program_expression::int32_literal(1)),
        ),
    );
    let caller_state = ExecutionState::new();
    let outcome = StatementOutcome::Return {
        value: int32(1).into(),
        state: Box::new(caller_state.clone()),
    };
    let (function_outcome, obligations) = program_function_outcome_from_statement_outcome(
        &caller_state,
        &function,
        outcome,
        Vec::new(),
        &PureFactContext::new(),
    );
    let candidates = program_function_execution_candidates_from_outcomes(
        caller_state,
        function.clone(),
        Vec::new(),
        vec![(function_outcome, Vec::new(), obligations)],
    );
    let mut trace = crate::kernel::proof::ExecutionEvidence::default();
    for event in events {
        trace.push(event);
    }
    (candidates, function, trace)
}

fn skip_theorem(state: ExecutionState) -> crate::kernel::proof::CheckedExecutionEvent {
    crate::kernel::proof::CheckedExecutionEvent::Statement(Theorem::new(
        Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(ProgramStatement::Skip),
            outcome: StatementOutcome::Normal(Box::new(state)),
        },
    ))
}

fn return_one_theorem(state: ExecutionState) -> crate::kernel::proof::CheckedExecutionEvent {
    crate::kernel::proof::CheckedExecutionEvent::Statement(Theorem::new(
        Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(program_return(
                crate::kernel::program_expression::int32_literal(1),
            )),
            outcome: StatementOutcome::Return {
                value: int32(1).into(),
                state: Box::new(state),
            },
        },
    ))
}

#[test]
fn recording_passes_over_skip_on_either_side() {
    let entry = ExecutionState::new();
    // The driver stepped through the `Skip`: it consumes the source's `Skip`.
    let (candidates, function, trace) = skip_inputs(vec![
        skip_theorem(entry.clone()),
        return_one_theorem(entry.clone()),
    ]);
    complete_early_return(&candidates, &function, trace)
        .expect("a `Skip` theorem consumes the `Skip` at the head of the source");
    // The driver completed the empty arm in place: the source's `Skip` is
    // passed over before the real statement is matched.
    let (candidates, function, trace) = skip_inputs(vec![return_one_theorem(entry.clone())]);
    complete_early_return(&candidates, &function, trace)
        .expect("a `Skip` left in the source is passed over");
    // An extra `Skip` theorem touches nothing.
    let (candidates, function, trace) = skip_inputs(vec![
        skip_theorem(entry.clone()),
        skip_theorem(entry.clone()),
        return_one_theorem(entry.clone()),
    ]);
    complete_early_return(&candidates, &function, trace)
        .expect("a second `Skip` theorem is a no-op");
    // A `Skip` theorem must still start from the reached state. (The first
    // event names the trace's entry state, so the mismatch is placed second.)
    let elsewhere = ExecutionState::new().with_local("x", int32(1));
    let (candidates, function, trace) = skip_inputs(vec![
        skip_theorem(entry.clone()),
        skip_theorem(elsewhere),
        return_one_theorem(entry),
    ]);
    assert_eq!(
        complete_early_return(&candidates, &function, trace).err(),
        Some("evidence does not start from the running state")
    );
}

#[test]
fn completion_accepts_a_case_arm_recorded_after_the_return() {
    // A post-execution case split records its arm after the path's
    // returning statement. Both arms must be present across the traces.
    let entry_state = program_function_entry_state(
        &ExecutionState::new(),
        &program_function(
            ProgramType::Int32,
            "early",
            Vec::new(),
            ProgramStatement::Skip,
        ),
        &[],
    )
    .expect("entry state");
    let returning = StatementOutcome::Return {
        value: int32(0).into(),
        state: Box::new(entry_state),
    };
    let (candidates, function, trace) = early_return_inputs(returning);
    let root = crate::kernel::proof::ProofFacts::default();
    let then_fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(1_000_050)),
            MachineTerm::constant(5),
        ),
        true,
    );
    let else_fact = Proposition::Not(Box::new(then_fact.clone()));
    let partition = crate::kernel::proof::CheckedProofCasePartition::check(
        &root,
        then_fact.clone(),
        else_fact.clone(),
    )
    .expect("complementary case facts");
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    let outcomes = trace
        .to_vec()
        .into_iter()
        .filter_map(|event| match event {
            crate::kernel::proof::CheckedExecutionEvent::Statement(theorem) => Some(theorem),
            _ => None,
        })
        .map(|theorem| (theorem, &[][..], &[][..]))
        .collect::<Vec<_>>();
    core.record_statement_outcomes(&function, &[], &outcomes, PureFactContext::new())
        .expect("the returning branch theorem advances the entry frontier");
    core.fork_outcome_evidence(&[crate::kernel::proof::OutcomeEvidenceFork::binary(
        partition,
        [root.with_fact(then_fact), root.with_fact(else_fact)],
        [
            crate::kernel::proof::OutcomeEvidenceFork::Keep,
            crate::kernel::proof::OutcomeEvidenceFork::Keep,
        ],
    )])
    .expect("the single trace forks into both arms");
    let traces = core.execution_evidence.to_vec();
    assert_eq!(traces.len(), 2);
    let candidate = candidates.paths()[0].clone();
    let copy = || {
        (
            candidate.outcome().clone(),
            candidate.facts().to_vec(),
            candidate.obligations().to_vec(),
        )
    };
    let forked = program_function_execution_candidates_from_outcomes(
        candidates.state().clone(),
        function.clone(),
        Vec::new(),
        vec![copy(), copy()],
    );
    core.checked_function_execution(
        &forked,
        &function,
        PureFactContext::new(),
        ExecutionEnvironment::new(),
        ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        FunctionContractExecutionMode::VerifyLoops,
    )
    .expect("both forked paths complete with their case arms");
    // One arm alone is not exhaustive.
    let one_arm = program_function_execution_candidates_from_outcomes(
        candidates.state().clone(),
        function.clone(),
        Vec::new(),
        vec![copy()],
    );
    let mut one_trace = core.clone();
    one_trace.execution_evidence = vec![traces[0].clone()].into();
    assert_eq!(
        one_trace
            .checked_function_execution(
                &one_arm,
                &function,
                PureFactContext::new(),
                ExecutionEnvironment::new(),
                ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
                FunctionContractExecutionMode::VerifyLoops,
            )
            .err(),
        Some("a proof-case partition is not exhausted by the retained traces")
    );
}

#[test]
fn contract_exit_rule_is_the_plain_outcome_without_resources() {
    let function = program_function(
        ProgramType::Int32,
        "plain",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(3)),
    );
    let caller_state = ExecutionState::new();
    let entry_state = program_function_entry_state(&caller_state, &function, &[]).expect("entry");
    let returning = StatementOutcome::Return {
        value: int32(3).into(),
        state: Box::new(entry_state),
    };
    let (plain, _) = program_function_outcome_from_statement_outcome(
        &caller_state,
        &function,
        returning.clone(),
        Vec::new(),
        &PureFactContext::new(),
    );
    let (exit_outcome, _, _) = crate::kernel::functions::contract_exit_outcome(
        &caller_state,
        &function,
        &[],
        returning,
        Vec::new(),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
        crate::kernel::functions::ResourceTransitionPurpose::FunctionBoundary,
    )
    .expect("no execution limit")
    .expect("no runtime error");
    assert_eq!(exit_outcome, plain);
}

#[test]
fn recording_complete_sequence_requires_exact_remaining_source() {
    let body = program_seq(
        program_return(crate::kernel::program_expression::int32_literal(0)),
        program_return(crate::kernel::program_expression::int32_literal(1)),
    );
    let function = program_function(ProgramType::Int32, "sequence", Vec::new(), body.clone());
    let entry =
        program_function_entry_state(&ExecutionState::new(), &function, &[]).expect("entry");
    for (statement, accepted) in [
        (body, true),
        (
            program_seq(
                program_return(crate::kernel::program_expression::int32_literal(0)),
                program_return(crate::kernel::program_expression::int32_literal(2)),
            ),
            false,
        ),
        (
            program_seq(
                ProgramStatement::Skip,
                program_return(crate::kernel::program_expression::int32_literal(1)),
            ),
            false,
        ),
    ] {
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            ExecutionState::new(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        let evidence = Theorem::new(Proposition::ProgramStatementVerifies {
            state: Box::new(entry.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(0).into(),
                state: Box::new(entry.clone()),
            },
        });
        let recorded = core.record_statement_transition(
            &function,
            &[],
            evidence,
            PureFactContext::new(),
            &[],
            &[],
        );
        assert_eq!(recorded.is_ok(), accepted);
        if accepted {
            assert!(core.evidence_source.is_none());
        }
    }
}

#[test]
fn recording_statement_evidence_checks_it_advances_the_frontier() {
    // The record call checks that the theorem proves the frontier's next
    // source statement from the running state.
    let branch = program_if(
        crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ),
        program_return(crate::kernel::program_expression::int32_literal(0)),
        ProgramStatement::Skip,
    );
    let function = program_function(
        ProgramType::Int32,
        "early",
        Vec::new(),
        program_seq(
            branch.clone(),
            program_return(crate::kernel::program_expression::int32_literal(1)),
        ),
    );
    let entry_state = program_function_entry_state(&ExecutionState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let verifies = |state: ExecutionState, statement: ProgramStatement| {
        Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(0).into(),
                state: Box::new(state),
            },
        }
    };
    let record = |theorem: Theorem, context: PureFactContext| {
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            ExecutionState::new(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        core.record_statement_transition(&function, &[], theorem, context, &[], &[])
    };
    record(
        Theorem::new(verifies(entry_state.clone(), branch.clone())),
        PureFactContext::new(),
    )
    .expect("the body's first statement from the entry state advances the entry frontier");
    let refusal = record(
        Theorem::new(verifies(
            entry_state.clone(),
            program_return(crate::kernel::program_expression::int32_literal(1)),
        )),
        PureFactContext::new(),
    )
    .expect_err("a later statement is not the frontier's next");
    assert_eq!(
        refusal.reason,
        "statement evidence does not prove the frontier's next source statement"
    );
    assert_eq!(refusal.expected.as_ref(), Some(&branch));
    assert_eq!(
        refusal.proved,
        Some(program_return(
            crate::kernel::program_expression::int32_literal(1)
        ))
    );
    let elsewhere = entry_state.clone().with_local("x", int32(1));
    assert_eq!(
        record(
            Theorem::new(verifies(elsewhere, branch.clone())),
            PureFactContext::new(),
        )
        .map_err(|refusal| refusal.reason),
        Err("evidence does not start from the running state")
    );
}

#[test]
fn recording_condition_evidence_checks_it_decides_the_frontier() {
    // The condition record call checks the same for the theorem that
    // selects an `if` arm or a loop iteration: it decides the frontier's
    // next `if` or `while` condition, from the running state.
    let condition = crate::kernel::program_expression::less_than(
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let branch = program_if(
        condition.clone(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
        ProgramStatement::Skip,
    );
    let function = program_function(
        ProgramType::Int32,
        "early",
        Vec::new(),
        program_seq(
            branch,
            program_return(crate::kernel::program_expression::int32_literal(1)),
        ),
    );
    let entry_state = program_function_entry_state(&ExecutionState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let evaluates = |state: ExecutionState, condition: crate::kernel::ProgramExpression| {
        Proposition::ProgramConditionEvaluates {
            state: Box::new(state),
            condition,
            outcome: crate::kernel::ConditionOutcome::Value(true),
        }
    };
    let record = |theorem: Theorem, context: PureFactContext, path_facts: &[Proposition]| {
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            ExecutionState::new(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        core.record_condition_transition(&function, &[], theorem, context, path_facts, &[])
            .map_err(|refusal| refusal.reason)
    };
    record(
        Theorem::new(evaluates(entry_state.clone(), condition.clone())),
        PureFactContext::new(),
        &[],
    )
    .expect("the body's `if` condition from the entry state decides the entry frontier");
    assert_eq!(
        record(
            Theorem::new(evaluates(
                entry_state.clone(),
                crate::kernel::program_expression::less_than(
                    crate::kernel::program_expression::int32_literal(1),
                    crate::kernel::program_expression::int32_literal(0)
                ),
            )),
            PureFactContext::new(),
            &[],
        ),
        Err("condition evidence does not decide the frontier's next source condition")
    );
    let elsewhere = entry_state.clone().with_local("x", int32(1));
    assert_eq!(
        record(
            Theorem::new(evaluates(elsewhere, condition.clone())),
            PureFactContext::new(),
            &[],
        ),
        Err("evidence does not start from the running state")
    );
    // A statement that is not an `if` or `while` cannot be decided.
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    let returning = program_function(
        ProgramType::Int32,
        "returning",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    assert_eq!(
        core.record_condition_transition(
            &returning,
            &[],
            Theorem::new(Proposition::ProgramConditionEvaluates {
                state: Box::new(
                    program_function_entry_state(&ExecutionState::new(), &returning, &[])
                        .expect("entry")
                ),
                condition: crate::kernel::program_expression::less_than(
                    crate::kernel::program_expression::int32_literal(0),
                    crate::kernel::program_expression::int32_literal(1)
                ),
                outcome: crate::kernel::ConditionOutcome::Value(true),
            }),
            PureFactContext::new(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason),
        Err("condition evidence does not decide the frontier's next `if` or `while`")
    );
}

#[test]
fn condition_evidence_cannot_decide_a_do_while_before_its_body() {
    // `do { return 1; } while (0); return 0;` runs its body first. Evidence
    // that decides the loop's `0` at the head would select the tail and
    // skip the body, so the proof object refuses it: at a `do`-`while`
    // head the next statement is the body's first.
    let function = program_function(
        ProgramType::Int32,
        "runs_body",
        Vec::new(),
        program_seq(
            crate::kernel::program_do_while(
                crate::kernel::program_expression::int32_literal(0),
                program_return(crate::kernel::program_expression::int32_literal(1)),
            ),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
    );
    let entry_state = program_function_entry_state(&ExecutionState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    assert_eq!(
        core.record_condition_transition(
            &function,
            &[],
            Theorem::new(Proposition::ProgramConditionEvaluates {
                state: Box::new(entry_state),
                condition: crate::kernel::program_expression::int32_literal(0),
                outcome: crate::kernel::ConditionOutcome::Value(false),
            }),
            PureFactContext::new(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason),
        Err("condition evidence does not decide the frontier's next `if` or `while`")
    );
}

#[test]
fn recorded_evidence_reaches_the_theorem_outcome_not_the_driver_state() {
    // The proof object validates its chain from the theorems alone: the
    // next theorem must start from the state the recorded evidence
    // reached, whatever the driver's own copy of the state says.
    let condition = crate::kernel::program_expression::less_than(
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let branch = program_if(
        condition.clone(),
        ProgramStatement::Skip,
        ProgramStatement::Skip,
    );
    let tail = program_return(crate::kernel::program_expression::int32_literal(1));
    let function = program_function(
        ProgramType::Int32,
        "early",
        Vec::new(),
        program_seq(branch, tail.clone()),
    );
    let entry_state = program_function_entry_state(&ExecutionState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    core.record_condition_transition(
        &function,
        &[],
        Theorem::new(Proposition::ProgramConditionEvaluates {
            state: Box::new(entry_state.clone()),
            condition,
            outcome: crate::kernel::ConditionOutcome::Value(true),
        }),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the condition decides the entry `if`");
    assert_eq!(core.reached_state(), &entry_state);
    // The driver moves its frontier past the `if` but drifts its own state.
    core.frontier.position = crate::kernel::proof::FrontierPosition::StatementEntry {
        remaining: std::sync::Arc::new(tail.clone()),
    };
    let drifted = entry_state.clone().with_local("x", int32(1));
    core.state = drifted.clone().into();
    let returning = |state: ExecutionState| {
        Theorem::new(Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(tail.clone()),
            outcome: StatementOutcome::Return {
                value: int32(1).into(),
                state: Box::new(state),
            },
        })
    };
    assert_eq!(
        core.record_statement_transition(
            &function,
            &[],
            returning(drifted),
            PureFactContext::new(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason),
        Err("evidence does not start from the running state")
    );
    core.record_statement_transition(
        &function,
        &[],
        returning(entry_state.clone()),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the return from the reached state is accepted");
    assert_eq!(core.reached_state(), &entry_state);
    assert_eq!(
        core.record_statement_transition(
            &function,
            &[],
            returning(entry_state),
            PureFactContext::new(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason),
        Err("evidence was recorded after the trace completed")
    );
}

#[test]
fn recorded_evidence_consumes_the_source_not_the_driver_frontier() {
    // Once evidence is recorded, the next theorem is checked against the
    // source the evidence has yet to consume, whatever the driver's
    // frontier says.
    let condition = crate::kernel::program_expression::less_than(
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    );
    let branch = program_if(
        condition.clone(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
        ProgramStatement::Skip,
    );
    let tail = program_return(crate::kernel::program_expression::int32_literal(1));
    let function = program_function(
        ProgramType::Int32,
        "early",
        Vec::new(),
        program_seq(branch, tail.clone()),
    );
    let entry_state = program_function_entry_state(&ExecutionState::new(), &function, &[])
        .expect("a parameterless function binds its entry state");
    let returning = |statement: ProgramStatement, value: u32| {
        Theorem::new(Proposition::ProgramStatementVerifies {
            state: Box::new(entry_state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Return {
                value: int32(value).into(),
                state: Box::new(entry_state.clone()),
            },
        })
    };
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    // Selecting the empty else arm leaves the tail to consume.
    core.record_condition_transition(
        &function,
        &[],
        Theorem::new(Proposition::ProgramConditionEvaluates {
            state: Box::new(entry_state.clone()),
            condition,
            outcome: crate::kernel::ConditionOutcome::Value(false),
        }),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the condition decides the entry `if`");
    assert_eq!(core.evidence_source.as_deref(), Some(&tail));
    // The driver's frontier still names the `if`'s then arm.
    core.frontier.position = crate::kernel::proof::FrontierPosition::StatementEntry {
        remaining: std::sync::Arc::new(program_return(
            crate::kernel::program_expression::int32_literal(0),
        )),
    };
    let refusal = core
        .record_statement_transition(
            &function,
            &[],
            returning(
                program_return(crate::kernel::program_expression::int32_literal(0)),
                0,
            ),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect_err("the driver's frontier does not decide the source");
    assert_eq!(
        refusal.reason,
        "statement evidence does not prove the frontier's next source statement"
    );
    assert_eq!(refusal.expected.as_ref(), Some(&tail));
    assert_eq!(
        refusal.proved,
        Some(program_return(
            crate::kernel::program_expression::int32_literal(0)
        ))
    );
    core.record_statement_transition(
        &function,
        &[],
        returning(tail, 1),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("the tail is the source the evidence has yet to consume");
    assert!(core.evidence_source.is_none());
}

#[test]
fn void_fallthrough_completion_requires_consuming_the_entire_source() {
    for (return_type, pending_return) in [
        (ProgramType::Void, false),
        (ProgramType::Void, true),
        (ProgramType::Int32, false),
    ] {
        let body = if pending_return {
            ProgramStatement::seq(
                std::sync::Arc::new(ProgramStatement::Skip),
                std::sync::Arc::new(program_return(program_void_value())),
            )
        } else {
            ProgramStatement::Skip
        };
        let function = program_function(return_type, "fallthrough", Vec::new(), body);
        let caller = ExecutionState::new();
        let entry = program_function_entry_state(&caller, &function, &[]).expect("entry");
        let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
            caller.clone(),
            crate::kernel::proof::ExecutionFrontier::default(),
        );
        core.record_statement_transition(
            &function,
            &[],
            Theorem::new(Proposition::ProgramStatementVerifies {
                state: Box::new(entry.clone()),
                statement: Box::new(ProgramStatement::Skip),
                outcome: StatementOutcome::Normal(Box::new(entry.clone())),
            }),
            PureFactContext::new(),
            &[],
            &[],
        )
        .expect("checked next statement");
        let (outcome, obligations) = program_function_outcome_from_statement_outcome(
            &caller,
            &function,
            StatementOutcome::Return {
                value: ProgramValue::Void.into(),
                state: Box::new(entry),
            },
            Vec::new(),
            &PureFactContext::new(),
        );
        let candidates = program_function_execution_candidates_from_outcomes(
            caller,
            function.clone(),
            Vec::new(),
            vec![(outcome, Vec::new(), obligations)],
        );
        let result = core.checked_function_execution(
            &candidates,
            &function,
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            FunctionContractExecutionMode::VerifyLoops,
        );
        assert_eq!(
            result.is_ok(),
            return_type == ProgramType::Void && !pending_return
        );
    }
}

#[test]
fn a_completed_proof_object_yields_its_checked_execution() {
    // Completion composes the checked traces into one path per trace
    // concluding the candidate's outcome; an open trace yields nothing.
    let entry_state = program_function_entry_state(
        &ExecutionState::new(),
        &program_function(
            ProgramType::Int32,
            "early",
            Vec::new(),
            ProgramStatement::Skip,
        ),
        &[],
    )
    .expect("entry state");
    let returning = StatementOutcome::Return {
        value: int32(0).into(),
        state: Box::new(entry_state.clone()),
    };
    let (candidates, function, trace) = early_return_inputs(returning);
    let theorem = match trace.to_vec().into_iter().next() {
        Some(crate::kernel::proof::CheckedExecutionEvent::Statement(theorem)) => theorem,
        _ => unreachable!("the trace begins with its returning theorem"),
    };
    let mut core = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    core.record_statement_transition(&function, &[], theorem, PureFactContext::new(), &[], &[])
        .expect("the returning branch theorem advances the entry frontier");
    let completed = core
        .checked_function_execution(
            &candidates,
            &function,
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            FunctionContractExecutionMode::VerifyLoops,
        )
        .expect("a completed proof object yields its checked function execution");
    assert_eq!(completed.paths().len(), 1);
    let mut conclusion = completed.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    assert!(matches!(
        conclusion,
        Proposition::ProgramFunctionVerifies { outcome, .. } if outcome == candidates.paths()[0].outcome()
    ));

    let mut open = crate::kernel::proof::ExecutionProofCore::at_entry(
        ExecutionState::new(),
        crate::kernel::proof::ExecutionFrontier::default(),
    );
    open.record_statement_transition(
        &function,
        &[],
        Theorem::new(Proposition::ProgramStatementVerifies {
            state: Box::new(entry_state.clone()),
            statement: Box::new(ProgramStatement::Skip),
            outcome: StatementOutcome::Normal(Box::new(entry_state)),
        }),
        PureFactContext::new(),
        &[],
        &[],
    )
    .expect("a `Skip` theorem consumes nothing");
    assert_eq!(
        open.checked_function_execution(
            &candidates,
            &function,
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
            FunctionContractExecutionMode::VerifyLoops,
        )
        .err(),
        Some("a trace does not reach a return")
    );
}

#[test]
fn completion_key_folds_trivial_conditions_the_proof_lowering_folds() {
    use crate::kernel::api::completion_key;
    let x = MachineTerm::Variable(Variable(1));
    let y = MachineTerm::Variable(Variable(2));
    let truth = |value: bool| Proposition::ConditionIs(ConditionTerm::Constant(value), true);
    let equal = |left: &MachineTerm, right: &MachineTerm, value: bool| {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            },
            value,
        )
    };
    let nontrivial = equal(&x, &y, true);

    // A term compared with itself is a constant.
    assert_eq!(completion_key(&equal(&x, &x, true)), truth(true));
    assert_eq!(completion_key(&equal(&x, &x, false)), truth(false));
    // A constant condition folds to the canonical truth value.
    assert_eq!(
        completion_key(&Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            false
        )),
        truth(true)
    );
    // Negating a constant stays in the canonical truth form.
    assert_eq!(
        completion_key(&Proposition::Not(Box::new(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )))),
        truth(true)
    );
    // Negating a condition flips its value.
    assert_eq!(
        completion_key(&Proposition::Not(Box::new(nontrivial.clone()))),
        equal(&x, &y, false)
    );
    // Constant premises and conjuncts disappear.
    assert_eq!(
        completion_key(&Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Constant(false),
                false
            )),
            Box::new(nontrivial.clone()),
        )),
        nontrivial
    );
    assert_eq!(
        completion_key(&Proposition::And(
            Box::new(equal(&y, &y, true)),
            Box::new(nontrivial.clone()),
        )),
        nontrivial
    );
    assert_eq!(
        completion_key(&Proposition::Or(
            Box::new(nontrivial.clone()),
            Box::new(truth(true))
        )),
        truth(true)
    );
    // A quantifier folds its body, and over a constant body is the constant.
    let quantified = |body: Proposition| Proposition::ForAll {
        name: Default::default(),
        var: Variable(3),
        sort: Sort::ProgramInt32,
        body: Box::new(body),
    };
    assert_eq!(
        completion_key(&quantified(equal(&x, &x, true))),
        truth(true)
    );
    assert_eq!(
        completion_key(&quantified(Proposition::And(
            Box::new(truth(true)),
            Box::new(nontrivial.clone()),
        ))),
        quantified(nontrivial.clone())
    );
    // Nothing else changes.
    assert_eq!(completion_key(&nontrivial), nontrivial);
}

/// A call requirement the caller cannot discharge becomes a precondition
/// obligation, and that obligation now carries the head chain the lowering
/// that built it recorded: the guards lowering inserted in front of the
/// requirement, in the order an introduction reaches them.
///
/// The requirement here adds one to the symbolic argument, so lowering guards
/// it with the no-overflow premise the caller state does not establish.
/// Nothing pairs that guard with a written connective by shape: the record
/// says it is one lowering inserted.
#[test]
fn call_requirement_obligations_carry_their_lowering_record() {
    let successor_is_positive = SpecProposition::Comparison {
        left: SpecExpression::Add(
            Box::new(SpecExpression::ProgramExpression(
                crate::kernel::program_expression::variable("n"),
            )),
            Box::new(SpecExpression::ProgramExpression(
                crate::kernel::program_expression::int32_literal(1),
            )),
        ),
        operator: ComparisonOperator::GreaterThan,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
    };
    let returns_one = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            C_CONTRACT_RESULT_NAME,
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            1,
        )),
    };
    let helper = program_function(
        ProgramType::Int32,
        "successor_is_positive",
        vec![program_parameter("n", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(1)),
    )
    .with_contract(
        vec![successor_is_positive],
        vec![returns_one],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_local("n", int32(MachineTerm::Variable(Variable(31_000))));
    let execution = prove_symbolic_program_execution_paths_with_environment(
        state,
        program_call_then_assign(
            9,
            "result",
            "successor_is_positive",
            vec![crate::kernel::program_expression::variable("n")],
        ),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("verified call path");
    let obligation = path
        .obligations()
        .iter()
        .find(|obligation| obligation.context() == Some("successor_is_positive precondition"))
        .unwrap_or_else(|| {
            panic!(
                "an undischarged precondition should be emitted: {:#?}",
                path.obligations()
            )
        });
    let recorded = obligation
        .introductions()
        .expect("a kernel-built call requirement carries its lowering record");
    assert!(
        recorded.is_empty(),
        "arithmetic debts do not introduce guards"
    );
    let domain = Proposition::signed_arithmetic_domain(
        MachineIntegerType::Int32,
        MachineBinaryOp::Add,
        &MachineTerm::Variable(Variable(31_000)),
        &MachineTerm::constant(1),
    );
    assert!(
        path.obligations()
            .iter()
            .any(|debt| debt.proposition() == &domain)
    );
}

/// A self-recursive function that declares an expression `decreases` measure.
/// Its body is irrelevant here: what is exercised is the call step.
fn drain_with_expression_measure() -> ProgramFunction {
    program_function(
        ProgramType::Int32,
        "drain",
        vec![program_parameter("n", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(
                crate::kernel::program_expression::int32_literal(0),
            ),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    )
    .with_recursion_measure(vec![RankingComponent::Pure {
        source: "level(n)".to_string(),
        expression: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            "n",
        )),
    }])
}

fn opaque_rule_environment(function: ProgramFunction) -> ExecutionEnvironment {
    ExecutionEnvironment::new()
        .with_function(function.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        })
}

fn symbolic_caller_state() -> ExecutionState {
    ExecutionState::new()
        .with_population_creation_tracking()
        .with_local("n", int32(MachineTerm::Variable(Variable(31_000))))
}

/// The entry `drain` is anchored at: its parameter bound to the same symbolic
/// value the caller state holds, which is what makes M0 that value.
fn symbolic_entry_arguments() -> Vec<ProgramExpression> {
    vec![ProgramExpression::Value(int32(MachineTerm::Variable(
        Variable(31_000),
    )))]
}

/// The contexts of the ranking members a call step emitted, in order.
fn recursion_measure_contexts(path: &SymbolicExecutionPath) -> Vec<String> {
    path.obligations()
        .iter()
        .filter_map(|obligation| obligation.context())
        .filter(|context| context.contains("recursion measure"))
        .map(str::to_string)
        .collect()
}

fn call_path(
    environment: ExecutionEnvironment,
    callee: &str,
    argument: ProgramExpression,
) -> SymbolicExecution {
    prove_symbolic_program_execution_paths_with_environment(
        symbolic_caller_state(),
        program_call_then_assign(10, "result", callee, vec![argument]),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    )
}

/// The descent is checked at the call step, not by an analysis of the body.
/// This call's argument arithmetic already establishes the strict decrease,
/// so only the nonnegative member remains as an unresolved obligation.
#[test]
fn a_self_call_under_a_recursion_anchor_keeps_only_unresolved_ranking_members() {
    let drain = drain_with_expression_measure();
    let environment = program_execution_environment_with_recursion_anchor(
        opaque_rule_environment(drain.clone()),
        &drain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("the declared measure reads at the entry state");
    let execution = call_path(
        environment,
        "drain",
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::variable("n"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    );
    let path = execution.paths().first().expect("verified call path");
    assert_eq!(
        recursion_measure_contexts(path),
        vec![
            "drain recursion measure: `level(n)` is nonnegative at the recursive call".to_string(),
        ],
        "{:#?}",
        path.obligations()
    );
}

/// Without the anchor the same call is an ordinary opaque application. A
/// measure on the interface changes nothing by itself: it is the
/// certification of `drain` that owes the descent, and only there.
#[test]
fn a_call_without_a_recursion_anchor_owes_no_ranking_member() {
    let drain = drain_with_expression_measure();
    let execution = call_path(
        opaque_rule_environment(drain),
        "drain",
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::variable("n"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    );
    let path = execution.paths().first().expect("verified call path");
    assert!(
        recursion_measure_contexts(path).is_empty(),
        "{:#?}",
        path.obligations()
    );
}

/// The anchor names one function. A call to any other verified function,
/// while it is installed, is untouched.
#[test]
fn an_anchor_ranks_only_calls_to_the_function_it_names() {
    let drain = drain_with_expression_measure();
    let other = program_function(
        ProgramType::Int32,
        "other",
        vec![program_parameter("n", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(
                crate::kernel::program_expression::int32_literal(0),
            ),
        }],
        Vec::new(),
        vec![FunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = program_execution_environment_with_recursion_anchor(
        opaque_rule_environment(drain.clone())
            .with_function(other.clone())
            .with_verified_function_rule(VerifiedFunctionRule {
                pointer_result: None,
                function: other,
                loop_semantics: LoopSemantics::Verify,
                checked_callees: None,
                applied_tactics: Default::default(),
            }),
        &drain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("the declared measure reads at the entry state");
    let execution = call_path(
        environment,
        "other",
        crate::kernel::program_expression::variable("n"),
    );
    let path = execution.paths().first().expect("verified call path");
    assert!(
        recursion_measure_contexts(path).is_empty(),
        "{:#?}",
        path.obligations()
    );
}

/// A function that declares no measure gets its environment back unchanged,
/// so no certification that exists today changes shape or identity.
#[test]
fn a_function_without_a_declared_measure_installs_no_anchor() {
    let plain = program_function(
        ProgramType::Int32,
        "plain",
        vec![program_parameter("n", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let environment = opaque_rule_environment(plain.clone());
    let anchored = program_execution_environment_with_recursion_anchor(
        environment.clone(),
        &plain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("no declared measure is no work");
    assert_eq!(anchored, environment);
}

/// An anchored environment is a different environment. This is what stops a
/// checked execution recorded without the anchor -- one that raised no
/// descent obligation at its self-calls -- from being reused to certify a
/// contract whose function declares a measure.
#[test]
fn a_recursion_anchor_is_part_of_the_environment_identity() {
    let drain = drain_with_expression_measure();
    let plain = opaque_rule_environment(drain.clone());
    let anchored = program_execution_environment_with_recursion_anchor(
        plain.clone(),
        &drain,
        &symbolic_caller_state(),
        &symbolic_entry_arguments(),
    )
    .expect("the declared measure reads at the entry state");
    assert_ne!(anchored, plain);
}

/// The block a declaration mints is the object's identity, and about seventy
/// kernel sites read two equal blocks as one object. A called frame runs on
/// the caller's memory with its own locals map, so it cannot see the caller's
/// objects; if it minted the plain `local:<name>` anyway, the callee's object
/// and the caller's would be one block, one extent and one cell map.
#[test]
fn a_called_frames_declaration_does_not_take_the_callers_block() {
    let callers = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_memory(
            Memory::new()
                .with_block("local:x", 4)
                .store(callers.clone(), int32(1)),
        )
        .with_enclosing_frame_holds_locals(true);
    let statement = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(2)),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
    );
    let theorem = prove_symbolic_program_execution(state, statement, PureFactContext::new())
        .expect("a called frame declares its own local");
    let Proposition::ProgramStatementExecutes {
        outcome: StatementOutcome::Return { state: after, .. },
        ..
    } = theorem.proposition()
    else {
        panic!("expected a return: {:?}", theorem.proposition());
    };

    let minted = after.locals().slot("x").expect("the callee's own slot");
    assert_ne!(minted, &callers);
    assert_eq!(after.memory().cells.get(&callers), Some(int32(1)));
}

/// An identity is not free again once its object's lifetime has ended: the
/// tombstone is what makes an alias to the old object invalid, so handing the
/// block to a new object would revive every stale pointer to the old one.
#[test]
fn a_declaration_does_not_take_a_block_whose_lifetime_ended() {
    let retired = PointerBlock::from("local:x");
    let state = ExecutionState::new().with_memory(
        Memory::new()
            .with_block("local:x", 4)
            .without_local_block(&retired),
    );
    let statement = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(2)),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        ),
    );
    let theorem = prove_symbolic_program_execution(state, statement, PureFactContext::new())
        .expect("a declaration after an ended lifetime executes");
    let Proposition::ProgramStatementExecutes {
        outcome: StatementOutcome::Return { state: after, .. },
        ..
    } = theorem.proposition()
    else {
        panic!("expected a return: {:?}", theorem.proposition());
    };

    assert_ne!(
        &after
            .locals()
            .slot("x")
            .expect("the new object's slot")
            .block,
        &retired
    );
}

/// An automatic object's lifetime ends when control leaves the block that
/// declared it. An `if` arm is such a block: the address of a local it
/// declared designates no object once the arm is left, so a load through one
/// is undefined behaviour rather than a way to read what the arm wrote.
#[test]
fn an_if_arms_local_stops_existing_when_the_arm_is_left() {
    let arm = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(7)),
            program_assign("p", crate::kernel::program_expression::addr_of("x")),
        ),
    );
    let statement = program_seq(
        program_declare("anchor", ProgramType::Int32),
        program_seq(
            program_assign(
                "anchor",
                crate::kernel::program_expression::int32_literal(0),
            ),
            program_seq(
                program_declare("p", ProgramType::Int32Pointer),
                program_seq(
                    program_assign("p", crate::kernel::program_expression::addr_of("anchor")),
                    program_seq(
                        program_if(
                            crate::kernel::program_expression::variable("c"),
                            arm,
                            ProgramStatement::Skip,
                        ),
                        program_return(crate::kernel::program_expression::load(
                            crate::kernel::program_expression::variable("p"),
                        )),
                    ),
                ),
            ),
        ),
    );
    let state =
        ExecutionState::new().with_local("c", ProgramValue::Int32(MachineTerm::constant(1)));
    let theorem = prove_symbolic_program_execution(state, statement, PureFactContext::new())
        .expect("the taken arm is the only path");
    let Proposition::ProgramStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
        ),
        "reading an `if` arm's local after the arm is undefined behaviour, got {outcome:?}"
    );
}

/// A loop body is a block, and an iteration leaves it at the back edge as
/// well as at every exit, so a pointer to a body local does not outlive the
/// iteration that created it.
#[test]
fn a_loop_bodys_local_stops_existing_at_the_back_edge() {
    let body = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(9)),
            program_seq(
                program_assign("p", crate::kernel::program_expression::addr_of("x")),
                program_assign(
                    "i",
                    crate::kernel::program_expression::add(
                        crate::kernel::program_expression::variable("i"),
                        crate::kernel::program_expression::int32_literal(1),
                    ),
                ),
            ),
        ),
    );
    let statement = program_seq(
        program_declare("anchor", ProgramType::Int32),
        program_seq(
            program_assign(
                "anchor",
                crate::kernel::program_expression::int32_literal(0),
            ),
            program_seq(
                program_declare("p", ProgramType::Int32Pointer),
                program_seq(
                    program_assign("p", crate::kernel::program_expression::addr_of("anchor")),
                    program_seq(
                        program_declare("i", ProgramType::Int32),
                        program_seq(
                            program_assign(
                                "i",
                                crate::kernel::program_expression::int32_literal(0),
                            ),
                            program_seq(
                                program_while(
                                    crate::kernel::program_expression::less_than(
                                        crate::kernel::program_expression::variable("i"),
                                        crate::kernel::program_expression::int32_literal(2),
                                    ),
                                    Vec::new(),
                                    body,
                                ),
                                program_return(crate::kernel::program_expression::load(
                                    crate::kernel::program_expression::variable("p"),
                                )),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let theorem =
        prove_symbolic_program_execution(ExecutionState::new(), statement, PureFactContext::new())
            .expect("a concrete loop has one path");
    let Proposition::ProgramStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
        ),
        "reading a loop body's local after the loop is undefined behaviour, got {outcome:?}"
    );
}

/// `break` leaves the body too. An exit that skips the end of a block still
/// leaves the block, so it ends the same lifetimes falling off the end does.
#[test]
fn a_loop_bodys_local_stops_existing_on_break() {
    let body = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(2)),
            program_seq(
                program_assign("p", crate::kernel::program_expression::addr_of("x")),
                program_break(),
            ),
        ),
    );
    let statement = program_seq(
        program_declare("anchor", ProgramType::Int32),
        program_seq(
            program_assign(
                "anchor",
                crate::kernel::program_expression::int32_literal(0),
            ),
            program_seq(
                program_declare("p", ProgramType::Int32Pointer),
                program_seq(
                    program_assign("p", crate::kernel::program_expression::addr_of("anchor")),
                    program_seq(
                        program_while(
                            crate::kernel::program_expression::int32_literal(1),
                            Vec::new(),
                            body,
                        ),
                        program_return(crate::kernel::program_expression::load(
                            crate::kernel::program_expression::variable("p"),
                        )),
                    ),
                ),
            ),
        ),
    );
    let theorem =
        prove_symbolic_program_execution(ExecutionState::new(), statement, PureFactContext::new())
            .expect("the loop breaks on its first iteration");
    let Proposition::ProgramStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
        ),
        "reading a loop body's local after a `break` is undefined behaviour, got {outcome:?}"
    );
}

/// A `switch` body is one block for all of its cases, because control falls
/// from one case into the next. Leaving the switch leaves that block.
#[test]
fn a_switch_bodys_local_stops_existing_when_the_switch_is_left() {
    let case = program_seq(
        program_declare("x", ProgramType::Int32),
        program_seq(
            program_assign("x", crate::kernel::program_expression::int32_literal(4)),
            program_seq(
                program_assign("p", crate::kernel::program_expression::addr_of("x")),
                program_break(),
            ),
        ),
    );
    let statement = program_seq(
        program_declare("anchor", ProgramType::Int32),
        program_seq(
            program_assign(
                "anchor",
                crate::kernel::program_expression::int32_literal(0),
            ),
            program_seq(
                program_declare("p", ProgramType::Int32Pointer),
                program_seq(
                    program_assign("p", crate::kernel::program_expression::addr_of("anchor")),
                    program_seq(
                        program_switch(
                            crate::kernel::program_expression::int32_literal(1),
                            vec![SwitchCase {
                                value: Some(1),
                                body: Box::new(case),
                            }],
                        ),
                        program_return(crate::kernel::program_expression::load(
                            crate::kernel::program_expression::variable("p"),
                        )),
                    ),
                ),
            ),
        ),
    );
    let theorem =
        prove_symbolic_program_execution(ExecutionState::new(), statement, PureFactContext::new())
            .expect("a constant selector picks one case");
    let Proposition::ProgramStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    assert!(
        matches!(
            outcome,
            StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
        ),
        "reading a `switch` body's local after the switch is undefined behaviour, got {outcome:?}"
    );
}

/// A scope exit retires what the scope declared and nothing else: a pointer
/// to an object the enclosing block declared still designates it.
#[test]
fn an_outer_locals_address_survives_an_inner_scope() {
    let arm = program_seq(
        program_declare("x", ProgramType::Int32),
        program_assign("x", crate::kernel::program_expression::int32_literal(7)),
    );
    let statement = program_seq(
        program_declare("outer", ProgramType::Int32),
        program_seq(
            program_assign("outer", crate::kernel::program_expression::int32_literal(5)),
            program_seq(
                program_declare("p", ProgramType::Int32Pointer),
                program_seq(
                    program_assign("p", crate::kernel::program_expression::addr_of("outer")),
                    program_seq(
                        program_if(
                            crate::kernel::program_expression::variable("c"),
                            arm,
                            ProgramStatement::Skip,
                        ),
                        program_return(crate::kernel::program_expression::load(
                            crate::kernel::program_expression::variable("p"),
                        )),
                    ),
                ),
            ),
        ),
    );
    let state =
        ExecutionState::new().with_local("c", ProgramValue::Int32(MachineTerm::constant(1)));
    let theorem = prove_symbolic_program_execution(state, statement, PureFactContext::new())
        .expect("the taken arm is the only path");
    let Proposition::ProgramStatementExecutes { outcome, .. } = theorem.proposition() else {
        panic!("expected an execution: {:?}", theorem.proposition());
    };
    let StatementOutcome::Return { value, .. } = outcome else {
        panic!("expected a return: {outcome:?}");
    };
    assert_eq!(
        value.native().as_ref(),
        &ProgramValue::Int32(MachineTerm::constant(5))
    );
}

fn path_exists_at_program_point(
    ty: &AlgebraicType,
    binder: u64,
    argument: u64,
    memory: Memory,
    target: u32,
) -> Proposition {
    Proposition::Exists {
        name: "path".into(),
        var: Variable(binder),
        sort: Sort::Algebraic(ty.clone()),
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::ClickFunctionApplication {
                    name: "walk".into(),
                    arguments: vec![
                        PureFunctionArgument::ArrayRef {
                            memory,
                            pointer: ProgramValue::pointer(Pointer {
                                block: "graph".into(),
                                offset: PointerOffsetTerm::Constant(0),
                            }),
                            element_type: ProgramType::Int32,
                        },
                        PureFunctionArgument::Algebraic(AlgebraicTerm {
                            algebraic_type: ty.clone(),
                            node: AlgebraicTermNode::Variable(Variable(argument)),
                        }),
                    ],
                },
                target.into(),
            ),
            true,
        )),
    }
}

#[test]
fn certification_recognizes_only_the_same_algebraic_existential() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = AlgebraicType::parameter("Path".into());
    let before = Memory::new().with_block("graph", 4);
    let after = before.clone().store(
        Pointer {
            block: "graph".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(1),
    );
    let fact = path_exists_at_program_point(&ty, 100, 100, before.clone(), 0);
    let facts = PureFactContext::new().assume_proposition(fact);
    let proves = |goal| crate::kernel::PureFactContext::settles_exactly(&facts, &goal);
    assert!(proves(path_exists_at_program_point(
        &ty,
        200,
        200,
        before.clone(),
        0
    )));
    assert!(
        !proves(path_exists_at_program_point(&ty, 200, 200, after, 0)),
        "a changed graph is not alpha renaming"
    );
    assert!(
        !proves(path_exists_at_program_point(
            &ty,
            200,
            100,
            before.clone(),
            0
        )),
        "a free path is not the existential binder"
    );
    assert!(
        !facts.proves_atomic_without_search(&path_exists_at_program_point(
            &ty,
            200,
            100,
            before.clone(),
            0
        )),
        "the atomic existential rule must not match a free path either"
    );
    assert!(
        !proves(path_exists_at_program_point(
            &ty,
            200,
            200,
            before.clone(),
            1
        )),
        "the endpoint must match"
    );
    assert!(
        !proves(path_exists_at_program_point(
            &AlgebraicType::parameter("OtherPath".into()),
            200,
            200,
            before,
            0
        )),
        "the witness sort must match"
    );
}

#[test]
fn certification_generalization_cannot_borrow_a_preexisting_witness_id() {
    let binder = Variable(130);
    // A future freshening rule must not assume a reserved numeric range alone
    // makes its first identity absent from an arbitrary kernel fact context.
    let would_be_witness = Variable(1 << 44);
    let assumed = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(would_be_witness)),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    let goal = Proposition::ForAll {
        name: Default::default(),
        var: binder,
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(binder)),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        )),
    };
    let facts = PureFactContext::new().assume_proposition(assumed);
    assert!(!crate::kernel::PureFactContext::settles_exactly(
        &facts, &goal
    ));
}

#[test]
fn kernel_fresh_identity_cannot_be_forged_by_the_numeric_constructor() {
    let first = Variable::allocate_fresh().expect("fresh identity");
    let second = Variable::allocate_fresh().expect("another fresh identity");
    assert_ne!(first, second);
    assert_ne!(first, Variable(first.0));
}

fn conditional_path_universal(
    ty: &AlgebraicType,
    binder: u64,
    memory: Memory,
    target: u32,
) -> Proposition {
    let Proposition::Exists {
        name: _,
        var,
        sort,
        body,
    } = path_exists_at_program_point(ty, binder, binder, memory, target)
    else {
        unreachable!()
    };
    Proposition::Implies(
        Box::new(Proposition::ForAll {
            name: Default::default(),
            var: Variable(binder + 1),
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(MachineTerm::Variable(Variable(binder + 1)), 0.into()),
                true,
            )),
        }),
        Box::new(Proposition::ForAll {
            name: Default::default(),
            var,
            sort,
            body,
        }),
    )
}

#[test]
fn certification_keeps_conditional_universal_guards_states_and_sorts() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = AlgebraicType::parameter("Path".into());
    let memory = Memory::new().with_block("graph", 4);
    let fact = conditional_path_universal(&ty, 100, memory.clone(), 0);
    let proof_facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&fact));
    let facts = PureFactContext::new().assume_proposition(fact);
    let proves = |goal: &Proposition| {
        let certified = crate::kernel::PureFactContext::settles_exactly(&facts, goal);
        assert_eq!(proof_facts.pure_known_available(goal), certified);
        certified
    };
    let goal = conditional_path_universal(&ty, 200, memory.clone(), 0);
    assert!(proves(&goal));
    let Proposition::Implies(_, body) = &goal else {
        unreachable!()
    };
    assert!(
        !proves(body),
        "a conditional guarantee cannot lose its guard"
    );
    assert!(!proves(&conditional_path_universal(
        &ty,
        200,
        memory.clone(),
        1
    )));
    assert!(!proves(&conditional_path_universal(
        &AlgebraicType::parameter("OtherPath".into()),
        200,
        memory.clone(),
        0,
    )));
    let after = memory.store(
        Pointer {
            block: "graph".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(1),
    );
    assert!(!proves(&conditional_path_universal(&ty, 200, after, 0)));
}

#[test]
fn aggregate_copy_requires_write_authority_for_each_destination_field() {
    let target = Pointer {
        block: "target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let source = Pointer {
        block: "source".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let layout = AggregateLayout::new(
        8,
        4,
        vec![
            AggregateField::new("a", 0, ProgramType::Int32),
            AggregateField::new("b", 4, ProgramType::Int32),
        ],
    );
    let function = program_function(
        ProgramType::Void,
        "copy_fields",
        vec![
            program_parameter("target", ProgramType::Int32Pointer),
            program_parameter("source", ProgramType::Int32Pointer),
        ],
        program_copy_aggregate(
            crate::kernel::program_expression::variable("target"),
            crate::kernel::program_expression::variable("source"),
            layout,
        ),
    );
    for complete in [false, true] {
        let mut resources = vec![
            own_memory_fact(target.clone(), 0, 1),
            view_memory_fact(source.clone(), 0, 2),
        ];
        if complete {
            resources.push(own_memory_fact(target.clone(), 1, 2));
        }
        let theorem = prove_symbolic_program_function_execution_with_environment(
            ExecutionState::new()
                .with_resource_context(ResourceContext::new().unchecked_with_facts(resources)),
            function.clone(),
            vec![
                crate::kernel::program_expression::pointer_value(target.clone()),
                crate::kernel::program_expression::pointer_value(source.clone()),
            ],
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::EXECUTE_BODIES,
        )
        .unwrap();
        let Proposition::ProgramFunctionExecutes { outcome, .. } = theorem.proposition() else {
            panic!("expected function execution");
        };
        if complete {
            assert!(
                matches!(outcome, FunctionOutcome::Return { .. }),
                "{outcome:?}"
            );
        } else {
            assert!(
                matches!(
                    outcome,
                    FunctionOutcome::RuntimeError(RuntimeError::MissingResource { .. })
                ),
                "{outcome:?}"
            );
        }
    }
}

// Construction summaries reuse caller storage, including the result's own
// address. This exercises checked artifacts and rule application together.
#[test]
fn construction_return_contract_certifies_and_applies_to_caller_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = AggregateLayout::new(
        16,
        8,
        vec![
            AggregateField::new("self", 0, ProgramType::Int32Pointer),
            AggregateField::new("value", 8, ProgramType::Int32),
        ],
    );
    let result = crate::kernel::program_expression::variable(C_CONTRACT_RESULT_NAME);
    let field = crate::kernel::program_expression::cast(
        crate::kernel::program_expression::pointer_offset_bytes(result.clone(), 8),
        ProgramType::Int32Pointer,
    );
    let storage = MemorySegment::new(
        result.clone(),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(4),
    );
    let owner = ResourceSpec::owned_memory(storage.clone());
    let equality = |left, right| SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(left),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(right),
    };
    let function = program_function(
        ProgramType::VoidPointer,
        "constructed_node",
        vec![program_parameter("input", ProgramType::Int32)],
        program_seq(
            program_typed_store(result.clone(), field.clone(), ProgramType::Int32Pointer),
            program_seq(
                program_typed_store(
                    field.clone(),
                    crate::kernel::program_expression::variable("input"),
                    ProgramType::Int32,
                ),
                program_return(result.clone()),
            ),
        ),
    )
    .with_construction_return(layout.clone())
    .with_resource_summary(vec![owner.clone()], vec![owner])
    .with_contract(
        vec![],
        vec![
            equality(
                crate::kernel::program_expression::typed_load(result, ProgramType::Int32Pointer),
                field.clone(),
            ),
            equality(
                crate::kernel::program_expression::typed_load(field, ProgramType::Int32),
                crate::kernel::program_expression::variable("input"),
            ),
        ],
        vec![storage],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::effect(0),
            FunctionContractClaim::ensure_proposition(0, 0),
            FunctionContractClaim::ensure_proposition(1, 1),
            FunctionContractClaim::ensure_resource(2, 0),
        ],
        true,
    );
    let proof_destination = Pointer::symbolic(Variable(873_001));
    register_block_alignment(&proof_destination.block, 8);
    let proof_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_uninitialized_block(proof_destination.block.clone(), 16))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(
                proof_destination.clone(),
                0u32.into(),
                4u32.into(),
            )),
        ))
        .with_aggregate_return_destination(proof_destination, layout.clone());
    let execution = certify_contract_with_kernel_artifacts(
        proof_state.clone(),
        function.clone(),
        vec![ProgramExpression::Value(int32(MachineTerm::Variable(
            Variable(873_002),
        )))],
        vec![],
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let claims = program_verified_function_contract_claims(&function, &execution)
        .expect("construction claims should certify from generic unwritten storage");
    let rule =
        program_verified_function_rule(function.clone(), &claims).expect("construction rule");
    assert!(
        program_verified_function_rule(
            function
                .clone()
                .with_return_aggregate_layout(layout.clone()),
            &claims
        )
        .is_none()
    );
    assert!(program_external_function_rule(function.clone()).is_some());
    assert!(FunctionContract::new("ConstructionCallback", function.clone()).is_none());
    let mut environment = ExecutionEnvironment::new()
        .with_function(function.clone())
        .with_verified_function_rule(rule);
    let mut callee = "constructed_node";
    for name in ["forward_constructed_node", "outer_constructed_node"] {
        let forward = program_function(
            ProgramType::VoidPointer,
            name,
            function.parameters().to_vec(),
            program_seq(
                program_call_construct(
                    C_CONTRACT_RESULT_NAME,
                    callee,
                    vec![crate::kernel::program_expression::variable("input")],
                ),
                program_return(crate::kernel::program_expression::variable(
                    C_CONTRACT_RESULT_NAME,
                )),
            ),
        )
        .with_construction_return(layout.clone())
        .with_resource_summary(
            function.resource_requires().to_vec(),
            function.resource_ensures().to_vec(),
        )
        .with_contract(
            function.contract_requires().to_vec(),
            function.contract_ensures().to_vec(),
            function.contract_mutable().to_vec(),
            function.contract_claims().to_vec(),
            true,
        );
        let arguments = vec![ProgramExpression::Value(int32(MachineTerm::Variable(
            Variable(873_002),
        )))];
        let artifact = prove_checked_program_function_execution_with_environment(
            proof_state.clone(),
            forward.clone(),
            arguments.clone(),
            PureFactContext::new(),
            environment.clone(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
        );
        // Summary ensures are symbolic facts, so forwarding needs the same
        // checked proposition completions that a Surface proof supplies.
        let mut completions = Vec::new();
        let closing = crate::kernel::ContractClosingContext::new(&artifact);
        let mut exit_completions = Vec::new();
        for (path_index, path) in artifact.paths().iter().enumerate() {
            use crate::kernel::proof::*;
            let Proposition::ProgramFunctionVerifies { outcome, .. } =
                crate::kernel::api::proof_evidence_conclusion(path.theorem())
            else {
                panic!("forwarding must have a checked function outcome");
            };
            let FunctionOutcome::Return { value, state } = outcome else {
                panic!("forwarding must return");
            };
            let mut facts = path.assumptions().pure_facts();
            facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
            let assumptions = facts.iter().fold(PureFactContext::new(), |context, fact| {
                context.assume_proposition(fact.clone())
            });
            let core = OutcomeProofCore {
                publication: None,
                identity: OutcomeIdentity::fresh(),
                result: Arc::new(value.clone().into_native()),
                store_consequences_available: true,
                state: state.as_ref().clone().into(),
                is_exceptional: false,
                effect_facts: path.facts().clone().into(),
            };
            let owned = crate::kernel::CheckedPathSpecification::new(&forward, path)
                .expect("forwarded path specification");
            let closing_facts = ProofFacts::from_ordered(&facts);
            let claim_goals = OutcomeClaimGoals::open([], false);
            let mut goals = closing.open(path_index, &core);
            while let Some(kind) = goals.first_open_goal() {
                goals = goals
                    .prove_goal_for_specification(
                        kind,
                        &artifact,
                        path,
                        owned.specification(),
                        &core,
                        &claim_goals,
                        &closing_facts,
                    )
                    .expect("forwarded resource and effect obligation");
            }
            let completion = goals
                .completion(path)
                .expect("all forwarding goals are closed");
            exit_completions.push(completion);
            for index in 0..2 {
                let goals = program_function_ensure_goals(
                    &forward,
                    index,
                    &proof_state,
                    &arguments,
                    outcome,
                    &assumptions,
                    &[],
                )
                .expect("forwarded ensure goals");
                assert_eq!(goals.len(), 1);
                let goal = &goals[0];
                let mut goal_facts = facts.clone();
                goal_facts.extend_from_slice(goal.facts());
                let outcome = Arc::new(OutcomeProofState::new(
                    OutcomeProofCore {
                        publication: None,
                        identity: OutcomeIdentity::fresh(),
                        result: Arc::new(value.clone().into_native()),
                        store_consequences_available: true,
                        state: state.as_ref().clone().into(),
                        is_exceptional: false,
                        effect_facts: path.facts().clone().into(),
                    },
                    (),
                ));
                let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
                    ProofObject::root(
                        (),
                        ProofBranch::new(
                            ProofObligation::FunctionOutcome(FunctionOutcomeObligation::new(
                                0, outcome,
                            )),
                            ProofBranchState {
                                facts: ProofFacts::from_ordered(&goal_facts),
                                unfolded_predicates: PersistentOrderedSet::default(),
                                execution: None,
                            },
                        ),
                    );
                let proof = proof
                    .focus_contract_claim(goal, ())
                    .expect("forwarded claim requirements");
                let closed = proof
                    .apply_known(PropositionKnownContext::Exact)
                    .unwrap_or_else(|_| {
                        panic!("forwarded ensure {index} must follow from the call")
                    });
                let owned =
                    crate::kernel::api::contract_certification::CheckedPathSpecification::new(
                        &forward, path,
                    )
                    .expect("forwarded path specification");
                completions.push(
                    owned
                        .complete(
                            &closed.completed_proposition().expect("closed ensure"),
                            path,
                        )
                        .expect("checked forwarded ensure"),
                );
            }
        }
        let artifact = artifact
            .with_closed_exit_obligations(exit_completions)
            .expect("forwarded exit completions");
        let execution = prove_program_function_contract_execution_paths_with_checked_artifacts(
            proof_state.clone(),
            forward.clone(),
            arguments,
            environment.clone(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
            &[artifact],
        );
        let claims =
            program_function_contract_claims_from_completions(&forward, &execution, &completions)
                .unwrap_or_else(|| panic!("forwarded construction claims for {name}"));
        let rule = program_verified_function_rule(forward.clone(), &claims)
            .expect("forwarded construction rule");
        environment = environment
            .with_function(forward)
            .with_verified_function_rule(rule);
        callee = name;
    }
    let paths = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new().with_population_creation_tracking(),
        program_seq(
            program_allocate_aggregate_destination("node", layout),
            program_seq(
                program_call_construct(
                    "node",
                    "outer_constructed_node",
                    vec![crate::kernel::program_expression::int32_literal(37)],
                ),
                program_return(crate::kernel::program_expression::typed_load(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable("node"),
                        8,
                    ),
                    ProgramType::Int32,
                )),
            ),
        ),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(paths.paths().len(), 1);
    let path = &paths.paths()[0];
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Return { value, state },
        ..
    } = crate::kernel::api::proof_evidence_conclusion(path.theorem())
    else {
        panic!(
            "constructed result must be readable: {:?}",
            crate::kernel::api::proof_evidence_conclusion(path.theorem())
        );
    };
    let at = state.locals().aggregate_object_pointer("node").unwrap();
    assert!(state.memory().has_initialized_bytes_at(at, 8));
    assert!(
        !state.memory().has_initialized_bytes_at(at, 16),
        "padding is not a constructed value field"
    );
    assert!(
        state
            .memory()
            .has_initialized_bytes_at(&at.offset_by_bytes(8), 4)
    );
    let assumptions = path
        .facts()
        .iter()
        .fold(PureFactContext::new(), |context, fact| {
            context.assume_proposition(fact.proposition().clone())
        });
    let ProgramValue::Int32(value) = value.clone().into_native() else {
        panic!("constructed int32 field");
    };
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(ConditionTerm::equal(value.clone(), 37u32.into()), true,)
    ));
    let loads = evaluate_program_expression_paths(
        state,
        &crate::kernel::program_expression::typed_load(
            crate::kernel::program_expression::variable("node"),
            ProgramType::Int32Pointer,
        ),
        &assumptions,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let [load] = loads.as_slice() else {
        panic!("one self-pointer load");
    };
    let ExpressionOutcome::Value(ProgramValue::Pointer(self_pointer)) = &load.outcome else {
        panic!("constructed self-pointer should be readable");
    };
    let assumptions = load.facts.iter().fold(assumptions, |context, fact| {
        context.assume_proposition(fact.proposition().clone())
    });
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::pointer_equal(self_pointer.pointer().clone(), at.offset_by_bytes(8)),
            true,
        )
    ));
}

// A modular ordinary-parameter constructor must establish initialization from
// its checked body, without manufacturing values for unwritten padding.
#[test]
fn construction_parameter_summary_initializes_only_checked_fields() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = AggregateLayout::new(
        16,
        8,
        vec![
            AggregateField::new("self", 0, ProgramType::Int32Pointer),
            AggregateField::new("value", 8, ProgramType::Int32),
        ],
    );
    let destination = crate::kernel::program_expression::variable("destination");
    let field = crate::kernel::program_expression::cast(
        crate::kernel::program_expression::pointer_offset_bytes(destination.clone(), 8),
        ProgramType::Int32Pointer,
    );
    let storage = MemorySegment::new(
        destination.clone(),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(4),
    );
    let owner = ResourceSpec::owned_memory(storage.clone());
    let function = program_function(
        ProgramType::Void,
        "construct_parameter",
        vec![
            program_parameter("destination", ProgramType::Int32Pointer),
            program_parameter("input", ProgramType::Int32),
        ],
        program_seq(
            program_typed_store(destination, field.clone(), ProgramType::Int32Pointer),
            program_seq(
                program_typed_store(
                    field,
                    crate::kernel::program_expression::variable("input"),
                    ProgramType::Int32,
                ),
                program_return(program_void_value()),
            ),
        ),
    )
    .with_construction_parameter(0, layout.clone())
    .with_resource_summary(vec![owner.clone()], vec![owner])
    .with_contract(
        vec![],
        vec![],
        vec![storage],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::effect(0),
            FunctionContractClaim::ensure_resource(0, 0),
        ],
        true,
    );
    let at = Pointer::symbolic(Variable(873_011));
    register_block_alignment(&at.block, 8);
    let entry = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_uninitialized_block(at.block.clone(), 16))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(at.clone(), 0u32.into(), 4u32.into())),
        ));
    let execution = certify_contract_with_kernel_artifacts(
        entry.clone(),
        function.clone(),
        vec![
            crate::kernel::program_expression::pointer_value(at.clone()),
            ProgramExpression::Value(int32(MachineTerm::Variable(Variable(873_012)))),
        ],
        vec![],
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let claims = program_verified_function_contract_claims(&function, &execution)
        .expect("constructor claims");
    let rule = program_verified_function_rule(function.clone(), &claims).expect("constructor rule");
    assert!(program_external_function_rule(function.clone()).is_none());
    assert!(FunctionContract::new("ConstructorCallback", function.clone()).is_none());
    assert!(
        program_verified_function_rule(
            function
                .clone()
                .with_construction_parameter(1, layout.clone()),
            &claims
        )
        .is_none()
    );
    let environment = ExecutionEnvironment::new()
        .with_function(function)
        .with_verified_function_rule(rule);
    // A returned-construction factory uses the same ordinary constructor
    // summary while retaining its own hidden destination across the void call.
    let result = crate::kernel::program_expression::variable(C_CONTRACT_RESULT_NAME);
    let storage = MemorySegment::new(
        result.clone(),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(4),
    );
    let owner = ResourceSpec::owned_memory(storage.clone());
    let factory = program_function(
        ProgramType::VoidPointer,
        "parameter_factory",
        vec![program_parameter("input", ProgramType::Int32)],
        program_seq(
            program_call(
                "construct_parameter",
                vec![
                    crate::kernel::program_expression::cast(
                        result.clone(),
                        ProgramType::Int32Pointer,
                    ),
                    crate::kernel::program_expression::variable("input"),
                ],
            ),
            program_return(result),
        ),
    )
    .with_construction_return(layout.clone())
    .with_resource_summary(vec![owner.clone()], vec![owner])
    .with_contract(
        vec![],
        vec![],
        vec![storage],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::effect(0),
            FunctionContractClaim::ensure_resource(0, 0),
        ],
        true,
    );
    let execution = certify_contract_with_kernel_artifacts(
        entry.with_aggregate_return_destination(at, layout.clone()),
        factory.clone(),
        vec![ProgramExpression::Value(int32(MachineTerm::Variable(
            Variable(873_012),
        )))],
        vec![],
        environment.clone(),
        ExecutionSemantics::APPLY_VERIFIED_RULES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let claims = program_verified_function_contract_claims(&factory, &execution)
        .expect("factory calling ordinary constructor");
    let rule = program_verified_function_rule(factory.clone(), &claims).expect("factory rule");
    let environment = environment
        .with_function(factory)
        .with_verified_function_rule(rule);
    let paths = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new().with_population_creation_tracking(),
        program_seq(
            program_allocate_aggregate_destination("node", layout),
            program_seq(
                program_call_construct(
                    "node",
                    "parameter_factory",
                    vec![crate::kernel::program_expression::int32_literal(37)],
                ),
                program_return(crate::kernel::program_expression::typed_load(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable("node"),
                        8,
                    ),
                    ProgramType::Int32,
                )),
            ),
        ),
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let [path] = paths.paths() else {
        panic!("one constructor summary path");
    };
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Return { state, .. },
        ..
    } = crate::kernel::api::proof_evidence_conclusion(path.theorem())
    else {
        let conclusion = crate::kernel::api::proof_evidence_conclusion(path.theorem());
        match conclusion {
            Proposition::ProgramStatementVerifies { outcome, .. }
            | Proposition::ProgramStatementExecutes { outcome, .. } => match outcome {
                StatementOutcome::RuntimeError(error) => panic!("constructor summary: {error:?}"),
                StatementOutcome::UndefinedBehavior(error) => {
                    panic!("constructor summary: {error:?}")
                }
                _ => panic!("unexpected constructor summary outcome"),
            },
            _ => panic!("unexpected constructor summary theorem"),
        }
    };
    let at = state.locals().aggregate_object_pointer("node").unwrap();
    assert!(state.memory().has_initialized_bytes_at(at, 8));
    assert!(
        state
            .memory()
            .has_initialized_bytes_at(&at.offset_by_bytes(8), 4)
    );
    assert!(!state.memory().has_initialized_bytes_at(at, 16));
}

// An embedded constructor initializes its own footprint without shrinking its
// parent's allocation or initializing a sibling. Its proof entry describes
// only that footprint, so it does not assume a complete allocation of that size.
#[test]
fn subobject_constructor_summary_preserves_parent_extent_and_siblings() {
    let _session = crate::kernel::VerificationSession::enter();
    let child = AggregateLayout::new(
        8,
        8,
        vec![AggregateField::new("size", 0, ProgramType::UInt64)],
    );
    let parent = AggregateLayout::new(
        16,
        8,
        vec![
            AggregateField::new("data", 0, ProgramType::Int32Pointer),
            AggregateField::new("extent.size", 8, ProgramType::UInt64),
        ],
    );
    let storage = MemorySegment::new(
        crate::kernel::program_expression::variable("destination"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(2),
    );
    let owner = ResourceSpec::owned_memory(storage.clone());
    let function = program_function(
        ProgramType::Void,
        "construct_extent",
        vec![
            program_parameter("destination", ProgramType::Int32Pointer),
            program_parameter("input", ProgramType::UInt64),
        ],
        program_seq(
            program_typed_store(
                crate::kernel::program_expression::variable("destination"),
                crate::kernel::program_expression::variable("input"),
                ProgramType::UInt64,
            ),
            program_return(program_void_value()),
        ),
    )
    .with_construction_parameter(0, child)
    .with_resource_summary(vec![owner.clone()], vec![owner])
    .with_contract(
        vec![],
        vec![],
        vec![storage],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::effect(0),
            FunctionContractClaim::ensure_resource(0, 0),
        ],
        true,
    );
    let at = Pointer::symbolic(Variable(873_021));
    register_block_alignment(&at.block, 8);
    let memory = Memory::new().with_uninitialized_object(at.clone(), 8);
    assert!(memory.block_size(&at.block).is_none());
    let live = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: at.clone(),
        bytes: 8u32.into(),
        wide: false,
    };
    let entry = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(at.clone(), 0u32.into(), 2u32.into())),
        ));
    let execution = certify_contract_with_kernel_artifacts(
        entry,
        function.clone(),
        vec![
            crate::kernel::program_expression::pointer_value(at),
            ProgramExpression::Value(uint64(MachineTerm::Variable(Variable(873_022)))),
        ],
        vec![live],
        ExecutionEnvironment::new(),
        ExecutionSemantics::EXECUTE_BODIES,
        FunctionContractExecutionMode::VerifyLoops,
    );
    let claims = program_verified_function_contract_claims(&function, &execution)
        .expect("object-footprint constructor proof");
    let rule = program_verified_function_rule(function.clone(), &claims)
        .expect("subobject constructor rule");
    let environment = ExecutionEnvironment::new()
        .with_function(function)
        .with_verified_function_rule(rule);
    for offset in [8, 4, 16] {
        let paths = prove_symbolic_program_execution_paths_with_environment(
            ExecutionState::new().with_population_creation_tracking(),
            program_seq(
                program_allocate_aggregate_destination("parent", parent.clone()),
                program_seq(
                    program_call(
                        "construct_extent",
                        vec![
                            crate::kernel::program_expression::cast(
                                crate::kernel::program_expression::pointer_offset_bytes(
                                    crate::kernel::program_expression::variable("parent"),
                                    offset,
                                ),
                                ProgramType::Int32Pointer,
                            ),
                            crate::kernel::program_expression::uint64_literal(37),
                        ],
                    ),
                    program_return(crate::kernel::program_expression::typed_load(
                        crate::kernel::program_expression::pointer_offset_bytes(
                            crate::kernel::program_expression::variable("parent"),
                            8,
                        ),
                        ProgramType::UInt64,
                    )),
                ),
            ),
            PureFactContext::new(),
            environment.clone(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
        );
        let [path] = paths.paths() else {
            panic!("one subobject call outcome");
        };
        let Proposition::ProgramStatementVerifies { outcome, .. } =
            crate::kernel::api::proof_evidence_conclusion(path.theorem())
        else {
            panic!("checked subobject execution");
        };
        if offset != 8 {
            assert!(
                matches!(outcome, StatementOutcome::RuntimeError(_)),
                "misaligned or out-of-bounds child must be refused"
            );
            continue;
        }
        let StatementOutcome::Return { state, .. } = outcome else {
            match outcome {
                StatementOutcome::RuntimeError(error) => {
                    panic!("subobject constructor: {error:?}")
                }
                StatementOutcome::UndefinedBehavior(error) => {
                    panic!("subobject constructor: {error:?}")
                }
                _ => panic!("subobject constructor must return"),
            }
        };
        let base = state.locals().aggregate_object_pointer("parent").unwrap();
        assert_eq!(state.memory().block_size(&base.block), Some(&16u32.into()));
        assert!(
            state
                .memory()
                .has_initialized_bytes_at(&base.offset_by_bytes(8), 8)
        );
        assert!(
            !state.memory().has_initialized_bytes_at(base, 8),
            "sibling remains unwritten"
        );
    }
}

// Allocation grants only its exact byte extent, never initialization; taking
// that owner away must block both named and pointer-mediated local accesses.
#[test]
fn automatic_scalar_ownership_is_exact_and_required_for_all_accesses() {
    let assumptions = PureFactContext::new();
    let paths = execute_execution_statement_paths(
        &ExecutionState::new(),
        &program_declare("word", ProgramType::UInt32),
        &assumptions,
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let StatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("scalar declaration");
    };
    let state = state.as_ref().clone();
    let pointer = Memory::local_pointer("word");
    let owner = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        pointer.clone(),
        0.into(),
        4.into(),
        1,
    ));
    assert!(state.resources().satisfies_fact(&owner, &assumptions));
    assert!(!state.memory().has_initialized_bytes_at(&pointer, 4));
    assert!(!state.resources().satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new_with_element_width(
            pointer.clone(),
            0.into(),
            5.into(),
            1
        )),
        &assumptions
    ));
    let initialized = state.clone().with_local("word", uint32(7));
    let empty = initialized.with_resource_context(ResourceContext::new());
    for expression in [
        crate::kernel::program_expression::variable("word"),
        crate::kernel::program_expression::typed_load(
            crate::kernel::program_expression::addr_of("word"),
            ProgramType::UInt32,
        ),
    ] {
        let paths = evaluate_program_expression_paths(
            &empty,
            &expression,
            &assumptions,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert!(matches!(
            &paths[0].outcome,
            ExpressionOutcome::RuntimeError(RuntimeError::MissingResource { .. })
        ));
    }
    for statement in [
        program_assign("word", crate::kernel::program_expression::uint32_literal(9)),
        program_typed_store(
            crate::kernel::program_expression::addr_of("word"),
            crate::kernel::program_expression::uint32_literal(9),
            ProgramType::UInt32,
        ),
    ] {
        let paths = execute_execution_statement_paths(
            &empty,
            &statement,
            &assumptions,
            ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert!(matches!(
            &paths[0].outcome,
            StatementOutcome::RuntimeError(RuntimeError::MissingResource { .. })
        ));
    }
    let retired =
        crate::kernel::eval::end_scope_automatic_lifetimes(&state, &["word".into()]).unwrap();
    assert!(!retired.resources().satisfies_fact(&owner, &assumptions));
    assert!(retired.memory().is_ended_local_address(&pointer));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/contract_execution_tests.rs");
}

/// A contract that `produces` a composite from pieces publishes the body's
/// facts with it. Certification assembles the composite from the exit's
/// pieces only when each body fact holds there; a C store that falsified a
/// fact leaves the claim uncertified, and the same store of the stated value
/// certifies it (`bugs/` regression: an ordinary exit produced a composite
/// without its body facts).
#[test]
fn a_produced_composite_is_certified_only_when_the_exit_establishes_its_body_facts() {
    let pointer = Pointer {
        block: "produced-composite-cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let cell = || {
        crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
        )
    };
    let definition = CompositeResourceDefinition::new(
        "zero_cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(cell()),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
    );
    let certified = |stored: u32| {
        let function = program_function(
            ProgramType::Void,
            "produce_zero_cell",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            program_seq(
                program_store(
                    crate::kernel::program_expression::variable("p"),
                    crate::kernel::program_expression::int32_literal(stored),
                ),
                program_return(program_void_value()),
            ),
        )
        .with_resource_summary(
            vec![ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(1),
            ))],
            vec![ResourceSpec::composite(
                ResourceAccessMode::Own,
                "zero_cell".into(),
                vec![crate::kernel::program_expression::variable("p")],
                vec![ProgramType::Int32Pointer],
            )],
        )
        .with_composite_resource_definitions(vec![definition.clone()])
        .with_contract(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![FunctionContractClaim::ensure_resource(0, 0)],
            true,
        );
        let state = ExecutionState::new()
            .with_memory(
                Memory::new()
                    .with_block(pointer.block.clone(), 4)
                    .store(pointer.clone(), int32(7)),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new(pointer.clone(), 0.into(), 1.into())),
            ));
        let arguments = vec![crate::kernel::program_expression::pointer_value(
            pointer.clone(),
        )];
        let execution = certify_contract_with_kernel_artifacts(
            state.clone(),
            function.clone(),
            arguments.clone(),
            Vec::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::EXECUTE_BODIES,
            FunctionContractExecutionMode::VerifyLoops,
        );
        let claims = program_unverified_function_contract_claims(&function, &execution)
            .expect("the exit frontier is available to claims");
        // The kernel's exit transition is the publication the Surface reads
        // a produced resource through; it must refuse exactly when
        // certification does.
        let path = &execution.cases()[0][0].paths[0];
        let mut proposition = path.theorem.proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        let (Proposition::ProgramFunctionExecutes {
            state: caller_state,
            outcome,
            ..
        }
        | Proposition::ProgramFunctionVerifies {
            state: caller_state,
            outcome,
            ..
        }) = proposition
        else {
            panic!("a contract path concludes a function execution: {proposition:?}");
        };
        let transition = crate::kernel::api::checked_program_function_contract_resource_transition(
            caller_state,
            &function,
            &arguments,
            outcome.clone(),
            &path.assumptions,
        );
        assert_eq!(claims.is_empty(), transition.is_ok(), "{transition:?}");
        claims.is_empty()
    };
    assert!(
        !certified(9),
        "a store of 9 falsifies `p[0] == 0`: the composite must not be produced"
    );
    assert!(certified(0), "a store of 0 establishes the body fact");
}

/// A proof issues a theorem per path and claim, and each carries the
/// function and its specification, so cloning them shares the contract and
/// the specification's argument and requirement lists rather than copying
/// lists that span every parameter once per claim (roadmap/scaling.md,
/// cause 8).
#[test]
fn cloned_functions_and_specifications_share_their_contracts() {
    let parameters = (0..8)
        .map(|index| program_parameter(format!("p{index}"), ProgramType::Int32Pointer))
        .collect::<Vec<_>>();
    let function = program_function(
        ProgramType::Int32,
        "wide",
        parameters,
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let copy = function.clone();
    assert!(Arc::ptr_eq(
        &function.contract_interface,
        &copy.contract_interface
    ));

    let specification = program_function_specification(
        ExecutionState::new(),
        (0..8)
            .map(|index| ProgramExpression::Value(int32(index)))
            .collect(),
        vec![Proposition::ConditionIs(ConditionTerm::Constant(true), true); 8],
        FunctionOutcome::Return {
            value: int32(0).into(),
            state: Box::new(ExecutionState::new()),
        },
    );
    let copy = specification.clone();
    assert!(Arc::ptr_eq(&specification.arguments, &copy.arguments));
    assert!(Arc::ptr_eq(&specification.requires, &copy.requires));
}
