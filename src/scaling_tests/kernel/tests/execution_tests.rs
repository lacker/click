// Scaling tests of `src/kernel/tests/execution_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn direct_local_write_builds_borrow_obligation_without_visiting_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let execute =
        |state: &ExecutionState, statement: &ProgramStatement, assumptions: &PureFactContext| {
            execute_execution_statement_paths(
                state,
                statement,
                assumptions,
                ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        };
    let state = normal_state(&execute(
        &ExecutionState::new(),
        &program_declare("x", ProgramType::Int32),
        &PureFactContext::new(),
    ));
    let slot = state.locals().slot("x").unwrap().clone();
    let borrow = active_memory_borrow(MemoryRange::new(
        Address::symbolic(Variable(930_000)),
        0u32.into(),
        1u32.into(),
    ));
    let state = state.with_borrow_ledger(Some(borrow));
    let write = program_assign("x", crate::kernel::program_expression::int32_literal(1));

    let mut samples = Vec::new();
    for count in [4, 16, 64] {
        let mut assumptions = PureFactContext::new();
        for i in 0..count {
            assumptions = assumptions.assume_condition(
                OldConditionTerm::address_equal(
                    slot.clone(),
                    Address::symbolic(Variable(931_000 + i)),
                ),
                true,
            );
        }
        // The proof boundary publishes admitted equalities for ownership
        // queries before the step. Measure the write against that snapshot.
        state
            .resources()
            .synchronize_memory_equalities(&assumptions);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute(&state, &write, &assumptions)
        });
        assert_eq!(paths.len(), 1);
        borrow_write_separation(&paths[0]);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

/// Selecting a verified loop rule reads each required assumption through an
/// indexed lookup, so the work is charged to the rule's own prerequisites and
/// does not grow with the unrelated ambient facts in scope at the loop.
#[test]
fn verified_loop_rule_selection_is_flat_in_unrelated_ambient_facts() {
    let (statement, base_rule) = prerequisite_loop_rule_fixture();
    let state = ExecutionState::new().with_local("i", int32(0));
    let guard = loop_rule_guard(1);
    let mut applicable = base_rule.clone();
    applicable.required_assumptions = PureFactContext::new().assume_condition(guard.clone(), true);
    let mut inapplicable = base_rule;
    inapplicable.required_assumptions =
        PureFactContext::new().assume_condition(loop_rule_guard(2), true);
    // The inapplicable rule comes first, so every lookup rejects one rule's
    // prerequisite and accepts the other's.
    let environment =
        ExecutionEnvironment::new().with_verified_loop_rules([inapplicable, applicable]);

    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_condition(guard.clone(), true);
        for index in 0..size as u32 {
            assumptions = assumptions.assume_condition(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(u64::from(500_000 + index))),
                    OldMachineTerm::constant(index),
                ),
                true,
            );
        }
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            environment
                .applicable_verified_loop_rule(&state, &statement, &assumptions)
                .is_some()
        });
        assert!(selected, "the applicable rule should still be selected");
        assert_eq!(assumptions.pure_facts().len(), size + 1);
        assert!(
            work < 64,
            "selection work must stay bounded by the rules' own prerequisites: {work}"
        );
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 16, "{samples:?}");
    }
}

// The back-edge closer must extend its checked assumptions once per member,
// rather than rebuilding the growing guard prefix for every declaration.
#[test]
fn invariant_back_edge_context_extension_scales_with_members_not_ambient_facts() {
    let state =
        ExecutionState::new().with_local("i", int32(OldMachineTerm::Variable(Variable(912_346))));
    let mut samples = Vec::new();
    for size in [8usize, 16, 32] {
        let checks = (0..size)
            .map(|index| {
                LoopInvariantCheck::new(
                    SpecProposition::Comparison {
                        left: SpecExpression::ProgramExpression(
                            crate::kernel::program_expression::variable("i"),
                        ),
                        operator: ComparisonOperator::LessEqual,
                        right: SpecExpression::Value(int32(1000 + index as u32)),
                    },
                    None,
                    Some(format!("member {index}")),
                )
            })
            .collect::<Vec<_>>();
        let mut ambient_samples = Vec::new();
        for ambient in [0usize, 128, 512] {
            // Keep term-bridge imports cold at every sample size.
            crate::kernel::clear_machine_observation_memo();
            let mut assumptions = PureFactContext::new();
            for index in 0..ambient {
                assumptions = assumptions.assume_proposition(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                });
            }
            let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
            let (goals, work) = crate::instrumentation::measure_deterministic_work(|| {
                loop_invariant_obligations_at_back_edge(
                    &state,
                    &state,
                    &checks,
                    &IntegerTerm::var(Variable(9_999)),
                    &assumptions,
                )
                .expect("all explicit members lower")
            });
            let entries = crate::kernel::reasoning::path_facts::context_rebuild_entries() - before;
            assert_eq!(goals.len(), size);
            assert!(
                entries <= 4 * size,
                "{size} members rebuilt {entries} entries"
            );
            assert!(goals.iter().enumerate().all(|(index, goal)| goal.context()
                == Some(format!("member {index}").as_str())
                && goal.introductions().is_some()));
            ambient_samples.push((entries, work));
        }
        assert!(
            ambient_samples.windows(2).all(|pair| pair[0] == pair[1]),
            "ambient facts changed closer work: {ambient_samples:?}"
        );
        samples.push(ambient_samples[0]);
    }
    for pair in samples.windows(2) {
        assert!(pair[1].0 <= 2 * pair[0].0 + 8, "{samples:?}");
        // The generated certificate explicitly contains its guard prefixes;
        // context insertion itself stays linear in the declared members.
        assert!(pair[1].1 <= 5 * pair[0].1 + 64, "{samples:?}");
    }
}

/// A zero-filled automatic array's declaration, a load of a written field,
/// of a zero one, and a store then a load, cost the same whatever the
/// array's length, and every load is exact. The declaration used to store
/// every field of every element.
#[test]
fn a_zero_filled_automatic_array_costs_the_same_whatever_its_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let statement = zero_filled_node_array(length, &[(20, int32(7), ProgramType::Int32)]);
        let (state, declaration_work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_declaration(&ExecutionState::new(), &statement)
        });
        let last = 16 * (length - 1);
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            let stored = execute_declaration(
                &state,
                &program_typed_store(
                    crate::kernel::program_expression::pointer_offset_bytes(
                        crate::kernel::program_expression::variable("items"),
                        last,
                    ),
                    crate::kernel::program_expression::int32_literal(9),
                    ProgramType::Int32,
                ),
            );
            [
                load_items_field(&state, 20, ProgramType::Int32),
                load_items_field(&state, last, ProgramType::Int32),
                load_items_field(&state, last + 4, ProgramType::UInt8),
                load_items_field(&stored, last, ProgramType::Int32),
                load_items_field(&stored, last - 16, ProgramType::Int32),
            ]
        });
        let value = ExpressionOutcome::Value;
        assert_eq!(
            loads,
            [
                value(int32(7)),
                value(int32(0)),
                value(uint8(0)),
                value(int32(9)),
                value(int32(0)),
            ],
            "[{length}] reads its initializer"
        );
        (
            length,
            declaration_work,
            load_work,
            state.memory().cells.representation_len(),
        )
    });
    let (_, declaration_work, load_work, entries) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3) == (declaration_work, load_work, entries)),
        "a zero-filled declaration's cost depends on the array's length (length, declaration \
         work, load work, cell entries): {samples:?}"
    );
}

/// A statement theorem names its own path facts and obligations, not the
/// context it executed under: that context is recorded beside it. Copying
/// every context fact into the theorem as a premise made each step clone the
/// path's whole context and the recorder look each one up again
/// (`roadmap/scaling.md` cause 4), so the theorem's size must not grow with
/// unrelated facts in scope.
#[test]
fn statement_theorems_do_not_list_the_context_they_executed_under() {
    let state = ExecutionState::new().with_local("i", int32(0));
    let statement = program_assign(
        "i",
        crate::kernel::program_expression::add(
            crate::kernel::program_expression::variable("i"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    );
    let mut premise_counts = Vec::new();
    for size in [16u32, 64, 256] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(1_910_000 + u64::from(index))),
                    OldMachineTerm::constant(index),
                ),
                true,
            );
        }
        let execution = prove_symbolic_execution_statement_verification_paths_with_environment(
            state.clone(),
            statement.clone(),
            assumptions,
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        );
        let path = &execution.paths()[0];
        let mut premises = 0;
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            premises += 1;
            proposition = body;
        }
        assert!(matches!(
            proposition,
            Proposition::ProgramStatementVerifies { .. }
        ));
        premise_counts.push(premises);
    }
    assert!(
        premise_counts.windows(2).all(|pair| pair[0] == pair[1]),
        "a statement theorem lists its context: {premise_counts:?}"
    );
}

#[test]
fn const_array_construction_scales_with_written_elements_and_keeps_omitted_cells_compact() {
    let measure = |length, written, unrelated| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut state = ExecutionState::new();
        for index in 0..unrelated {
            state = execute_declaration(
                &state,
                &crate::kernel::program_declare(format!("unrelated_{index}"), ProgramType::Int32),
            );
        }
        let fill = ZeroFill::new(
            4,
            length,
            vec![ZeroCell::new(0, ProgramType::Int32, false, int32(0))],
        )
        .with_written_elements(
            (0..written)
                .map(|index| {
                    (
                        index,
                        crate::kernel::program_expression::int32_literal(index + 1),
                    )
                })
                .collect(),
        );
        let declaration = program_declare_with_zero_fill(
            "values",
            ProgramType::Int32Array(length),
            false,
            false,
            true,
            false,
            Some(fill),
        );
        let (state, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_declaration(&state, &declaration)
        });
        let slot = state.locals.slot("values").unwrap();
        assert!(state.memory().is_read_only_block(&slot.base));
        assert_eq!(
            state
                .memory()
                .load(&slot.offset_by_bytes(4 * (written - 1))),
            ExpressionOutcome::Value(int32(written))
        );
        assert_eq!(
            state.memory().load(&slot.offset_by_bytes(4 * (length - 1))),
            ExpressionOutcome::Value(int32(0))
        );
        assert_eq!(
            state.memory().cells.runs_in_block(&slot.base).count(),
            written as usize + 1
        );
        work
    };
    let small = [4, 1024, 1_000_000].map(|length| measure(length, 2, 0));
    assert!(small.iter().all(|work| *work <= small[0] + 16), "{small:?}");
    let unrelated = [0, 32, 128].map(|count| measure(1000, 2, count));
    assert!(
        unrelated.iter().all(|work| *work <= unrelated[0] + 32),
        "{unrelated:?}"
    );
    let written = [4, 16, 64].map(|count| measure(1000, count, 0));
    assert!(written[2] <= 4 * written[1] + 32, "{written:?}");
    eprintln!(
        "const-array declaration work (bounds, unrelated, written): {small:?}, {unrelated:?}, {written:?}"
    );
}

#[test]
fn loop_freshness_ignores_unrelated_live_state() {
    use crate::instrumentation::{VerificationEvent, collect};
    use crate::kernel::program_expression::{int32_literal, less_than, variable};

    let _session = crate::kernel::VerificationSession::enter();
    let condition = less_than(variable("i"), int32_literal(1));
    let body = program_assign("i", int32_literal(1));
    let statement = program_while_with_invariant_checks(
        condition.clone(),
        Vec::new(),
        Vec::new(),
        body.clone(),
    );
    let assumptions = PureFactContext::new();
    let base = ExecutionBudget::KERNEL_VARIABLE_BASE;

    for grow_owners in [false, true] {
        for size in [4, 16, 64, 128] {
            let mut state = ExecutionState::new().with_local("i", int32(0));
            if grow_owners {
                state = state.with_resource_context(ResourceContext::new().unchecked_with_facts(
                    (0..size).map(|index| {
                        ResourceFact::own(Resource::Memory(MemoryRange::new(
                            Address::symbolic(Variable(base + index)),
                            0u32.into(),
                            1u32.into(),
                        )))
                    }),
                ));
            } else {
                for index in 0..size {
                    state = state.with_local(
                        format!("unrelated_{index}"),
                        int32(OldMachineTerm::Variable(Variable(base + index))),
                    );
                }
            }
            state.prepare_execution_variable_reservations();
            // Change a single binding after warming the roots, as ordinary
            // execution does between loop checks.
            state = state.with_local("i", int32(1));
            let ((head, (exit, rule)), events) = collect(|| {
                let head = crate::kernel::api::loop_phase_preservation_contexts(
                    &state,
                    Some(&condition),
                    &[],
                    &[],
                    &[],
                    &[],
                    &body,
                    &assumptions,
                    size,
                )
                .expect("preservation context");
                let mut budget = ExecutionBudget::continuing_from(head[0].next_kernel_variable());
                let exit =
                    crate::kernel::api::prove_symbolic_loop_exit_with_proven_phases_using_budget(
                        state,
                        statement.clone(),
                        assumptions.clone(),
                        ExecutionEnvironment::new(),
                        true,
                        true,
                        Vec::new(),
                        Vec::new(),
                        Vec::new(),
                        &[],
                        None,
                        None,
                        &mut budget,
                    );
                (head, exit)
            });
            assert_eq!(
                head[0].iterations(),
                &IntegerTerm::var(Variable(base + size))
            );
            assert!(!exit.paths().is_empty());
            assert!(rule.is_some());
            let reservations = events
                .iter()
                .filter_map(|event| match event {
                    VerificationEvent::OperationFinished { name, work, .. }
                        if name == "loop entry state reservation"
                            || name == "statement state reservation" =>
                    {
                        Some((name.as_str(), *work))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            eprintln!("loop reservation owners={grow_owners} size={size}: {reservations:?}");
            assert_eq!(
                reservations,
                [
                    ("loop entry state reservation", 1),
                    ("statement state reservation", 0)
                ]
            );
        }
    }
}
