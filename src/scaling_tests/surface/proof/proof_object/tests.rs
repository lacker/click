// Scaling tests of `src/surface/proof/proof_object/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::binary_node;
use crate::kernel::{MachineCastSpelling, MachineTerm};

#[test]
fn a_missing_premise_spelling_walks_recorded_history_only_once() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let visible = MachineTerm::Variable(Variable(8_179_800));
    let state = ExecutionState::new().with_local("visible", ProgramValue::Int32(visible.clone()));
    let equal_zero = |term| {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(term),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        )
    };
    let missing = equal_zero(MachineTerm::Variable(Variable(8_179_801)));
    let named = equal_zero(visible);
    let facts = [missing.clone(), named.clone()];
    let surfaces = SurfacePropositionMap::default();
    for size in [4usize, 16, 64] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                state.clone(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(size - 1),
            kind: ProgramPointKind::Entry,
        };
        let root = Proof::for_fixed_state_goal_with_requirements(
            "missing premise spelling",
            0,
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ParameterBinding::default(),
            FixedStateFrame::new(&state, &state, None, &retained_states),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        let (spelled, events) = crate::instrumentation::collect(|| {
            crate::kernel::search::ProofSearch::available_surface_fact(
                &(root),
                &surfaces,
                Some(&anchor),
                &missing,
            )
        });
        assert!(spelled.is_none(), "no state names the missing variable");
        let walks = events
            .iter()
            .filter(|event| {
                matches!(event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "solve premise surface at recorded states"
                )
            })
            .count();
        assert!(
            walks <= 1,
            "size {size}: a completed history miss must not restart ({walks} walks)"
        );
        let spelled = crate::kernel::search::ProofSearch::available_surface_fact(
            &(root),
            &surfaces,
            Some(&anchor),
            &named,
        )
        .expect("a named current value remains available");
        assert_eq!(
            root.lower_surface_proposition_direct(&spelled, "named control")
                .unwrap(),
            named
        );
        assert!(root.facts().contains(&missing));
    }
}

fn same_block_offset_rewrite_work(
    pointer_history: usize,
    state_count: usize,
    from_cursor: bool,
) -> usize {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let base = Pointer {
        block: crate::kernel::PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(8_179_100)), 4),
    };
    let remaining = MachineTerm::Variable(Variable(8_179_101));
    // `k as uint32 as int32`: σ of the low word, as written.
    let k = MachineTerm::sign_cast32(
        MachineIntegerType::UInt32,
        MachineIntegerType::Int32,
        MachineTerm::legacy_cast(
            MachineCastSpelling::UInt32From64,
            Box::new(remaining.clone()),
        ),
    );
    let shifted = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Add(
            Box::new(base.offset.clone()),
            Box::new(PointerOffsetTerm::scaled_int32_node(
                binary_node!(
                    Int32,
                    Subtract,
                    Box::new(MachineTerm::constant(4)),
                    Box::new(k.clone()),
                ),
                4,
            )),
        ),
    };
    let cursor = Pointer::symbolic(Variable(8_179_099));
    let state = ExecutionState::new()
        .with_local("cursor", ProgramValue::pointer(cursor.clone()))
        .with_local("base", ProgramValue::pointer(base.clone()))
        .with_local("k", ProgramValue::UInt64(remaining));
    let mut facts = (0..pointer_history)
        .flat_map(|i| {
            let old = MachineTerm::legacy_cast(
                MachineCastSpelling::UInt32From64,
                Box::new(MachineTerm::Variable(Variable(8_180_000 + i as u64))),
            );
            [
                Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(
                        Pointer {
                            block: base.block.clone(),
                            offset: PointerOffsetTerm::Add(
                                Box::new(base.offset.clone()),
                                Box::new(PointerOffsetTerm::scaled_int32_node(
                                    binary_node!(
                                        Int32,
                                        Subtract,
                                        Box::new(MachineTerm::constant(4)),
                                        Box::new(old.clone()),
                                    ),
                                    4,
                                )),
                            ),
                        },
                        base.clone(),
                    ),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(old),
                        right: Box::new(MachineTerm::constant(4)),
                    },
                    true,
                ),
            ]
        })
        .collect::<Vec<_>>();
    let bound = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(k),
            right: Box::new(MachineTerm::constant(4)),
        },
        true,
    );
    facts.push(bound.clone());
    let fixture = crate::surface::parse("theorem shifted(cursor: int32*, base: int32*, k: uint64) { requires (k as uint32 as int32) == 4; requires cursor == base + (4 - (k as uint32 as int32)); ensures true; }").unwrap();
    let surface = fixture.theorem_definitions()[0].requires[0]
        .proposition()
        .unwrap()
        .clone();
    let mut surfaces = SurfacePropositionMap::default();
    // The checked scalar fact has no recorded source form, as in a loop-head have.
    let lowered = lower_fixed_state_proposition_with_assumptions(
        &surface,
        &PureFactContext::new(),
        ParameterBinding::default(),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        SpecDefinitions::new(&predicates, &functions),
    )
    .unwrap();
    assert_eq!(lowered, bound);
    let entry = state.clone().with_local(
        "k",
        ProgramValue::UInt64(MachineTerm::Variable(Variable(8_179_098))),
    );
    if from_cursor {
        let local_native_output_213 = state.locals().get_native("cursor");
        let ProgramValue::Pointer(cursor_value) = local_native_output_213.as_deref().unwrap()
        else {
            unreachable!()
        };
        let local_native_output_216 = state.locals().get_native("base");
        let ProgramValue::Pointer(base_value) = local_native_output_216.as_deref().unwrap() else {
            unreachable!()
        };
        let mut shifted_value = base_value.clone();
        shifted_value.replace_pointer(shifted.clone());
        let relation = Proposition::ConditionIs(
            ConditionTerm::pointer_value_equal(cursor_value.clone(), shifted_value),
            true,
        );
        let relation_surface = fixture.theorem_definitions()[0].requires[1]
            .proposition()
            .unwrap()
            .clone();
        assert_eq!(
            lower_fixed_state_proposition_with_assumptions(
                &relation_surface,
                &assumptions_from_propositions(&facts),
                ParameterBinding::default(),
                FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                SpecDefinitions::new(&predicates, &functions),
            )
            .unwrap(),
            relation,
        );
        surfaces
            .record_lowering(&relation_surface, &relation)
            .unwrap();
        facts.insert(0, relation);
    }
    let mut retained_states = RecordedStates::new();
    for i in 0..state_count {
        retained_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Region(i),
                kind: ProgramPointKind::Entry,
            },
            entry.clone(),
        );
    }
    let anchor = ProgramPointRef {
        region: CodeRegionRef::Region(state_count - 1),
        kind: ProgramPointKind::Entry,
    };
    let root = Proof::for_fixed_state_goal_with_requirements(
        "same-block offset equality",
        0,
        &facts,
        Proposition::ConditionIs(
            ConditionTerm::pointer_equal(if from_cursor { cursor } else { shifted }, base),
            true,
        ),
        ParameterBinding::default(),
        FixedStateFrame::new(&entry, &state, None, &retained_states),
        Some(&anchor),
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
        &[],
        &[],
    );
    let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(root))
    });
    let closed = closed.expect("the offset's k == 4 fact should close the pointer equality");
    assert!(closed.is_complete());
    // Shared literal propagation can close the goal during its last rewrite;
    // only the selected pointer equality needs an explicit checked rewrite.

    assert_eq!(
        closed
            .certificate()
            .steps()
            .iter()
            .filter(|step| matches!(step, ProofStep::Rewrite(_)))
            .count(),
        1
    );
    work
}

#[test]
fn same_block_pointer_offset_rewrite_ignores_other_pointers_at_the_base() {
    let costs = [4, 8, 16, 32].map(|size| same_block_offset_rewrite_work(size, 4, false));
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] + 64),
        "{costs:?}"
    );
}

#[test]
fn same_block_pointer_offset_rewrite_does_not_search_recorded_states() {
    let costs = [4, 8, 16, 32].map(|size| same_block_offset_rewrite_work(4, size, true));
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] + 64),
        "{costs:?}"
    );
}

#[test]
fn both_and_scopes_are_isolated_check_provenance_and_scale() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let context = pure_identity_fixture();
    let truth = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let other = Proposition::Equal(
        Term::Bitvector32(MachineTerm::constant(7)),
        Term::Bitvector32(MachineTerm::constant(7)),
    );
    let goal = Proposition::And(Box::new(truth.clone()), Box::new(other.clone()));
    let samples = [16, 32, 64, 128].map(|size| {
        let facts = (0..size)
            .map(|i| Proposition::Predicate {
                name: format!("ambient_{i}"),
                arguments: vec![],
            })
            .collect::<Vec<_>>();
        let root = Proof::for_pure_goal(
            "both",
            &facts,
            goal.clone(),
            &context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let ((joined, split_proof, left_done, marker, split, ids), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let (split_proof, split, ids) = root.split_focused_both().unwrap();
                let marker = split_proof.checkpoint();
                assert_eq!(
                    split_proof.focus_branch(ids[0]).unwrap().goal(),
                    Some(&truth)
                );
                assert_eq!(
                    split_proof.focus_branch(ids[1]).unwrap().goal(),
                    Some(&other)
                );
                assert!(!split_proof.facts().contains(&truth));
                assert!(!split_proof.facts().contains(&other));
                let left_done = split_proof
                    .focus_branch(ids[0])
                    .unwrap()
                    .driver()
                    .apply_step(ProofStep::Normalize)
                    .unwrap();
                let right = left_done.focus_branch(ids[1]).unwrap();
                assert!(!right.facts().contains(&truth));
                let done = right.driver().apply_step(ProofStep::Normalize).unwrap();
                let joined = done.join_focused_both(&marker, split, ids).unwrap();
                (joined, split_proof, left_done, marker, split, ids)
            });
        assert!(joined.is_complete());
        assert!(left_done.join_focused_both(&marker, split, ids).is_err());
        let (foreign, foreign_split, foreign_ids) = root.split_focused_both().unwrap();
        let done = left_done
            .focus_branch(ids[1])
            .unwrap()
            .driver()
            .apply_step(ProofStep::Normalize)
            .unwrap();
        assert!(
            done.join_focused_both(&foreign.checkpoint(), foreign_split, foreign_ids)
                .is_err()
        );
        assert_eq!(split_proof.branches().count(), 2);
        assert!(matches!(
            joined.certificate().steps(),
            [ProofStep::Both { .. }]
        ));
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "{samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 5.7s in the parallel gate"]
fn loop_entry_solve_keeps_checked_unspellable_assumptions_and_scales() {
    let parsed = syntax::parse_function("int32 identity(int32 x) { return x; }").unwrap();
    let state = ExecutionState::new();
    let result = int32(0);
    let arguments = vec![ProgramExpression::Value(result.clone())];
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    // Loop producers may capture a value that the phase's source naming
    // tables do not spell. The producer's kernel judgment is authoritative;
    // its source proposition is a presentation, not a replacement judgment.
    let surface = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Variable("x".into())),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_less_than(
            MachineTerm::Variable(crate::kernel::Variable(1_000_000)),
            MachineTerm::uint64_constant(22208),
        ),
        true,
    );
    let obligation = crate::kernel::ProofObligation::new(goal.clone());
    let mut previous_work = None;
    for size in [16_u32, 64, 256, 1024] {
        let mut facts = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::uint64_less_than(
                        MachineTerm::Variable(crate::kernel::Variable(1_000_000)),
                        MachineTerm::uint64_constant(22209 + u64::from(index)),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        facts.push(goal.clone());
        let root = Proof::for_fixed_state_frontier(
            "loop entry unspellable assumption",
            0,
            &facts,
            ParameterBinding::new(parsed.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, Some(&result), &retained_states),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let scope = root
            .begin_loop_entry_goal(surface.clone(), &obligation)
            .unwrap();
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            (scope).driver().try_solve_closure().unwrap().unwrap()
        });
        assert_eq!(checked.body().certificate().steps(), &[ProofStep::Known]);
        let completion = checked.completed_loop_entry_goal().unwrap();
        assert_eq!(completion.proposition(), &goal);
        assert!(
            completion
                .root_assumptions()
                .shares_assumptions_with(root.facts())
        );
        assert!(checked.join().unwrap().facts().contains(&goal));
        if let Some(previous) = previous_work {
            assert!(
                work <= previous + 128,
                "{size}: {work} units after {previous}"
            );
        }
        previous_work = Some(work);
        let missing = Proof::for_fixed_state_frontier(
            "loop entry missing assumption",
            0,
            &facts[..facts.len() - 1],
            ParameterBinding::new(parsed.parameters(), &arguments),
            FixedStateFrame::new(&state, &state, Some(&result), &retained_states),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let missing = missing
            .begin_loop_entry_goal(surface.clone(), &obligation)
            .unwrap();
        assert!(missing.driver().apply_step(ProofStep::Known).is_err());
        assert!(missing.join().is_err());
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn choose_projection_walk_is_deterministic_across_selected_body_sizes() {
    let click_file = crate::surface::parse(
        r#"
            int32 identity(int32 x) {
                requires exists (k: int32) { k == x };
                ensures result == x;
            }
        "#,
    )
    .expect("the existential requirement should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
        .expect("test function should parse");
    let function = parsed_function.to_kernel_function();
    let predicates = PredicateEnvironment::new(&[]);
    let click_functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(&[]);
    let execution_environment = ExecutionEnvironment::new();
    let state = ExecutionState::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];

    fn balanced_and(mut leaves: Vec<Proposition>) -> Proposition {
        while leaves.len() > 1 {
            let mut next = Vec::with_capacity(leaves.len().div_ceil(2));
            let mut pairs = leaves.into_iter();
            while let Some(left) = pairs.next() {
                let Some(right) = pairs.next() else {
                    next.push(left);
                    break;
                };
                next.push(Proposition::And(Box::new(left), Box::new(right)));
            }
            leaves = next;
        }
        leaves
            .pop()
            .expect("a selected body must have at least one leaf")
    }

    let run = |size: u32| {
        let chosen_variable = Variable(9_300_000);
        let body = balanced_and(
            (0..size)
                .map(|index| {
                    Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(MachineTerm::Variable(chosen_variable)),
                            right: Box::new(MachineTerm::constant(index)),
                        },
                        true,
                    )
                })
                .collect(),
        );
        let source = Proposition::Exists {
            name: "source_value".to_string(),
            var: chosen_variable,
            sort: Sort::ProgramInt32,
            body: Box::new(body),
        };
        let owner = CallerSourceOwnerId::ordinary("test.c", "identity");
        let entry_origins = vec![EntryFactOrigin::Requirement {
            source_id: RequirementSourceId {
                owner: owner.clone(),
                outer_ordinal: 0,
            },
            role: RequirementFactRole::Principal {
                unfolding_path: Vec::new(),
            },
        }];
        let caller_requirement_index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            function_block,
            parsed_function.parameters(),
            std::slice::from_ref(&source),
            &entry_origins,
            crate::kernel::MemoryStateIdentity::of(state.memory()),
        );
        let before = fact_node_allocations();
        let root = Proof::for_execution_frontier(
            "chosen projection scaling",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier::default(),
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            vec![source.clone()],
            ExecutionProofConstants {
                function_entry_state: Some(state.clone()),
                execution_start_facts: Arc::new(PureFactList::from(vec![source])),
                entry_fact_origins: entry_origins.into(),
                caller_requirement_index: caller_requirement_index.into(),
                caller_source_owner: Some(owner),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &execution_environment,
            &resources,
            SpecDefinitions::new(&predicates, &click_functions),
            &theorems,
        );
        CHOSEN_PROJECTION_WALK_WORK.with(|count| count.set((0, 0)));
        let chosen = root
            .driver()
            .apply_step(ProofStep::Choose(ProofChoice {
                name: "candidate".to_string(),
                source: ProofFactSource::Requirement(0),
            }))
            .expect("the selected existential should check");
        let leaves = chosen
            .execution()
            .and_then(|execution| execution.presentation.chosen_projection.as_ref())
            .map_or(0, |projection| projection.leaves.len());
        (
            leaves,
            CHOSEN_PROJECTION_WALK_WORK.with(std::cell::Cell::get),
            fact_node_allocations() - before,
        )
    };

    let mut samples = Vec::new();
    for size in [8_u32, 32, 128, 512] {
        let _ = run(size);
        let first = crate::instrumentation::measure_deterministic_work(|| run(size));
        let second = crate::instrumentation::measure_deterministic_work(|| run(size));
        assert_eq!(
            first.0.0, second.0.0,
            "leaf count must be deterministic at {size}"
        );
        assert_eq!(
            first.0.0, size as usize,
            "all selected leaves must be retained at {size}"
        );
        // Fact indexing and proof setup are outside the projection walk.
        // Their AVL shapes can differ between identical semantic samples:
        // a phased reproduction had totals 3047/3049 at 32 leaves, while
        // setup used 6 nodes and the walk used 96 nodes in both runs.
        assert_eq!(
            first.0.1, second.0.1,
            "projection visits and allocations must be deterministic at {size}"
        );
        assert_eq!(
            first.0.1.0,
            (2 * size - 1) as usize,
            "the walk must visit each selected conjunction node once"
        );
        samples.push((size, first.1, first.0.1.1, first.0.2));
        samples.push((size, second.1, second.0.1.1, second.0.2));
    }
    let (base_size, base_work, base_walk_allocations, _) = samples[0];
    for (size, work, walk_allocations, total_allocations) in samples {
        assert!(
            work <= base_work + 64 * (size - base_size) as usize,
            "selected-body projection work exceeded the linear bound at {size}: {work}"
        );
        assert!(
            walk_allocations <= base_walk_allocations + 8 * (size - base_size) as usize,
            "projection walk allocations exceeded the linear bound at {size}: {walk_allocations}"
        );
        // The complete choose also updates persistent fact indexes; their
        // logarithmic search paths have a separate size-dependent bound.
        let index_height = (u32::BITS - size.leading_zeros()) as usize;
        assert!(
            total_allocations <= 32 * size as usize * index_height,
            "proof setup and choose allocations exceeded the indexed bound at {size}: {total_allocations}"
        );
    }
}

#[test]
fn explicit_loop_have_retains_checked_body_and_complete_invariant_bundle() {
    let file = crate::surface::parse(
        r#"
        predicate selected(x: int32) { x == x }
        int32 identity(int32 x) { ensures result == x; }
    "#,
    )
    .unwrap();
    let parsed = syntax::parse_function("int32 identity(int32 x) { return x; }").unwrap();
    let function = parsed.to_kernel_function();
    let predicates = PredicateEnvironment::new(file.predicate_definitions());
    let click_functions = ClickFunctionEnvironment::new(file.click_function_definitions());
    let theorems = TheoremEnvironment::new(file.theorem_definitions());
    let resources = ResourceEnvironment::new(file.resource_definitions());
    let environment = ExecutionEnvironment::new();
    let arguments = vec![ProgramExpression::Value(int32(7))];
    let value = ContractExpression::ProgramExpression(ProgramExpression::Value(int32(7)));
    let surface = ClickProposition::PredicateCall {
        name: "selected".into(),
        arguments: vec![value.clone()],
    };
    let body_surface = ClickProposition::Comparison {
        left: value.clone(),
        operator: ComparisonOperator::Equal,
        right: value,
    };
    let spec = crate::kernel::SpecProposition::Comparison {
        left: crate::kernel::SpecExpression::Value(int32(7)),
        operator: crate::kernel::ComparisonOperator::Equal,
        right: crate::kernel::SpecExpression::Value(int32(7)),
    };
    let checks = vec![
        LoopInvariantCheck::new(spec, None, None),
        LoopInvariantCheck::new(
            crate::kernel::SpecProposition::Comparison {
                left: crate::kernel::SpecExpression::Value(int32(7)),
                operator: crate::kernel::ComparisonOperator::LessEqual,
                right: crate::kernel::SpecExpression::Value(int32(8)),
            },
            None,
            None,
        ),
    ];
    let legacy_surface = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(7))),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(8))),
    };
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let frontier = ExecutionFrontier {
            region: ExecutionRegionKind::LoopBody,
            position: FrontierPosition::RegionBoundary,
            ..ExecutionFrontier::default()
        };
        let root = Proof::for_execution_frontier(
            "checked loop have",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                frontier,
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                invariant_body_context: Some(Arc::new(InvariantBodyContext {
                    loop_index: 0,
                    checks: checks.clone(),
                    iterations: Some(crate::kernel::IntegerTerm::var(crate::kernel::Variable(
                        9_999,
                    ))),
                    ..InvariantBodyContext::default()
                })),
                ..ExecutionProofConstants::default()
            },
            &file.function_blocks()[0],
            &function,
            &parsed,
            &arguments,
            &environment,
            &resources,
            SpecDefinitions::new(&predicates, &click_functions),
            &theorems,
        )
        .driver()
        .apply_step(ProofStep::UnfoldPredicate("selected".into()))
        .unwrap();
        let body_kernel = root.lower_surface_goal(&body_surface, "test body").unwrap();
        let scope = root.driver().open_have(surface.clone()).unwrap();
        assert!(scope.clone().join().is_err());
        let closed = scope.driver().apply_step(ProofStep::Normalize).unwrap();
        let (joined, work) =
            crate::instrumentation::measure_deterministic_work(|| closed.join().unwrap());
        samples.push(work);
        assert!(joined.facts().contains(&body_kernel));
        assert!(!root.facts().contains(&body_kernel));
        assert_eq!(joined.added_facts().len(), 2);
        assert!(
            joined
                .execution()
                .unwrap()
                .presentation
                .surface_propositions
                .available_kernel_matching(&surface, |kernel| joined.facts().contains(kernel))
                .is_some()
        );
        let explicit = root
            .driver()
            .apply_step(ProofStep::Have {
                proposition: surface.clone(),
                proof: Box::new(ProofCertificate::from_steps(vec![ProofStep::Normalize]).unwrap()),
            })
            .unwrap();
        assert!(explicit.facts().contains(&body_kernel));
        assert!(joined.certify_loop_invariant_bundle(&checks, &[]).is_err());
        let prepared = joined
            .driver()
            .prepare_loop_invariant_bundle(
                &ExecutionState::new(),
                &ExecutionState::new(),
                &crate::kernel::IntegerTerm::var(crate::kernel::Variable(9_999)),
                &ProgramExpression::Value(int32(1)),
                &checks,
                &[],
                None,
                &[surface.clone(), legacy_surface.clone()],
                &[],
                &[],
                false,
            )
            .unwrap()
            .unwrap();
        let certified = prepared
            .certify_loop_invariant_bundle(&checks, &[])
            .unwrap();
        let execution = certified.execution().unwrap();
        let record = execution.core.checked_invariant_lowerings.as_ref().unwrap();
        assert_eq!(record.checks(), checks);
        assert!(matches!(
            prepared.certificate().steps().last(),
            Some(ProofStep::CloseInvariantsBy(_))
        ));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "loop have join work: {samples:?}"
        );
    }
}

#[test]
fn explicit_invariant_body_scales_and_supplies_kernel_validation() {
    let file = crate::surface::parse("int32 region(int32 x) { ensures result == x; }").unwrap();
    let block = &file.function_blocks()[0];
    let predicates = PredicateEnvironment::new(&[]);
    let click_functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let parsed = syntax::parse_function("int32 region(int32 x) { return x; }").unwrap();
    let function = parsed.to_kernel_function();
    let functions = ExecutionEnvironment::new();
    let resources = ResourceEnvironment::new(&[]);
    let arguments = [ProgramExpression::Value(int32(7))];
    let checks = vec![crate::kernel::LoopInvariantCheck::new(
        crate::kernel::SpecProposition::Comparison {
            left: crate::kernel::SpecExpression::Value(int32(0)),
            operator: crate::kernel::ComparisonOperator::LessEqual,
            right: crate::kernel::SpecExpression::Value(int32(0)),
        },
        None,
        None,
    )];
    let samples = [16, 32, 64, 128].map(|size| {
        let root = Proof::for_execution_frontier(
            "explicit invariant body",
            0,
            ExecutionProofState::at_entry(
                ExecutionState::new(),
                ExecutionFrontier {
                    region: ExecutionRegionKind::LoopBody,
                    position: FrontierPosition::RegionBoundary,
                    ..Default::default()
                },
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                invariant_body_context: Some(Arc::new(InvariantBodyContext {
                    loop_index: 0,
                    checks: checks.clone(),
                    iterations: Some(crate::kernel::IntegerTerm::var(crate::kernel::Variable(
                        9_999,
                    ))),
                    ..InvariantBodyContext::default()
                })),
                ..Default::default()
            },
            block,
            &function,
            &parsed,
            &arguments,
            &functions,
            &resources,
            SpecDefinitions::new(&predicates, &click_functions),
            &theorems,
        );
        let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.driver()
                .apply_close_invariants_body(&[ProofTactic::Normalize])
                .unwrap()
        });
        assert!(root.certificate().steps().is_empty());
        assert!(
            !root
                .execution()
                .unwrap()
                .core
                .region_invariants_close_requested
        );
        assert!(
            closed
                .execution()
                .unwrap()
                .core
                .region_invariants_close_requested
        );
        assert_eq!(root.facts().to_vec(), closed.facts().to_vec());
        assert!(
            root.execution()
                .unwrap()
                .core
                .state
                .shares_storage_with(&closed.execution().unwrap().core.state)
        );
        assert!(matches!(
            closed.certificate().steps(),
            [ProofStep::CloseInvariantsBy(_)]
        ));
        // A bare request is not evidence; the completed kernel-owned scope is.
        let Ok(requested) = root.state.request_frontier_invariant_closure() else {
            panic!("an unclosed loop frontier accepts a closure request")
        };
        assert!(
            root.with_kernel_state(requested)
                .certify_loop_invariant_bundle(&checks, &[])
                .is_err()
        );
        closed.certify_loop_invariant_bundle(&checks, &[]).unwrap();
        assert!(
            closed
                .driver()
                .apply_close_invariants_body(&[ProofTactic::Normalize])
                .is_err()
        );
        assert!(root.driver().apply_close_invariants_body(&[]).is_err());
        work
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
            "{samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn cursor_execution_load_binding_work_is_deterministic_and_output_sized() {
    let click_file = crate::surface::parse(
        r#"
            int32 branch_load_scaling(int32 x, int32 p[1]) {
                ensures returns_any: result == result by { known(); }
            }
        "#,
    )
    .expect("test function contract should parse");
    let function_block = &click_file.function_blocks()[0];
    let parsed_function = syntax::parse_function(
        "int32 branch_load_scaling(int32 x, int32 p[1]) { if (x < 0) { return p[0]; } else { return p[0]; } }",
    )
    .expect("test C branch should parse");
    let function = parsed_function.to_kernel_function();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ))),
    );
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(60_002)))),
        ProgramExpression::Value(ProgramValue::pointer(pointer.clone())),
    ];
    let function_environment = ExecutionEnvironment::new();
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment =
        ClickFunctionEnvironment::new(click_file.click_function_definitions());
    let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
    let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
    let run = |size: u32| {
        let root = Proof::for_execution_frontier(
            "cursor load scaling proof",
            0,
            ExecutionProofState::at_entry(
                state.clone(),
                ExecutionFrontier {
                    next_statement_index: 0,
                    ..ExecutionFrontier::default()
                },
                RecordedStates::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            (0..size).map(indexed_fact).collect::<Vec<_>>(),
            ExecutionProofConstants {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..ExecutionProofConstants::default()
            },
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resource_environment,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let (split, record) = root
            .split_focused_execution_branch()
            .expect("scaling branch should split");
        let advanced = split
            .focus_split_arm(&record, true)
            .expect("then scaling arm should be open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("then scaling load should execute")
            .focus_split_arm(&record, false)
            .expect("else scaling arm should be open")
            .driver()
            .apply_step(ProofStep::Step)
            .expect("else scaling load should execute");
        let joined = advanced
            .join_focused_execution_terminal(&record)
            .expect("scaling load arms should join");
        // Reads remain structural values; joining must preserve the actual
        // returned loads without inventing generated source bindings.
        let terminal = joined
            .finalization_view()
            .expect("joined outcomes should remain");
        let paths = terminal.frontier.execution().unwrap().paths();
        assert!(!paths.is_empty());
        for path in paths {
            assert!(matches!(path.outcome(),
                FunctionOutcome::Return { value, .. }
                    if matches!(value.native().as_ref(), ProgramValue::Int32(MachineTerm::MemoryLoad(_, at, crate::kernel::LoadKind::Int32)) if **at == pointer)));
        }
        let execution = joined.execution().expect("joined execution should remain");
        (
            execution.presentation.generated_load_bindings.len(),
            execution.presentation.generated_load_binding_events.len(),
        )
    };
    let mut samples = Vec::new();
    for size in [8_u32, 32, 128, 512] {
        // Warm the shared parser/kernel caches so the measured cursor work
        // reflects the transition and join paths rather than one-time setup.
        let _ = run(size);
        let (first, first_work) = crate::instrumentation::measure_deterministic_work(|| run(size));
        let (second, _second_work) =
            crate::instrumentation::measure_deterministic_work(|| run(size));
        assert_eq!(
            first, second,
            "cursor result must be deterministic at size {size}"
        );
        assert_eq!(
            first,
            (0, 0),
            "load metadata output must stay constant at size {size}"
        );
        samples.push((size, first_work));
    }
    let (base_size, base_work) = samples[0];
    for (size, work) in samples {
        assert!(
            work <= base_work + 64 * (size - base_size) as usize,
            "cursor load metadata work grew beyond the output-sized bound at size {size}: {work} > {}",
            base_work + 64 * (size - base_size) as usize
        );
    }
}

#[test]
fn integer_equality_rewrite_builds_names_only_on_refusal_and_scales() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let surface = ClickProposition::Comparison {
        left: ContractExpression::Binding("x".into()),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::Binding("y".into()),
    };
    let mut baseline = None;
    for size in [4usize, 16, 64, 256] {
        // Keep every measurement cold. Reusing the same variables across
        // sizes would warm the new shared-term bridge only after size 4.
        let x = IntegerTerm::var(Variable(9_103_000 + 2 * size as u64));
        let y = IntegerTerm::var(Variable(9_103_001 + 2 * size as u64));
        let equality = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(x.clone().into(), y.clone().into()),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::multiply(x.clone(), x.clone()).into(),
                y.clone().into(),
            ),
            true,
        );

        let context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            memory: Memory::new(),
            array_refs: BTreeMap::new(),
            requires: vec![equality.clone()],
            surface_requirements: SurfacePropositionMap::default(),
            values: (0..size)
                .map(|i| (format!("unused_{i}"), int32(i as u32)))
                .collect(),
        };
        let root = Proof::for_pure_goal(
            "Integer rewrite names",
            &context.requires,
            goal.clone(),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let calls = std::cell::Cell::new(0);
        let name = || {
            calls.set(calls.get() + 1);
            crate::surface::diagnostics::value_naming_tables(&context.values)
        };
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.finish_rewrite(
                Box::new(goal.clone()),
                Box::new(equality.clone()),
                &surface,
                name,
            )
        });
        checked.expect("checked Integer rewrite should refine its goal");
        assert_eq!(
            calls.get(),
            0,
            "size {size}: successful rewrite scanned diagnostic names"
        );
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "size {size}: unrelated locals changed rewrite work"
        );
        let empty = Proof::for_pure_goal(
            "Integer rewrite refusal names",
            &[],
            goal.clone(),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let error = empty
            .finish_rewrite(
                Box::new(goal.clone()),
                Box::new(equality.clone()),
                &surface,
                name,
            )
            .err()
            .expect("missing evidence should be refused");
        assert_eq!(calls.get(), 1);
        assert!(error.message().contains("exact available fact"));
        assert!(error.message().len() < 8000);
    }
}

#[test]
fn state_premise_synthesis_seeks_near_anchor_without_scanning_history() {
    let parameters = syntax::parse_function("int32 noop(int32 x) { return x; }").unwrap();
    let value = MachineTerm::Variable(Variable(8_178_901));
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(value.clone()))];
    let parameter_binding = ParameterBinding::new(parameters.parameters(), &arguments);
    let kernel = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(value),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    let anchor = ProgramPointRef {
        region: CodeRegionRef::Region(1),
        kind: ProgramPointKind::Entry,
    };
    for size in [16usize, 64, 256, 1024, 4096] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                ExecutionState::new(),
            );
        }
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            super::super::super::smart_closures::synthesize_surface_at_recorded_states(
                &kernel,
                parameter_binding,
                &retained_states,
                &anchor,
            )
            .next()
        });
        let surface = surface.expect("the nearest state should name the parameter");
        assert!(proposition_contains_at_expression(&surface));
        let state = ExecutionState::new();
        let lowered = lower_fixed_state_proposition_with_assumptions(
            &surface,
            &PureFactContext::new(),
            parameter_binding,
            FixedStateFrame::new(&state, &state, None, &retained_states),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
        )
        .expect("the candidate must lower against the selected state");
        assert_eq!(
            lowered, kernel,
            "state spelling must preserve the exact premise"
        );
        let height = usize::BITS - size.leading_zeros();
        assert!(
            work <= 32 * height as usize + 128,
            "size {size}: {work} synthesis work"
        );
        crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            assert!(
                super::super::super::smart_closures::synthesize_surface_at_recorded_states(
                    &kernel,
                    parameter_binding,
                    &retained_states,
                    &anchor
                )
                .next()
                .is_none()
            );
        });
    }
}

#[test]
fn missing_state_premise_spelling_has_bounded_history_search() {
    let parameters = syntax::parse_function("int32 noop() { return 0; }").unwrap();
    // No state or parameter names this symbolic value. Every synthesis probe
    // misses, exercising the exhaustive-history fallback rather than the
    // successful first-candidate case.
    let kernel = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(8_178_903))),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    for size in [16usize, 64, 256, 1024, 4096] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                ExecutionState::new(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(size / 2),
            kind: ProgramPointKind::Entry,
        };
        let (count, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut candidates =
                super::super::super::smart_closures::synthesize_surface_at_recorded_states(
                    &kernel,
                    ParameterBinding::new(parameters.parameters(), &[]),
                    &retained_states,
                    &anchor,
                );
            let count = candidates.by_ref().count();
            assert!(candidates.next().is_none());
            count
        });
        assert_eq!(count, 0);
        let height = usize::BITS - size.leading_zeros();
        assert!(
            work <= 256 * height as usize + 8192,
            "size {size}: {work} work"
        );
    }
}

#[test]
fn state_premise_candidates_stop_on_deterministic_work_exhaustion() {
    use crate::instrumentation::{TacticEvent, TacticWorkLimits, VerificationEvent};
    let parameters = syntax::parse_function("int32 noop(int32 x) { return x; }").unwrap();
    let value = MachineTerm::Variable(Variable(8_178_902));
    let arguments = vec![ProgramExpression::Value(ProgramValue::Int32(value.clone()))];
    let kernel = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(value),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    let anchor = ProgramPointRef {
        region: CodeRegionRef::Region(0),
        kind: ProgramPointKind::Entry,
    };
    for size in [16usize, 64, 256, 1024, 4096] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                ExecutionState::new(),
            );
        }
        // Exhaust before the independent state-candidate search cap. A
        // normal bounded search miss need not consume the tactic budget.
        let limit = 8;
        let ((candidates, work), events) = crate::instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: limit,
                smart: limit,
                control: limit,
            },
            || {
                crate::instrumentation::collect(|| {
                    let tactic = TacticEvent {
                        source_tactic_path: None,
                        claim: "state budget".into(),
                        tactic_index: 0,
                        tactic_name: "solve".into(),
                        class: "smart".into(),
                        statement_index: 0,
                        source_index: 0,
                    };
                    crate::instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                    let measured = crate::instrumentation::measure_deterministic_work(|| {
                        let mut candidates =
                            super::super::super::smart_closures::synthesize_surface_at_recorded_states(
                                &kernel,
                                ParameterBinding::new(parameters.parameters(), &arguments),
                                &retained_states,
                                &anchor,
                            );
                        let count = candidates.by_ref().count();
                        assert!(candidates.next().is_none());
                        count
                    });
                    crate::instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                    measured
                })
            },
        );
        assert!(
            candidates < size,
            "exhaustion must prevent visiting the whole history"
        );
        assert!(
            work <= limit + 16,
            "size {size}: {work} work after limit {limit}"
        );
        assert!(
            events
                .iter()
                .any(|event| matches!(event, VerificationEvent::TacticWorkBudgetExceeded { .. })),
            "the work miss must retain its budget diagnosis"
        );
    }
}

#[test]
fn wide_bound_direct_rewrite_ignores_connected_ambient_equalities() {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let click_function_environment = ClickFunctionEnvironment::new(&[]);
    let theorem_environment = TheoremEnvironment::new(&[]);
    let x = MachineTerm::Variable(Variable(9_920_000));
    let y = MachineTerm::Variable(Variable(9_920_001));
    let bound = MachineTerm::uint64_constant(22208);
    let equality = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(x.clone()),
            right: Box::new(y.clone()),
        },
        true,
    );
    let known = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: Box::new(y.clone()),
            right: Box::new(bound.clone()),
        },
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: Box::new(x.clone()),
            right: Box::new(bound.clone()),
        },
        true,
    );
    let expression = |name: &str| {
        ContractExpression::ProgramExpression(ProgramExpression::Variable(name.into()))
    };
    let equality_surface = ClickProposition::Comparison {
        left: expression("x"),
        operator: ComparisonOperator::Equal,
        right: expression("y"),
    };
    let goal_surface = ClickProposition::Comparison {
        left: expression("x"),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt64(bound),
        )),
    };
    let mut costs = Vec::new();
    for ambient in [0, 16, 64, 256, 1024] {
        let mut facts = vec![equality.clone(), known.clone()];
        for i in 0..ambient {
            facts.push(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: Box::new(y.clone()),
                    right: Box::new(MachineTerm::Variable(Variable(9_921_000 + i))),
                },
                true,
            ));
        }
        let mut surface_requirements = SurfacePropositionMap::default();
        surface_requirements
            .record_lowering(&equality_surface, &equality)
            .unwrap();
        let theorem_context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            memory: Memory::new(),
            values: BTreeMap::from([
                ("x".into(), ProgramValue::UInt64(x.clone())),
                ("y".into(), ProgramValue::UInt64(y.clone())),
            ]),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements,
        };
        let root = Proof::for_pure_goal_with_surface(
            "direct wide bound",
            &facts,
            goal.clone(),
            Some(goal_surface.clone()),
            &theorem_context,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            &theorem_environment,
        );
        let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::try_indexed_direct_equality_rewrite(&(root), false)
                .break_value()
                .flatten()
        });
        let closed = closed.expect("one checked rewrite should expose the recorded bound");
        assert!(closed.is_complete());
        assert_eq!(closed.certificate().steps().len(), 2);
        assert!(matches!(
            &closed.certificate().steps()[0],
            ProofStep::Rewrite(_)
        ));
        assert!(matches!(&closed.certificate().steps()[1], ProofStep::Known));
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0]),
        "{costs:?}"
    );
}

#[test]
fn loop_entry_wide_extent_guard_retains_its_own_source_and_scales() {
    let parsed = syntax::parse_function("void span(const uint8* buf, uint64 len) { }").unwrap();
    let pointer = Pointer::symbolic(Variable(812_000));
    let original = MachineTerm::Variable(Variable(812_001));
    let remaining =
        MachineTerm::uint64_subtract(original.clone(), MachineTerm::uint64_constant(16));
    // The source retains `16 + len`, including when len stores `original - 16`.
    // Algebraic cancellation is a comparison rule, not the source's term.
    let extent = MachineTerm::logical_machine_binary(
        crate::kernel::MachineIntegerType::UInt64,
        crate::kernel::MachineBinaryOp::Add,
        MachineTerm::uint64_constant(16),
        remaining.clone(),
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(extent, MachineTerm::uint64_constant(i64::MAX as u64)),
        true,
    );
    let obligation = crate::kernel::ProofObligation::new(goal.clone());
    let base = ProgramExpression::Variable("buf".into());
    let start = ProgramExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(0)));
    let end = ProgramExpression::Add(
        Box::new(ProgramExpression::Value(ProgramValue::UInt64(
            MachineTerm::uint64_constant(16),
        ))),
        Box::new(ProgramExpression::Variable("len".into())),
    );
    let surface = ClickProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: base.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::ProgramExpression(base),
                start: ContractExpression::ProgramExpression(start),
                end: ContractExpression::ProgramExpression(end),
            },
        },
    };
    let arguments = vec![
        ProgramExpression::Value(ProgramValue::typed_pointer(
            pointer.clone(),
            ProgramType::UInt8Pointer,
        )),
        ProgramExpression::Value(ProgramValue::UInt64(original.clone())),
    ];
    let entry = ExecutionState::new()
        .with_local(
            "buf",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer),
        )
        .with_local("len", ProgramValue::UInt64(original));
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let mut work = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut state = entry
            .clone()
            .with_local("len", ProgramValue::UInt64(remaining.clone()));
        for index in 0..size {
            state = state.with_local(format!("unused_{index}"), int32(index));
        }
        let facts = vec![goal.clone()];
        let root = Proof::for_fixed_state_frontier(
            "wide loop view guard",
            0,
            &facts,
            ParameterBinding::new(parsed.parameters(), &arguments),
            FixedStateFrame::new(&entry, &state, None, &retained_states),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
            let scope = root
                .begin_loop_entry_goal(surface.clone(), &obligation)
                .unwrap();
            let before = scope.body().clone();
            let completed = before.driver().apply_step(ProofStep::Known).unwrap();
            let retained = before.retain_completed_goal(&completed, &[]).unwrap();
            assert!(retained.facts().contains(&goal));
        });
        work.push(units);
    }
    assert!(
        work[3] <= work[0] * 3 + 128,
        "loop guard source walked unrelated locals: {work:?}"
    );
}

#[test]
fn completed_goal_retention_validates_current_source_after_stale_recording() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let entry_len = MachineTerm::Variable(Variable(813_000));
    let current_len =
        MachineTerm::uint64_subtract(entry_len.clone(), MachineTerm::uint64_constant(16));
    let limit = MachineTerm::uint64_constant(22208);
    let bound = |length| {
        Proposition::ConditionIs(
            ConditionTerm::uint64_less_equal(length, limit.clone()),
            true,
        )
    };
    let old_goal = bound(entry_len.clone());
    let current_goal = bound(current_len.clone());
    let surface = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Variable("len".into())),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt64(limit),
        )),
    };
    let entry = ExecutionState::new().with_local("len", ProgramValue::UInt64(entry_len));
    let retained_states = RecordedStates::new();
    let mut surfaces = SurfacePropositionMap::default();
    surfaces.record_lowering(&surface, &old_goal).unwrap();
    let mut work = Vec::new();
    for size in [0, 16, 64, 256, 1024] {
        let mut state = entry
            .clone()
            .with_local("len", ProgramValue::UInt64(current_len.clone()));
        for index in 0..size {
            state = state.with_local(format!("unused_{index}"), int32(index));
        }
        let facts = vec![old_goal.clone(), current_goal.clone()];
        let root = Proof::for_fixed_state_surface_goal(
            "current retained bound",
            0,
            &facts,
            current_goal.clone(),
            surface.clone(),
            ParameterBinding::default(),
            &entry,
            &state,
            &retained_states,
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        assert_eq!(
            root.lower_surface_proposition(&surface, "stale source")
                .unwrap(),
            old_goal
        );
        let completed = root.driver().apply_step(ProofStep::Known).unwrap();
        let (retained, units) = crate::instrumentation::measure_deterministic_work(|| {
            root.retain_completed_goal(&completed, &[]).unwrap()
        });
        assert!(retained.facts().contains(&current_goal));
        work.push(units);
        let empty_surfaces = SurfacePropositionMap::default();
        let wrong = Proof::for_fixed_state_surface_goal(
            "mismatched retained bound",
            0,
            std::slice::from_ref(&old_goal),
            old_goal.clone(),
            surface.clone(),
            ParameterBinding::default(),
            &entry,
            &state,
            &retained_states,
            &empty_surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let completed = wrong.driver().apply_step(ProofStep::Known).unwrap();
        assert!(wrong.retain_completed_goal(&completed, &[]).is_err());
    }
    assert!(
        work[4] <= work[0] * 3 + 128,
        "retention walked unrelated locals: {work:?}"
    );
}

#[test]
fn indexed_rewrite_does_not_spell_registered_read_definitions() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let parsed = crate::surface::parse(
        "theorem alias(first: int32, second: int32) { requires first == second; ensures true; }",
    )
    .unwrap();
    let alias_surface = parsed.theorem_definitions()[0].requires[0]
        .proposition()
        .unwrap()
        .clone();
    let mut samples = Vec::new();
    for size in [4usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(
            crate::kernel::Memory::new().with_block("rewrite_reads", 4096),
        );
        let mut facts = Vec::new();
        let mut reads = Vec::new();
        for index in 0..size {
            let load = MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "rewrite_reads".into(),
                    offset: PointerOffsetTerm::Constant(index as i64 * 4),
                }),
                crate::kernel::LoadKind::Int32,
            );
            let (variable, registered) = crate::kernel::load_variable_for_term(&load).unwrap();
            let fact = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(MachineTerm::Variable(variable)),
                    right: Box::new(registered),
                },
                true,
            );
            assert!(crate::kernel::is_verified_load_variable_defining_fact(
                &fact
            ));
            facts.push(fact);
            reads.push(MachineTerm::Variable(variable));
        }
        let state = ExecutionState::new()
            .with_memory(memory.memory().clone())
            .with_local("first", ProgramValue::Int32(reads[0].clone()))
            .with_local("second", ProgramValue::Int32(reads[1].clone()));
        let mut retained_states = RecordedStates::new();
        for index in 0..8 {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                ExecutionState::new(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(7),
            kind: ProgramPointKind::Entry,
        };
        let surfaces = SurfacePropositionMap::default();
        let sum = reads
            .iter()
            .cloned()
            .fold(MachineTerm::constant(0), |sum, read| {
                binary_node!(Int32, Add, Box::new(sum), Box::new(read))
            });
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(sum),
                right: Box::new(MachineTerm::constant(7)),
            },
            true,
        );
        let root = Proof::for_fixed_state_goal_with_requirements(
            "registered read rewrite candidates",
            0,
            &facts,
            goal,
            ParameterBinding::default(),
            FixedStateFrame::new(&state, &state, None, &retained_states),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        let ((closed, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(root))
            })
        });
        assert!(
            closed.is_none(),
            "definitions do not establish the false sum"
        );
        let history_queries = events
            .iter()
            .filter(|event| {
                matches!(event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if *name == "solve premise surface at recorded states")
            })
            .count();
        assert_eq!(
            history_queries, 0,
            "registered definitions triggered state spelling at size {size}"
        );
        assert!(facts.iter().all(|fact| root.facts().contains(fact)));
        let alias = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(reads[0].clone()),
                right: Box::new(reads[1].clone()),
            },
            true,
        );
        let mut alias_facts = facts.clone();
        alias_facts.push(alias.clone());
        let mut alias_surfaces = SurfacePropositionMap::default();
        alias_surfaces
            .record_lowering(&alias_surface, &alias)
            .unwrap();
        for (premises, expected) in [(&alias_facts, true), (&facts, false)] {
            let proof = Proof::for_fixed_state_goal_with_requirements(
                "different reads remain usable",
                0,
                premises,
                alias.clone(),
                ParameterBinding::default(),
                FixedStateFrame::new(&state, &state, None, &retained_states),
                Some(&anchor),
                &alias_surfaces,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
                &[],
                &[],
                &[],
            );
            assert_eq!(
                crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(proof))
                    .is_some_and(|proof| proof.is_complete()),
                expected
            );
        }
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 5 + 64),
        "registered definition filtering exceeded input growth: {samples:?}"
    );
}

#[test]
fn current_scalar_premise_spelling_ignores_unrelated_recorded_states() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let before = MachineTerm::Variable(Variable(8_179_500));
    let now = MachineTerm::Variable(Variable(8_179_501));
    let entry = ExecutionState::new().with_local("value", ProgramValue::Int32(before.clone()));
    let state = ExecutionState::new().with_local("value", ProgramValue::Int32(now.clone()));
    let equal_zero = |value| {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(value),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        )
    };
    let current = equal_zero(now);
    let old = equal_zero(before);
    let facts = vec![current.clone(), old.clone()];
    let surfaces = SurfacePropositionMap::default();
    let mut samples = Vec::new();
    for size in [16usize, 64, 256] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                entry.clone(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(size - 1),
            kind: ProgramPointKind::Entry,
        };
        let root = Proof::for_fixed_state_goal_with_requirements(
            "current scalar premise",
            0,
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ParameterBinding::default(),
            FixedStateFrame::new(&entry, &state, None, &retained_states),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::available_surface_fact(
                &(root),
                &surfaces,
                Some(&anchor),
                &current,
            )
        });
        let surface = surface.expect("the current state names this selected fact");
        assert!(!proposition_contains_at_expression(&surface));
        assert!(!proposition_contains_old_expression(&surface));
        assert_eq!(
            root.lower_surface_proposition_direct(&surface, "current premise control")
                .unwrap(),
            current
        );
        // The same name has another value at entry. Its older fact must keep
        // that state instead of being reinterpreted as the current value.
        let old_surface = crate::kernel::search::ProofSearch::available_surface_fact(
            &(root),
            &surfaces,
            Some(&anchor),
            &old,
        )
        .expect("the entry state names the older selected fact");
        assert!(
            proposition_contains_at_expression(&old_surface)
                || proposition_contains_old_expression(&old_surface)
        );
        assert_eq!(
            root.lower_surface_proposition_direct(&old_surface, "old premise control")
                .unwrap(),
            old
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "current premise spelling searched unrelated states: {samples:?}"
    );
}

#[test]
fn mixed_entry_and_current_premise_spelling_ignores_unrelated_states() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let pointer = Pointer {
        block: crate::kernel::PointerBlock::Concrete("mixed-premise".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let entry = ExecutionState::new()
        .with_memory(Memory::new().with_block("mixed-premise", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt32Pointer),
        )
        .with_local(
            "now",
            ProgramValue::UInt32(MachineTerm::Variable(Variable(8_179_510))),
        );
    let state = entry
        .clone()
        .with_memory(
            entry
                .memory()
                .clone()
                .store(pointer, ProgramValue::UInt32(MachineTerm::constant(5))),
        )
        .with_local(
            "now",
            ProgramValue::UInt32(MachineTerm::Variable(Variable(8_179_511))),
        );
    let fixture = crate::surface::parse("theorem mixed(p: uint32*, now: uint32) { requires now == old(p[0]) % 7u32; ensures true; }").unwrap();
    let surface = fixture.theorem_definitions()[0].requires[0]
        .proposition()
        .unwrap();
    let surfaces = SurfacePropositionMap::default();
    let mut samples = Vec::new();
    for size in [16usize, 64, 256] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                entry.clone(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(size - 1),
            kind: ProgramPointKind::Entry,
        };
        let kernel = lower_fixed_state_proposition_with_assumptions(
            surface,
            &PureFactContext::new(),
            ParameterBinding::default(),
            FixedStateFrame::new(&entry, &state, None, &retained_states),
            SpecDefinitions::new(&predicates, &functions),
        )
        .unwrap();
        let facts = [kernel.clone()];
        let root = Proof::for_fixed_state_goal_with_requirements(
            "mixed entry/current premise",
            0,
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ParameterBinding::default(),
            FixedStateFrame::new(&entry, &state, None, &retained_states),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        let (spelled, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::available_surface_fact(
                &(root),
                &surfaces,
                Some(&anchor),
                &kernel,
            )
        });
        let spelled = spelled.expect("entry and current states together name this fact");
        assert!(proposition_contains_old_expression(&spelled));
        assert_eq!(
            root.lower_surface_proposition_direct(&spelled, "mixed premise control")
                .unwrap(),
            kernel
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "mixed premise spelling searched unrelated history: {samples:?}"
    );
}

#[test]
fn indexed_rewrite_does_not_search_history_for_unrecorded_store_facts() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let parsed = crate::surface::parse(
        "theorem alias(first: int32, second: int32) { requires first == second; ensures true; }",
    )
    .unwrap();
    let alias_surface = parsed.theorem_definitions()[0].requires[0]
        .proposition()
        .unwrap()
        .clone();
    let mut samples = Vec::new();
    for size in [4usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = crate::kernel::Memory::new().with_block("rewrite_reads", 4096);
        let mut facts = Vec::new();
        let mut reads = Vec::new();
        for index in 0..size {
            let pointer = Pointer {
                block: "rewrite_reads".into(),
                offset: PointerOffsetTerm::Constant(index as i64 * 4),
            };
            let stored = binary_node!(
                UInt32,
                Remainder,
                Box::new(MachineTerm::Variable(Variable(8_179_600 + index as u64,))),
                Box::new(MachineTerm::constant(7)),
            );
            memory = memory.store(pointer.clone(), ProgramValue::UInt32(stored.clone()));
            let load = MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(&memory),
                Box::new(pointer),
                crate::kernel::LoadKind::Int32,
            );
            // The `int32` read of a `uint32` store is σ of the stored value.
            facts.push(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(load.clone()),
                    right: Box::new(MachineTerm::sign_cast32(
                        MachineIntegerType::UInt32,
                        MachineIntegerType::Int32,
                        stored,
                    )),
                },
                true,
            ));
            reads.push(load);
        }
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        ) = &facts[0]
        else {
            unreachable!()
        };
        assert!(crate::kernel::is_store_fact(
            &ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: left.clone(),
                right: right.clone()
            },
            true
        ));
        assert!(!crate::kernel::is_store_fact(
            &ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: left.clone(),
                right: right.clone()
            },
            false
        ));
        assert!(!crate::kernel::is_store_fact(
            &ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: left.clone(),
                right: Box::new(binary_node!(
                    Int32,
                    Add,
                    right.clone(),
                    Box::new(MachineTerm::constant(1))
                ))
            },
            true
        ));
        let MachineTerm::MemoryLoad(memory_for_control, pointer_for_control, _) = left.as_ref()
        else {
            unreachable!()
        };
        assert!(!crate::kernel::is_store_fact(
            &ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::MemoryLoad(
                    memory_for_control.clone(),
                    pointer_for_control.clone(),
                    crate::kernel::LoadKind::Bits64
                )),
                right: right.clone()
            },
            true
        ));
        let state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_local("first", ProgramValue::Int32(reads[0].clone()))
            .with_local("second", ProgramValue::Int32(reads[1].clone()));
        let mut retained_states = RecordedStates::new();
        for index in 0..8 {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                ExecutionState::new(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(7),
            kind: ProgramPointKind::Entry,
        };
        let surfaces = SurfacePropositionMap::default();
        let sum = reads
            .iter()
            .cloned()
            .fold(MachineTerm::constant(0), |sum, read| {
                binary_node!(Int32, Add, Box::new(sum), Box::new(read))
            });
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(sum),
                right: Box::new(MachineTerm::constant(7)),
            },
            true,
        );
        let root = Proof::for_fixed_state_goal_with_requirements(
            "stored read rewrite candidates",
            0,
            &facts,
            goal,
            ParameterBinding::default(),
            FixedStateFrame::new(&state, &state, None, &retained_states),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        let ((closed, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(root))
            })
        });
        assert!(
            closed.is_none(),
            "store records do not establish the false sum"
        );
        let history_queries = events
            .iter()
            .filter(|event| {
                matches!(event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if *name == "solve premise surface at recorded states")
            })
            .count();
        assert_eq!(
            history_queries, 0,
            "unrecorded store facts triggered state spelling at size {size}"
        );
        assert!(facts.iter().all(|fact| root.facts().contains(fact)));
        let (spelled, direct_events) = crate::instrumentation::collect(|| {
            crate::kernel::search::ProofSearch::available_surface_fact(
                &(root),
                &surfaces,
                Some(&anchor),
                &facts[0],
            )
        });
        assert!(
            spelled.is_none(),
            "the internal store record has no retained source"
        );
        assert!(
            direct_events.iter().all(|event| !matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if *name == "solve premise surface at recorded states"
                        || *name == "solve premise surface across recorded states"
            )),
            "direct premise resolution searched unrelated history"
        );
        // An explicitly retained store equality remains a source rewrite.
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: _,
                right: stored,
            },
            true,
        ) = &facts[0]
        else {
            unreachable!()
        };
        let recorded_state = state
            .clone()
            .with_local("second", ProgramValue::Int32(stored.as_ref().clone()));
        let mut recorded_surfaces = SurfacePropositionMap::default();
        recorded_surfaces
            .record_lowering(&alias_surface, &facts[0])
            .unwrap();
        let recorded = Proof::for_fixed_state_goal_with_requirements(
            "retained store source",
            0,
            &facts,
            facts[0].clone(),
            ParameterBinding::default(),
            FixedStateFrame::new(&recorded_state, &recorded_state, None, &retained_states),
            Some(&anchor),
            &recorded_surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        assert_eq!(
            recorded
                .lower_surface_proposition_direct(&alias_surface, "retained store source control")
                .unwrap(),
            facts[0]
        );
        assert!(
            crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&recorded)
                .is_some_and(|proof| proof.is_complete()),
            "a retained store source must remain usable"
        );
        let alias = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(reads[0].clone()),
                right: Box::new(reads[1].clone()),
            },
            true,
        );
        let mut alias_facts = facts.clone();
        alias_facts.push(alias.clone());
        let mut alias_surfaces = SurfacePropositionMap::default();
        alias_surfaces
            .record_lowering(&alias_surface, &alias)
            .unwrap();
        for (premises, expected) in [(&alias_facts, true), (&facts, false)] {
            let proof = Proof::for_fixed_state_goal_with_requirements(
                "different reads remain usable",
                0,
                premises,
                alias.clone(),
                ParameterBinding::default(),
                FixedStateFrame::new(&state, &state, None, &retained_states),
                Some(&anchor),
                &alias_surfaces,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
                &[],
                &[],
                &[],
            );
            assert_eq!(
                crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(proof))
                    .is_some_and(|proof| proof.is_complete()),
                expected
            );
        }
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 5 + 64),
        "store fact filtering exceeded input growth: {samples:?}"
    );
}

fn check_impossible_offset_rewrite_search(already_intrinsic: bool, native: bool) {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let scalar = |index: usize| {
        ContractExpression::ProgramExpression(ProgramExpression::Variable(format!("offset{index}")))
    };
    let integer = |index| ContractExpression::Call {
        name: "to_integer".into(),
        arguments: vec![scalar(index)],
    };
    let source_equal = |left, right| ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    };
    let mut costs = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let words = (0..=size)
            .map(|index| MachineTerm::Variable(Variable(8_987_000 + index as u64)))
            .collect::<Vec<_>>();
        let terms = words
            .iter()
            .map(|word| {
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::UInt32,
                    word.clone(),
                ))
            })
            .collect::<Vec<_>>();
        let mut surfaces = SurfacePropositionMap::default();
        let facts = (1..=size)
            .map(|index| {
                let fact = Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(words[0].clone()),
                        right: Box::new(words[index].clone()),
                    },
                    true,
                );
                surfaces
                    .record_lowering(&source_equal(scalar(0), scalar(index)), &fact)
                    .unwrap();
                fact
            })
            .collect::<Vec<_>>();
        let base = usize::from(!already_intrinsic);
        let right = IntegerTerm::Add(
            terms[base].clone().into(),
            IntegerTerm::Constant(1.into()).into(),
        );
        let goal = Proposition::ConditionIs(
            if native {
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(words[0].clone()),
                    right: Box::new(binary_node!(
                        Int32,
                        Add,
                        Box::new(words[base].clone()),
                        Box::new(MachineTerm::constant(1)),
                    )),
                }
            } else {
                ConditionTerm::IntegerEqual(terms[0].clone().into(), right.into())
            },
            true,
        );
        let surface_goal = source_equal(
            if native { scalar(0) } else { integer(0) },
            ContractExpression::Add(
                Box::new(if native { scalar(base) } else { integer(base) }),
                Box::new(ContractExpression::IntegerLiteral("1".into())),
            ),
        );
        let context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: Default::default(),
            memory: Memory::new(),
            values: words
                .iter()
                .enumerate()
                .map(|(index, word)| (format!("offset{index}"), ProgramValue::UInt32(word.clone())))
                .collect(),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements: surfaces,
        };
        let root = Proof::for_pure_goal_with_surface(
            "intrinsically impossible integer offset",
            &facts,
            goal.clone(),
            Some(surface_goal.clone()),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure(&(root))
        });
        assert!(closed.is_none(), "offset equality must remain rejected");
        costs.push(work);

        let mut contradictory = facts.clone();
        contradictory.push(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ));
        let contradictory_context = PureTheoremContext {
            requires: contradictory.clone(),
            ..context.clone()
        };
        let unreachable = Proof::for_pure_goal_with_surface(
            "unreachable integer offset",
            &contradictory,
            goal,
            Some(surface_goal),
            &contradictory_context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        assert!(
            crate::kernel::search::ProofSearch::try_solve_closure(&(unreachable))
                .ok()
                .flatten()
                .is_some_and(|proof| proof.is_complete()),
            "an explicit contradiction must still close an unreachable goal"
        );
    }
    let bounded = costs
        .iter()
        .zip([8usize, 16, 32, 64])
        .all(|(work, size)| *work <= size * 128 + 1024);
    assert!(
        bounded,
        "already intrinsic={already_intrinsic}: refuted search used irrelevant aliases: {costs:?}"
    );
}

#[test]
fn impossible_integer_offset_rewrite_search_stays_local() {
    check_impossible_offset_rewrite_search(true, false);
}

#[test]
fn rewritten_impossible_integer_offset_search_stays_local() {
    check_impossible_offset_rewrite_search(false, false);
}

#[test]
fn impossible_native_offset_rewrite_search_stays_local() {
    check_impossible_offset_rewrite_search(true, true);
    check_impossible_offset_rewrite_search(false, true);
}

#[test]
fn deferred_terminal_tactics_share_ambient_bindings_without_map_work() {
    use crate::persistent::{measure_persistent_work, persistent_node_allocations};
    let mut baseline_work = None;
    for size in [4, 16, 64, 256] {
        let bindings = (0..size).fold(PersistentMap::default(), |bindings, i| {
            bindings.with_inserted(
                format!("local_{i}"),
                ContractExpression::IntegerLiteral(i.to_string()),
            )
        });
        let mut execution = ExecutionProofState::at_entry(
            ExecutionState::new(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        );
        let before = persistent_node_allocations();
        let (_, work) = measure_persistent_work(|| {
            for index in 0..8 {
                execution.presentation.defer_post_execution(
                    index,
                    index,
                    PostExecutionTactic::Solve,
                    Some(bindings.clone()),
                );
            }
        });
        assert_eq!(
            persistent_node_allocations() - before,
            0,
            "ambient {size}: scope capture copied map nodes"
        );
        assert_eq!(
            work,
            *baseline_work.get_or_insert(work),
            "ambient bindings must not change cursor work"
        );
        for deferred in execution.presentation.post_execution_tactics.iter() {
            assert!(
                deferred
                    .lexical_bindings
                    .as_ref()
                    .unwrap()
                    .shares_root_with(&bindings)
            );
        }
        eprintln!("ambient bindings={size}, cursor work={work}");
    }
}

#[test]
fn typed_intro_records_bound_spellings_without_scanning_ambient_facts() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let context = pure_identity_fixture();
    let truth = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let surface_truth = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
    };
    let samples = [4, 16, 64, 256].map(|size| {
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_pure_surface_goal(
            "typed intro spelling",
            &facts,
            Proposition::ForAll {
                name: Default::default(),
                var: Variable(0),
                sort: Sort::machine_integer(MachineIntegerType::UInt8),
                body: Box::new(truth.clone()),
            },
            ClickProposition::ForAll {
                click_type: ClickType::Program(crate::languages::interface::InterfaceType::UInt8),
                name: "byte".into(),
                written_name: None,
                body: Box::new(surface_truth.clone()),
            },
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.apply_intro(Some("bound")).unwrap()
        });
        // A `uint8` binder is a value of its own format: its range is the
        // format's, so intro adds no bound fact to spell.
        assert_eq!(next.state().added_facts().len(), 0);
        for fact in next.state().added_facts() {
            assert_eq!(next.locals().surface_facts.surfaces(fact).count(), 1);
        }
        work
    });
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 128),
        "typed intro spelling work: {samples:?}"
    );
}

#[test]
fn smart_goal_spelling_does_not_scan_ambient_facts_or_same_value_names() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let term = MachineTerm::Variable(Variable(8_199_901));
    let goal = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: Box::new(term.clone()),
            right: Box::new(MachineTerm::constant(1)),
        },
        true,
    );
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024] {
        let mut state = ExecutionState::new();
        for index in 0..size {
            state = state
                .with_local(
                    format!("alias_{index:04}"),
                    ProgramValue::Int32(term.clone()),
                )
                .with_local(format!("unrelated_{index:04}"), int32(index));
        }
        let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        let root = Proof::for_fixed_state_goal(
            "structural smart goal",
            0,
            &facts,
            goal.clone(),
            ParameterBinding::default(),
            &state,
            &state,
            &retained_states,
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        let event = crate::instrumentation::TacticEvent {
            source_tactic_path: None,
            claim: "structural smart goal".into(),
            tactic_index: 0,
            tactic_name: "solve".into(),
            class: "smart".into(),
            statement_index: 0,
            source_index: 0,
        };
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticStarted(
            event.clone(),
        ));
        let (spelled, work) =
            crate::instrumentation::measure_deterministic_work(|| root.spelled_goal(&goal));
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFinished {
            tactic: event,
            elapsed: std::time::Duration::ZERO,
            work: 0,
        });
        let spelled = spelled.expect("a smart goal retains its structural name");
        assert_eq!(
            root.lower_surface_proposition_direct(&spelled, "round trip")
                .unwrap(),
            goal
        );
        // Merely naming the goal must not prove its unsupported inequality.
        assert!(!root.facts().contains(&goal));
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(samples.windows(2).all(|p| p[1] <= p[0] + 32), "{samples:?}");
}

#[test]
fn exact_goal_solve_stops_at_known_as_related_and_unrelated_facts_grow() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let variable = MachineTerm::Variable(Variable(8_180_000));
    let state = ExecutionState::new().with_local("x", ProgramValue::Int32(variable.clone()));
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let bound = |variable: MachineTerm, limit| {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(variable),
                right: Box::new(MachineTerm::constant(limit)),
            },
            true,
        )
    };
    let goal = bound(variable.clone(), 3);
    let surface = ClickProposition::Comparison {
        left: ContractExpression::ProgramExpression(ProgramExpression::Variable("x".into())),
        operator: ComparisonOperator::LessThan,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(3))),
    };
    for related in [false, true] {
        let mut previous = None;
        for size in [16_u32, 64, 256, 1024] {
            let mut facts = (0..size)
                .map(|index| {
                    bound(
                        if related {
                            variable.clone()
                        } else {
                            MachineTerm::Variable(Variable(9_000_000 + u64::from(index)))
                        },
                        100 + index,
                    )
                })
                .collect::<Vec<_>>();
            facts.push(bound(variable.clone(), 2)); // Also offers a longer derivation.
            facts.push(goal.clone());
            let root = Proof::for_fixed_state_frontier(
                "exact solve",
                0,
                &facts,
                ParameterBinding::default(),
                FixedStateFrame::new(&state, &state, None, &retained_states),
                &surfaces,
                SpecDefinitions::new(&predicates, &functions),
                &theorems,
                &[],
                &[],
            );
            let scope = root.driver().open_have(surface.clone()).unwrap();
            let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
                scope.driver().try_solve_closure().unwrap().unwrap()
            });
            assert_eq!(closed.body().certificate().steps(), &[ProofStep::Known]);
            assert!(root.certificate().steps().is_empty());
            if let Some(previous) = previous {
                assert!(
                    work <= previous + 128,
                    "related={related}, size={size}: {work} after {previous}"
                );
            }
            previous = Some(work);
        }
    }
}

#[test]
fn fixed_state_application_proves_premises_and_replays_explicitly() {
    let file = crate::surface::parse(
        "theorem nonnegative(n: int32) { requires n >= 0; ensures n >= 0 by known(); }",
    )
    .unwrap();
    let parsed = syntax::parse_function("int32 identity(int32 x) { return x; }").unwrap();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let definitions = SpecDefinitions::new(&predicates, &functions);
    let theorems = TheoremEnvironment::new(file.theorem_definitions());
    let value = ProgramValue::Int32(MachineTerm::Variable(Variable(8_900_000)));
    let state = ExecutionState::new().with_local("x", value.clone());
    let arguments = vec![ProgramExpression::Value(value)];
    let binding = ParameterBinding::new(parsed.parameters(), &arguments);
    let retained_states = RecordedStates::new();
    let premise = ClickProposition::Comparison {
        left: ContractExpression::Binding("x".into()),
        operator: ComparisonOperator::GreaterThan,
        right: ContractExpression::IntegerLiteral("0".into()),
    };
    let goal = ClickProposition::Comparison {
        left: ContractExpression::Binding("x".into()),
        operator: ComparisonOperator::GreaterEqual,
        right: ContractExpression::IntegerLiteral("0".into()),
    };
    let lower = |p: &ClickProposition| {
        lower_fixed_state_proposition_with_assumptions(
            p,
            &PureFactContext::new(),
            binding,
            FixedStateFrame::new(&state, &state, None, &retained_states),
            definitions,
        )
        .unwrap()
    };
    let premise_kernel = lower(&premise);
    let goal_kernel = lower(&goal);
    let mut forms = SurfacePropositionMap::default();
    forms.record_lowering(&premise, &premise_kernel).unwrap();
    let application = TheoremApplication {
        name: "nonnegative".into(),
        arguments: vec![ContractExpression::Binding("x".into())],
    };
    let mut baseline = None;
    for size in [4u32, 16, 64] {
        let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
        facts.push(premise_kernel.clone());
        let root = Proof::for_fixed_state_goal(
            "fixed theorem obligations",
            0,
            &facts,
            goal_kernel.clone(),
            binding,
            &state,
            &state,
            &retained_states,
            &forms,
            definitions,
            &theorems,
            &[],
            &[],
        );
        let (prepared, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.prepare_theorem_application(&application)
        });
        assert_eq!(prepared.unwrap().obligations.len(), 1);
        assert!(
            work <= *baseline.get_or_insert(work),
            "{size} facts increased preparation work to {work}"
        );
        let completed = root
            .driver()
            .apply_theorem_application(&application)
            .unwrap();
        assert!(completed.is_complete());
        let tactics = completed.certificate().to_proof_tactics();
        assert!(matches!(tactics.first(), Some(ProofTactic::Have(_))));
        let replay = crate::surface::without_implicit_solve(|| {
            root.driver().try_authoritative_linear_script(&tactics)
        })
        .unwrap()
        .unwrap();
        assert!(replay.is_complete());
        assert!(root.certificate().steps().is_empty());
        let missing = Proof::for_fixed_state_goal(
            "missing fixed premise",
            0,
            &[],
            goal_kernel.clone(),
            binding,
            &state,
            &state,
            &retained_states,
            &forms,
            definitions,
            &theorems,
            &[],
            &[],
        );
        assert!(
            missing
                .driver()
                .apply_theorem_application(&application)
                .is_err()
        );
        assert!(missing.certificate().steps().is_empty());
    }
}

#[test]
fn cold_theorem_application_ignores_declaration_proof_length() {
    let mut baseline = None;
    let mut previous_proof_work = 0;
    for size in [4, 16, 64] {
        let source = format!(
            "theorem identity<T>(x: T) {{ requires x == x; ensures x == x by {{ {} known(); }} }}",
            "have x == x by solve(); ".repeat(size)
        );
        // Verification is declaration work; measure only the application below.
        crate::surface::verify_c_sources(&source, &[]).unwrap();
        let file = crate::surface::parse(&source).unwrap();
        // Sensitivity control: the removed proof-instantiation path grows with
        // this same input, while complete explicit application must stay flat.
        let substitution = std::collections::BTreeMap::from([(
            "T".into(),
            ClickType::Program(crate::languages::interface::InterfaceType::Int32).into(),
        )]);
        let (declaration, proof_work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::generics::instantiate_theorem(
                &file.theorem_definitions()[0],
                &substitution,
            )
        });
        declaration.unwrap();
        assert!(proof_work > previous_proof_work);
        previous_proof_work = proof_work;
        let parsed = syntax::parse_function("int32 identity(int32 x) { return x; }").unwrap();
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let definitions = SpecDefinitions::new(&predicates, &functions);
        let theorems = TheoremEnvironment::new(file.theorem_definitions());
        let value = ProgramValue::Int32(MachineTerm::Variable(Variable(8_900_000)));
        let state = ExecutionState::new().with_local("x", value.clone());
        let arguments = vec![ProgramExpression::Value(value)];
        let binding = ParameterBinding::new(parsed.parameters(), &arguments);
        let retained_states = RecordedStates::new();
        let premise = ClickProposition::Comparison {
            left: ContractExpression::Binding("x".into()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Binding("x".into()),
        };
        let goal = lower_fixed_state_proposition_with_assumptions(
            &premise,
            &PureFactContext::new(),
            binding,
            FixedStateFrame::new(&state, &state, None, &retained_states),
            definitions,
        )
        .unwrap();
        let mut forms = SurfacePropositionMap::default();
        forms.record_lowering(&premise, &goal).unwrap();
        let facts = vec![goal.clone()];
        let root = Proof::for_fixed_state_goal(
            "cold generic application",
            0,
            &facts,
            goal,
            binding,
            &state,
            &state,
            &retained_states,
            &forms,
            definitions,
            &theorems,
            &[],
            &[],
        );
        let application = TheoremApplication {
            name: "identity".into(),
            arguments: vec![ContractExpression::Binding("x".into())],
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.apply_theorem_using(&application, std::slice::from_ref(&premise))
        });
        result.unwrap();
        assert_eq!(work, *baseline.get_or_insert(work), "proof length {size}");
        let (repeated, repeated_work) = crate::instrumentation::measure_deterministic_work(|| {
            root.apply_theorem_using(&application, std::slice::from_ref(&premise))
        });
        repeated.unwrap();
        assert_eq!(
            work, repeated_work,
            "cold and repeated applications must match"
        );
    }
}

#[test]
fn retained_conditional_premise_spelling_does_not_search_state_history() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let a = MachineTerm::Variable(Variable(8_179_900));
    let b = MachineTerm::Variable(Variable(8_179_901));
    let result = MachineTerm::Variable(Variable(8_179_902));
    let conditional = MachineTerm::If {
        condition: Box::new(ConditionTerm::unsigned_less_equal(a.clone(), b.clone())),
        then_term: Box::new(a.clone()),
        else_term: Box::new(b.clone()),
    };
    let observe = |word| {
        crate::kernel::SharedIntegerTerm::from(crate::kernel::IntegerTerm::Machine(
            crate::kernel::SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, word),
        ))
    };
    let condition = ConditionTerm::IntegerEqual(observe(result.clone()), observe(conditional));
    let fact = Proposition::ConditionIs(condition.clone(), true);
    let state = ExecutionState::new()
        .with_local("a", ProgramValue::UInt32(a))
        .with_local("b", ProgramValue::UInt32(b))
        .with_local("chosen", ProgramValue::UInt32(result));
    let entry = state.clone();
    let surfaces = SurfacePropositionMap::default();
    let facts = [fact.clone()];
    let mut base = None;
    for size in [4usize, 16, 64] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                state.clone(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(size - 1),
            kind: ProgramPointKind::Entry,
        };
        let root = Proof::for_fixed_state_goal_with_requirements(
            "retained conditional spelling",
            0,
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ParameterBinding::default(),
            FixedStateFrame::new(&entry, &state, None, &retained_states),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
            &[],
        );
        let ((spelled, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::available_surface_fact(
                    &root,
                    &surfaces,
                    Some(&anchor),
                    &fact,
                )
            })
        });
        let spelled = spelled.expect("the selected conditional equality has a source form");
        let lowered = root
            .lower_surface_proposition_direct(&spelled, "conditional round trip")
            .unwrap();
        assert!(
            crate::kernel::proof::fact_reasoning::listed_equality_fact_is_available(
                &fact,
                std::slice::from_ref(&lowered),
            )
        );
        assert!(
            !crate::kernel::proof::fact_reasoning::listed_equality_fact_is_available(
                &Proposition::ConditionIs(condition.clone(), false),
                &[lowered],
            )
        );
        assert!(
            events.iter().all(|event| !matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if *name == "solve premise surface at recorded states"
                        || *name == "solve premise surface across recorded states"
            )),
            "size={size}: selected conditional spelling searched history"
        );
        let baseline = *base.get_or_insert(work);
        assert!(
            work <= baseline + 128,
            "size={size}, work={work}, baseline={baseline}"
        );
    }
}

#[test]
fn proof_binding_name_production_and_queries_follow_only_changed_bindings() {
    let binding = |variable| {
        ContractExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::typed_pointer(
                Pointer::symbolic(Variable(variable)),
                ProgramType::Int32Pointer,
            ),
        ))
    };
    let mut samples = Vec::new();
    for size in [8_u64, 32, 128, 512] {
        let mut locals = ProofLocals::default();
        let (((), production), _) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    locals.set_values(
                        locals
                            .values
                            .with_inserted(format!("binder{index:05}"), binding(9_810_000 + index)),
                    );
                    // Grow the selected variable's alias set too.
                    locals.set_values(
                        locals
                            .values
                            .with_inserted(format!("alias{index:05}"), binding(9_820_000)),
                    );
                    locals.set_integer_values(locals.integer_values.with_inserted(
                        format!("integer{index:05}"),
                        crate::kernel::SpecIntegerExpression::Term(IntegerTerm::Variable(
                            Variable(9_840_000 + index),
                        )),
                    ));
                    locals.set_algebraic_values(locals.algebraic_values.with_inserted(
                        format!("model{index:05}"),
                        crate::kernel::SpecAlgebraicExpression {
                            algebraic_type: crate::kernel::AlgebraicType::parameter("T".into()),
                            node: crate::kernel::SpecAlgebraicExpressionNode::Variable(Variable(
                                9_850_000 + index,
                            )),
                        },
                    ));
                }
            })
        });
        assert_eq!(production, 4 * size as usize);
        let parent = locals.clone();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    locals.value_names.name(Variable(9_810_000)),
                    Some("binder00000")
                );
                assert_eq!(
                    locals.value_names.name(Variable(9_820_000)),
                    Some("alias00000")
                );
                assert_eq!(locals.value_names.name(Variable(9_830_000)), None);
                locals.set_values(
                    locals
                        .values
                        .with_inserted("new".into(), binding(9_830_000)),
                );
                assert_eq!(locals.value_names.name(Variable(9_830_000)), Some("new"));
                locals.set_values(parent.values.clone());
                assert_eq!(locals.value_names.name(Variable(9_830_000)), None);
                assert_eq!(parent.value_names.name(Variable(9_830_000)), None);
            })
        });
        assert_eq!(work, 8);
        samples.push(map_work);
    }
    assert!(
        samples[3] < samples[0] * 4 + 128,
        "binding update/query scanned a scope: {samples:?}"
    );
}
