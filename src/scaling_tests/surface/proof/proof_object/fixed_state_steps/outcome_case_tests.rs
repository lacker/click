// Scaling tests of `src/surface/proof/proof_object/fixed_state_steps.rs` (module `outcome_case_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn nested_case_partition_reuses_decisions_without_relowering_or_forking() {
    for size in [4, 8, 16, 32] {
        let conditions = (0..size)
            .map(|index| ClickProposition::PredicateCall {
                name: format!("case_{index}"),
                arguments: Vec::new(),
            })
            .collect::<Vec<_>>();
        let nodes = conditions
            .iter()
            .enumerate()
            .map(|(index, condition)| {
                OutcomeNode::Case(OutcomeCase {
                    scope: None,
                    lexical_bindings: None,
                    occurrence: index,
                    fingerprint: ExecutionBranchDecisions::key(condition),
                    condition,
                    disjunction: false,
                    execution_route: None,
                    arms: [None, (index + 1 < size).then_some(index + 1)],
                })
            })
            .collect::<Vec<_>>();
        let mut decisions = ExecutionBranchDecisions::default();
        // Execution can record inner C decisions before an enclosing
        // proof case is joined. Lookup must not depend on history order.
        for condition in conditions.iter().rev() {
            decisions.push(ExecutionBranchDecision {
                fingerprint: std::sync::OnceLock::new(),
                condition: condition.clone(),
                value: false,
            });
        }
        let provenance = OutcomeProvenance {
            terminal_statement_case: None,
            checked_leaf_facts: None,
            loop_return: None,
            call_routes: Vec::new(),
            branch_decisions: decisions,
            surface_propositions: SurfacePropositionMap::default(),
            recorded_states: RecordedStates::default(),
            generated_load_bindings: PersistentMap::default(),
            match_arms: PersistentMap::default(),
            case_obligations: PersistentMap::default(),
            checked_haves: PersistentMap::default(),
        };
        let root = ProofFacts::default();
        let mut leaves = 0;
        let (fork, work) = crate::instrumentation::measure_deterministic_work(|| {
            partition_outcome_cases(
                &nodes,
                Some(0),
                &root,
                &root,
                &mut Vec::new(),
                provenance,
                &|_, _, _| panic!("a recorded case must not be lowered again"),
                &|_, _, _, _| unreachable!("the partition has no `match`"),
                &|_, _, _, _, _| unreachable!("recorded decisions need no proof"),
                &mut |facts, provenance| {
                    assert!(facts.is_empty(), "no invented case facts");
                    assert_eq!(provenance.branch_decisions.iter().count(), size);
                    leaves += 1;
                },
            )
            .unwrap()
        });
        assert!(matches!(fork, OutcomeEvidenceFork::Keep));
        assert_eq!(leaves, 1, "only the checked false path is retained");
        assert!(
            work <= size * 128,
            "linear case work at size {size}: {work}"
        );
    }
}

#[test]
fn branch_decision_lookup_does_not_scan_history_and_refuses_conflicts() {
    let selected = ClickProposition::PredicateCall {
        name: "selected".to_string(),
        arguments: Vec::new(),
    };
    let mut previous_work = None;
    for size in [8, 32, 128, 512] {
        let mut decisions = ExecutionBranchDecisions::default();
        decisions.push(ExecutionBranchDecision {
            fingerprint: std::sync::OnceLock::new(),
            condition: selected.clone(),
            value: false,
        });
        for index in 0..size {
            decisions.push(ExecutionBranchDecision {
                fingerprint: std::sync::OnceLock::new(),
                condition: ClickProposition::PredicateCall {
                    name: format!("unrelated_{index}"),
                    arguments: Vec::new(),
                },
                value: true,
            });
        }
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            decisions.value(&selected).unwrap()
        });
        assert_eq!(value, Some(false));
        if let Some(previous) = previous_work {
            assert!(
                work <= previous * 2,
                "lookup grew with history: {previous} -> {work}"
            );
        }
        previous_work = Some(work);
        decisions.push(ExecutionBranchDecision {
            fingerprint: std::sync::OnceLock::new(),
            condition: selected.clone(),
            value: true,
        });
        assert!(decisions.value(&selected).is_err());
    }
}

#[test]
fn flat_haves_before_a_case_use_linear_work_and_constant_traversal_stack() {
    for size in [32, 128, 512] {
        let have = ProofHave {
            proposition: ClickProposition::PredicateCall {
                name: "proved".into(),
                arguments: vec![],
            },
            proof: SourceProof::Default,
        };
        let source = DeferredPostExecutionTactic {
            lexical_bindings: None,
            tactic_index: 0,
            source_index: 0,
            tactic: PostExecutionTactic::Have(have),
        };
        let nodes = (0..size)
            .map(|index| OutcomeNode::Have {
                scope: None,
                occurrence: index,
                source: &source,
                next: (index + 1 < size).then_some(index + 1),
            })
            .collect::<Vec<_>>();
        let provenance = OutcomeProvenance {
            terminal_statement_case: None,
            checked_leaf_facts: None,
            loop_return: None,
            call_routes: vec![],
            branch_decisions: ExecutionBranchDecisions::default(),
            match_arms: PersistentMap::default(),
            case_obligations: PersistentMap::default(),
            checked_haves: PersistentMap::default(),
            surface_propositions: SurfacePropositionMap::default(),
            recorded_states: RecordedStates::default(),
            generated_load_bindings: PersistentMap::default(),
        };
        let root = ProofFacts::default();
        let calls = std::cell::Cell::new(0);
        let mut leaves = 0;
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            partition_outcome_cases(
                &nodes,
                Some(0),
                &root,
                &root,
                &mut vec![],
                provenance,
                &|_, _, _| unreachable!(),
                &|_, _, _, _| unreachable!(),
                &|_, written, _, _, _| {
                    assert!(written.is_some());
                    calls.set(calls.get() + 1);
                    Ok((
                        Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                        ProofCertificate::from_steps(vec![]).unwrap(),
                    ))
                },
                &mut |facts, provenance| {
                    assert_eq!(facts.len(), size);
                    assert!(provenance.checked_haves.get(&(size - 1)).is_some());
                    leaves += 1;
                },
            )
            .unwrap();
        });
        assert_eq!(calls.get(), size);
        assert_eq!(leaves, 1);
        assert!(work <= size * 256, "linear prefix work at {size}: {work}");
    }
}
