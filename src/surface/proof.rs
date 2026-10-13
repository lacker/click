use super::diagnostics::*;
use super::validation::{collect_called_predicates, collect_resource_count_families, tactic_name};
use super::*;
use crate::kernel::{ExecutionFactSource, ExecutionFacts};
use std::sync::Arc;

mod attempt;
mod claim_proofs;
#[cfg(test)]
pub(in crate::surface) use claim_proofs::count_flat_proof_units;
pub(in crate::surface) use fixed_state_proofs::{
    evaluate_c_fragment_through_kernel, evaluate_fixed_state_array_ref_through_kernel,
    evaluate_fixed_state_expression_through_kernel, evaluate_resource_argument_through_kernel,
    evaluate_resource_fragment_through_kernel, lower_fixed_state_proposition_through_kernel,
    lower_fixed_state_proposition_through_kernel_recording_introductions_with_bound_array_memories_and_facts,
    lower_fixed_state_proposition_through_kernel_with_opaque_calls,
};
mod cursor_execution;
mod execution_planning;
pub(in crate::surface) mod fact_reasoning;
mod fixed_state_proofs;
mod language_context;
mod proof_object;

#[cfg(test)]
pub(in crate::surface) use proof_object::{
    count_checked_execution_interface_joins, count_checked_expanded_execution_ifs,
    count_finalization_view_constructions,
};
mod checked_drivers;
mod execution_state;
mod guarded_consequents;
mod pure_theorems;
mod resources;
mod signed_definedness;
mod smart_closures;
mod smart_execution;
mod solver_bridges;
mod structural;
mod surface_certificates;
mod surface_construction;
mod surface_lowering;
mod surface_synthesis;
mod theorem_application;
mod timing;
mod uint32_representation;
mod wide_arithmetic;
use crate::kernel::fresh_int32_variable_for_propositions;
use crate::kernel::proof::{
    ExceptionalContinuation, ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind,
    FrontierPosition, LoopControlExit, PersistentOrderedSet, PersistentSequence,
    ProofExecutionContinuation, ProofFacts, SharedVec, old_reference_state,
    quantified_equivalence_index_key,
};

pub(in crate::surface) use crate::kernel::proof::{
    SnapshotBlindPropositionKey, snapshot_blind_proposition_key,
};
use claim_proofs::finish_ordered_proof;
pub(super) use claim_proofs::{
    prove_claim_by_tactics, prove_claims_by_grouped_auto, prove_claims_by_grouped_script,
};
use cursor_execution::*;

#[cfg(test)]
pub(in crate::surface) fn count_planning_statement_transitions<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    cursor_execution::count_planning_statement_transitions(operation)
}
#[cfg(test)]
pub(in crate::surface) fn collect_planning_statement_transitions<R>(
    operation: impl FnOnce() -> R,
) -> (R, Vec<(String, usize, String)>) {
    cursor_execution::collect_planning_statement_transitions(operation)
}
use checked_drivers::*;
use execution_planning::*;
pub(super) use execution_planning::{
    StatementFactTransportPolicy, StatementPrerequisitePolicy, certified_statement_transitions,
};
use execution_state::*;
pub(super) use execution_state::{
    capture_c0_proof_site_expansion, capture_c0_tactic_expansion,
    capture_prepared_proof_site_expansion, capture_prepared_tactic_expansion,
    capture_project_proof_site_expansion, capture_project_tactic_expansion,
};
#[cfg(test)]
pub(super) use fact_reasoning::describe_condition_search_miss;
use fact_reasoning::*;
pub(super) use fact_reasoning::{
    condition_polarity_equivalent, exactly_available_fact, search_condition_derivation,
};
use fixed_state_proofs::*;
use language_context::*;
use proof_object::*;
#[cfg(test)]
pub(in crate::surface) use pure_theorems::PROVED_THEOREMS;
pub(super) use pure_theorems::{
    assumed_theorem_certification_authorities, is_kernel_standard_theorem_name,
    pure_theorem_array_refs, pure_theorem_parameter_values, verify_concrete_theorem_definition,
    verify_theorem_definition, verify_theorem_definitions,
};
#[cfg(test)]
use pure_theorems::{lower_pure_theorem_proposition, pure_theorem_context};
pub(super) use resources::instantiate_composite_resource_body_resources;
use resources::*;
use structural::*;
use surface_certificates::*;
use surface_construction::*;
#[cfg(test)]
use surface_synthesis::{SURFACE_SYNTHESIS_DEPTH_LIMIT, bitvector_term_is_load_free};
pub(super) use surface_synthesis::{
    callback_source_name, synthesize_surface_equality_across_points, synthesize_surface_proposition,
};
use surface_synthesis::{
    surface_synthesis_exhaustion_description, surface_synthesis_failure,
    synthesize_surface_machine_expression,
    synthesize_surface_proposition_with_bound_variable_names,
};
use theorem_application::*;
use timing::TacticTiming;
pub(super) use timing::{SourceSiteKind, source_site_kind};

type NextTopLevelStatement = (CState, CState, CStatement, Option<CStatement>);

fn check_verification_deadline() -> Result<(), ClickError> {
    if crate::instrumentation::deadline_exceeded() {
        Err(ClickError::new(format!(
            "verification budget exhausted inside {}",
            crate::instrumentation::deadline_context()
        )))
    } else {
        Ok(())
    }
}

/// Language-facing diagnostic adapter for the kernel's instantiated-guard
/// check. Surface certificate planning shares the same checked rule without
/// gaining successor authority.
pub(super) fn discharge_instantiated_guards(
    instantiated: Proposition,
    premises: &[Proposition],
) -> Result<(Vec<Proposition>, Proposition), String> {
    crate::kernel::proof::fact_reasoning::discharge_instantiated_guards(instantiated, premises)
        .map_err(|error| {
            format_forall_int32_instantiation_error(error, ParameterBinding::default())
        })
}

pub(super) fn format_forall_int32_instantiation_error(
    error: crate::kernel::proof::fact_reasoning::ForallInt32InstantiationError,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    use crate::kernel::proof::fact_reasoning::ForallInt32InstantiationError as Error;
    match error {
        Error::RequiresUniversal => {
            "`instantiate` requires a universally quantified fact".to_string()
        }
        Error::UnsupportedSort => "`instantiate` supports only int32 universals".to_string(),
        // Spelled, not named by kind: "signed less-or-equal is true" does not
        // tell a reader which premise to supply, and a premise the hypothesis
        // owes is exactly what they have to write down.
        Error::MissingGuard(missing) => format!(
            "instantiated premise `{}` does not follow from the listed evidence",
            crate::surface::diagnostics::describe_pure_fact_spelled(&missing, parameter_binding),
        ),
        Error::KernelRejected => "kernel rejected the `instantiate` application".to_string(),
        Error::InvalidTheorem => "invalid universal instantiation theorem".to_string(),
        Error::ChangedQuantifiedPremise => {
            "universal instantiation changed its quantified premise".to_string()
        }
        Error::OmittedGuard => "universal instantiation omitted a discharged premise".to_string(),
        Error::ChangedGuard => "universal instantiation changed a discharged premise".to_string(),
        Error::UnexpectedConclusion => {
            "universal instantiation produced an unexpected conclusion".to_string()
        }
    }
}

pub(in crate::surface) fn normalizes_context_free(goal: &Proposition) -> bool {
    crate::kernel::proof::fact_reasoning::normalizes_context_free(goal)
}

#[cfg(test)]
mod certificate_tests {
    use super::*;

    #[test]
    fn local_index_surface_candidates_reject_nested_loads() {
        let pointer = Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(CMemory::new()),
            Box::new(pointer),
            crate::kernel::LoadKind::Bits32,
        );

        assert!(bitvector_term_is_load_free(&Bitvector32Term::Add(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Constant(1)),
        )));
        assert!(!bitvector_term_is_load_free(&Bitvector32Term::Add(
            Box::new(load),
            Box::new(Bitvector32Term::Constant(1)),
        )));
    }

    #[test]
    fn surface_synthesis_rejects_too_deep_terms_with_a_bounded_reason() {
        let mut term = Bitvector32Term::Variable(Variable(1));
        for _ in 0..=SURFACE_SYNTHESIS_DEPTH_LIMIT {
            term = Bitvector32Term::Add(Box::new(term), Box::new(Bitvector32Term::Constant(1)));
        }
        let proposition = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(term), Box::new(Bitvector32Term::Constant(0))),
            true,
        );

        assert!(
            synthesize_surface_proposition(
                &proposition,
                ParameterBinding::default(),
                &CState::new()
            )
            .is_none()
        );
        let reason = surface_synthesis_failure("could not reconstruct test fact", &proposition);
        assert!(reason.contains("bounded bitvector search"), "{reason}");
        assert!(!reason.contains("Variable("), "{reason}");
    }

    #[test]
    fn snapshot_annotation_rejects_deep_logic_without_using_the_native_stack() {
        let mut surface = ClickProposition::Comparison {
            left: ContractExpression::CBinding("value".to_string()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(0),
            ))),
        };
        for _ in 0..=SNAPSHOT_ANNOTATION_DEPTH_LIMIT {
            surface = ClickProposition::Not(Box::new(surface));
        }
        let point = ProgramPointRef {
            region: CodeRegionRef::Statement(0),
            kind: ProgramPointKind::Entry,
        };

        let error = surface_at_snapshot(&surface, &point)
            .expect_err("deep snapshot annotation must stop structurally");
        assert!(
            error.message().contains("structural depth bound"),
            "{error:?}"
        );
    }

    #[test]
    fn snapshot_index_finds_a_late_exact_selector_inside_a_quantifier() {
        let early_memory = CMemory::new().with_block("early", 4);
        let target_memory = CMemory::new().with_block("target", 4);
        let pointer = Pointer {
            block: "target".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let kernel = Proposition::ForAll {
            var: Variable(7),
            sort: Sort::Bitvector32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(target_memory.clone()),
                        Box::new(pointer),
                        crate::kernel::LoadKind::Bits32,
                    )),
                    Box::new(Bitvector32Term::Variable(Variable(7))),
                ),
                true,
            )),
        };
        let early = ProgramPointRef {
            region: CodeRegionRef::Statement(0),
            kind: ProgramPointKind::Entry,
        };
        let late = ProgramPointRef {
            region: CodeRegionRef::Statement(99),
            kind: ProgramPointKind::Entry,
        };
        let mut states = RecordedSnapshots::new();
        states.insert(early, CState::new().with_memory(early_memory));
        states.insert(late.clone(), CState::new().with_memory(target_memory));

        let (exact, compatible) = snapshot_indexed_selectors(&kernel, &states);
        assert_eq!(
            exact
                .iter()
                .map(|(selector, _)| *selector)
                .collect::<Vec<_>>(),
            vec![&SnapshotSelector::ProgramPoint(late)]
        );
        assert!(compatible.is_empty());
    }

    #[test]
    fn missing_snapshot_form_reports_a_concise_indexed_failure() {
        let target_memory = CMemory::new().with_block("target", 4);
        let pointer = Pointer {
            block: "target".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(target_memory),
                    Box::new(pointer),
                    crate::kernel::LoadKind::Bits32,
                )),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let state = CState::new().with_memory(CMemory::new().with_block("current", 4));

        let error = checked_surface_comparison_fact_in_state(
            ExecutionView::new(
                &ExecutionFrontier::default(),
                &ExecutionFacts::new(),
                &RecordedSnapshots::new(),
                &SurfacePropositionMap::default(),
                None,
            ),
            &kernel,
            SurfaceFactMatch::CanonicalExact,
            &[],
            ParameterBinding::default(),
            &state,
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
        )
        .expect_err("an unrecorded snapshot should have no surface form");

        assert!(
            error
                .message()
                .contains("0 exact and 0 compatible recorded snapshots"),
            "{error:?}"
        );
        assert!(!error.message().contains("CMemory"), "{error:?}");
    }

    #[test]
    fn snapshot_variant_search_reaches_a_candidate_after_eight() {
        let base = ClickProposition::Comparison {
            left: ContractExpression::CBinding("value".to_string()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(0),
            ))),
        };
        let selectors = (0..20)
            .map(|index| {
                SnapshotSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Statement(index),
                    kind: ProgramPointKind::Entry,
                })
            })
            .collect::<Vec<_>>();
        let variants = comparison_snapshot_variants(&base, &selectors)
            .expect("comparison should have snapshot variants");
        let position = variants
            .iter()
            .position(|candidate| {
                matches!(
                    candidate,
                    ClickProposition::Comparison {
                        left: ContractExpression::At {
                            selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                                region: CodeRegionRef::Statement(2),
                                kind: ProgramPointKind::Entry,
                            }),
                            ..
                        },
                        ..
                    }
                )
            })
            .expect("the late program point should remain a candidate");

        assert!(position > 8, "late valid candidates must not be truncated");
    }

    fn linear_tactic_coordinates(node: &InternalProofNode) -> Vec<(usize, usize)> {
        match node {
            InternalProofNode::Match {
                arms, continuation, ..
            } => {
                let mut coordinates = arms
                    .iter()
                    .flat_map(linear_tactic_coordinates)
                    .collect::<Vec<_>>();
                coordinates.extend(linear_tactic_coordinates(continuation));
                coordinates
            }
            InternalProofNode::Done => Vec::new(),
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                let mut coordinates = tactics
                    .iter()
                    .map(|tactic| (tactic.index, tactic.source_index))
                    .collect::<Vec<_>>();
                coordinates.extend(linear_tactic_coordinates(continuation));
                coordinates
            }
            InternalProofNode::Open {
                body, continuation, ..
            } => {
                let mut coordinates = linear_tactic_coordinates(body);
                coordinates.extend(linear_tactic_coordinates(continuation));
                coordinates
            }
            InternalProofNode::If {
                then_branch,
                else_branch,
                continuation,
                ..
            }
            | InternalProofNode::Branch {
                then_branch,
                else_branch,
                continuation,
                ..
            }
            | InternalProofNode::CallOutcomes {
                returned_branch: then_branch,
                threw_branch: else_branch,
                continuation,
                ..
            } => {
                let mut coordinates = linear_tactic_coordinates(then_branch);
                coordinates.extend(linear_tactic_coordinates(else_branch));
                coordinates.extend(linear_tactic_coordinates(continuation));
                coordinates
            }
        }
    }

    #[test]
    fn generated_certificate_steps_retain_one_owning_source_occurrence() {
        let tactics = [ProofTactic::Step, ProofTactic::Assumption];
        let source = build_internal_proof(&tactics, "source").expect("source proof should build");
        let generated = build_generated_certificate_proof(&tactics, "generated", 7)
            .expect("generated certificate should build");

        assert_eq!(linear_tactic_coordinates(&source), vec![(0, 0), (1, 1)]);
        assert_eq!(linear_tactic_coordinates(&generated), vec![(0, 7), (1, 7)]);
    }

    #[test]
    fn deferred_tactics_retain_their_owning_source_occurrence() {
        let mut execution = ExecutionProofState::at_entry(
            CState::new(),
            ExecutionFrontier::default(),
            RecordedSnapshots::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        );
        execution.defer_post_execution(9, 2, PostExecutionTactic::Simp);

        let mut deferred_entries = execution.post_execution_tactics.iter();
        let deferred = deferred_entries
            .next()
            .expect("expected one deferred tactic");
        assert!(deferred_entries.next().is_none());
        assert_eq!(deferred.tactic_index, 9);
        assert_eq!(deferred.source_index, 2);
        assert!(matches!(deferred.tactic, PostExecutionTactic::Simp));
    }

    #[test]
    fn timing_classifies_a_have_with_only_simple_tactics_as_simple() {
        let have = ProofTactic::Have(ProofHave {
            proposition: ClickProposition::Comparison {
                left: ContractExpression::CFragment(CExpression::Value(int32(1))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(1))),
            },
            proof: SourceProof::Script(vec![ProofTactic::Assumption]),
        });

        assert_eq!(source_site_kind(&have), SourceSiteKind::SimpleOperation);
    }

    #[test]
    fn timing_classifies_smart_and_structural_have_sites_separately() {
        let proposition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(1))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(1))),
        };
        let smart = ProofTactic::Have(ProofHave {
            proposition: proposition.clone(),
            proof: SourceProof::Tactic(SmartTactic::Simp),
        });
        let structural = ProofTactic::Have(ProofHave {
            proposition,
            proof: SourceProof::Script(Vec::new()),
        });

        assert_eq!(
            source_site_kind(&smart),
            SourceSiteKind::ExpandableAutomation
        );
        assert_eq!(
            source_site_kind(&structural),
            SourceSiteKind::ControlContainer
        );
    }

    #[test]
    fn post_execution_timing_charges_have_as_control() {
        let have = PostExecutionTactic::Have(ProofHave {
            proposition: ClickProposition::Comparison {
                left: ContractExpression::CFragment(CExpression::Value(int32(1))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(1))),
            },
            proof: SourceProof::Script(vec![ProofTactic::Assumption]),
        });

        assert_eq!(post_execution_tactic_timing(&have), ("have", "control"));
    }

    #[test]
    fn pure_certificate_check_is_transactional() {
        let file = parse(
            r#"
                theorem reflexive(x: int32) {
                    ensures x <= x by auto;
                }
            "#,
        )
        .expect("theorem should parse");
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions())
            .with_contracts(file.contract_definitions(), &file.c_function_names);
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());
        let spec_definitions =
            SpecDefinitions::new(&predicate_environment, &click_function_environment);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem = &file.theorem_definitions()[0];
        let context =
            pure_theorem_context(theorem, spec_definitions).expect("theorem context should lower");
        let Ensure::Proposition(surface_goal) = theorem.ensures()[0].ensure() else {
            panic!("expected proposition goal");
        };
        let goal = lower_pure_theorem_proposition(
            theorem.name(),
            surface_goal,
            &context.values,
            &context.array_refs,
            &context.memory,
            spec_definitions,
        )
        .expect("goal should lower");
        let root = Proof::for_pure_surface_goal(
            "reflexive.ensures_0",
            &context.requires,
            goal.clone(),
            surface_goal.clone(),
            &context,
            spec_definitions,
            &theorem_environment,
        );
        let error = root
            .apply_step(ProofStep::Assumption)
            .err()
            .expect("a rejected candidate must not be reported as success");
        assert!(
            error.message().contains("assumption"),
            "{}",
            error.message()
        );
        assert!(root.certificate().steps().is_empty());
        let completed = root
            .apply_step(ProofStep::Normalize)
            .expect("failed validation must not mutate the retained root");
        assert_eq!(
            completed.completed_proposition().unwrap().proposition(),
            &goal
        );
    }

    #[test]
    fn direct_pure_auto_and_simp_retain_checked_simple_proofs() {
        let file = parse(
            r#"
                theorem required(x: int32) {
                    requires x >= 0;
                    ensures x >= 0 by auto;
                }

                theorem reflexive(x: int32) {
                    ensures x == x by simp;
                }

                theorem applied(x: int32) {
                    requires x >= 0;
                    ensures x >= 0 by {
                        apply(required(x)) using { x >= 0; }
                    }
                }

                theorem applied_then_simp(x: int32) {
                    requires x >= 0;
                    ensures (x >= 0) and (x >= 0) by {
                        apply(required(x));
                        simp();
                    }
                }

                theorem implication(x: int32) {
                    ensures (x >= 0) implies (x >= 0) by {
                        intro();
                        assumption();
                    }
                }

                theorem conjunction(x: int32) {
                    requires x >= 0;
                    requires x <= 10;
                    ensures (x >= 0) and (x <= 10) by simp;
                }

                theorem disjunction(x: int32) {
                    requires x >= 0;
                    ensures (x >= 0) or (x < 0) by auto;
                }

                theorem impossible(x: int32) {
                    requires x >= 0;
                    requires not (x >= 0);
                    ensures x == 0 by {
                        contradiction(x >= 0);
                    }
                }
            "#,
        )
        .expect("theorems should parse");
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions())
            .with_contracts(file.contract_definitions(), &file.c_function_names);
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());

        let verified = verify_theorem_definitions(
            TheoremEnvironment::new(&[]),
            file.theorem_definitions(),
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
            None,
            &ResourceEnvironment::new(&[]),
            std::sync::Arc::new(FunctionSourceRegistry::default()),
        );
        let verified = verified.expect("direct checked pure proofs should verify");
        assert_eq!(
            verified[0].proof_tactics().as_deref(),
            Some([ProofTactic::Assumption].as_slice())
        );
        assert_eq!(
            verified[1].proof_tactics().as_deref(),
            Some([ProofTactic::Normalize].as_slice())
        );
        assert!(matches!(
            verified[2].proof_tactics().as_deref(),
            Some([ProofTactic::ApplyTheoremUsing { .. }])
        ));
        assert!(matches!(
            verified[3].proof_tactics().as_deref(),
            Some([ProofTactic::ApplyTheoremUsing { application, premises }])
                if application.name == "required" && premises.len() == 1
        ));
        assert_eq!(
            verified[4].proof_tactics().as_deref(),
            Some([ProofTactic::Intro, ProofTactic::Assumption].as_slice())
        );
        assert_eq!(
            verified[5].proof_tactics().as_deref(),
            Some([ProofTactic::Assumption].as_slice())
        );
        assert_eq!(
            verified[6].proof_tactics().as_deref(),
            Some([ProofTactic::Assumption].as_slice())
        );
        assert!(matches!(
            verified[7].proof_tactics().as_deref(),
            Some([ProofTactic::Contradiction(_)])
        ));
    }

    #[test]
    fn path_aligned_certificates_preserve_branch_structure() {
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let assumption = ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a certificate");
        let normalize = ProofCertificate::from_proof_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a certificate");

        let merged = merge_path_aligned_certificates(
            "branching",
            vec![
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: condition.clone(),
                        value: true,
                        match_arm: None,
                    }],
                    case_offsets: None,
                    certificate: assumption,
                },
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: condition.clone(),
                        value: false,
                        match_arm: None,
                    }],
                    case_offsets: None,
                    certificate: normalize,
                },
            ],
        )
        .expect("opposite path certificates should merge");

        let [
            ProofStep::If {
                condition: merged_condition,
                then_proof,
                else_proof,
                ..
            },
        ] = merged.steps()
        else {
            panic!("different path certificates should produce one proof branch");
        };
        assert_eq!(merged_condition, &condition);
        assert_eq!(then_proof.to_proof_tactics(), vec![ProofTactic::Assumption]);
        assert_eq!(else_proof.to_proof_tactics(), vec![ProofTactic::Normalize]);
    }

    #[test]
    fn path_aligned_certificates_reject_incompatible_frontiers() {
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let other = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("y".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let assumption = ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a certificate");
        let normalize = ProofCertificate::from_proof_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a certificate");

        let error = merge_path_aligned_certificates(
            "branching",
            vec![
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition,
                        value: true,
                        match_arm: None,
                    }],
                    case_offsets: None,
                    certificate: assumption,
                },
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: other,
                        value: false,
                        match_arm: None,
                    }],
                    case_offsets: None,
                    certificate: normalize,
                },
            ],
        )
        .expect_err("unrelated branch conditions must not be flattened together");

        assert!(error.message().contains("incompatible next branch"));
    }
}

#[derive(Clone)]
struct IndexedTactic {
    index: usize,
    source_index: usize,
    tactic: ProofTactic,
}

#[derive(Clone)]
enum InternalProofNode {
    Done,
    Match {
        index: usize,
        source_index: usize,
        proof_match: Arc<ProofMatch>,
        arms: Vec<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
    Linear {
        tactics: Vec<IndexedTactic>,
        continuation: Box<InternalProofNode>,
    },
    Open {
        index: usize,
        source_index: usize,
        resource: ResourceClause,
        body: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
    If {
        index: usize,
        source_index: usize,
        condition: ClickProposition,
        ensuring: Option<Vec<ProofAssertion>>,
        then_branch: Box<InternalProofNode>,
        else_branch: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
    Branch {
        index: usize,
        source_index: usize,
        ensuring: Option<Vec<ProofAssertion>>,
        then_branch: Box<InternalProofNode>,
        else_branch: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
    CallOutcomes {
        index: usize,
        source_index: usize,
        returned_branch: Box<InternalProofNode>,
        threw_branch: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
}

#[derive(Clone, Copy)]
pub(super) enum ProofTacticSource {
    SourceSyntax,
    GeneratedBy { source_index: usize },
}

fn build_internal_proof_with_source(
    tactics: &[ProofTactic],
    claim_label: &str,
    source: ProofTacticSource,
) -> Result<InternalProofNode, ClickError> {
    match source {
        ProofTacticSource::SourceSyntax => build_internal_proof(tactics, claim_label),
        ProofTacticSource::GeneratedBy { source_index } => {
            build_generated_certificate_proof(tactics, claim_label, source_index)
        }
    }
}

fn build_internal_proof(
    tactics: &[ProofTactic],
    _claim_label: &str,
) -> Result<InternalProofNode, ClickError> {
    build_internal_proof_at(tactics, 0, 0)
}

fn build_internal_proof_from_source_index(
    tactics: &[ProofTactic],
    source_index: usize,
) -> Result<InternalProofNode, ClickError> {
    build_internal_proof_at(tactics, 0, source_index)
}

fn build_generated_certificate_proof(
    tactics: &[ProofTactic],
    claim_label: &str,
    owning_source_index: usize,
) -> Result<InternalProofNode, ClickError> {
    let mut proof = build_internal_proof(tactics, claim_label)?;
    set_generated_proof_source_index(&mut proof, owning_source_index);
    Ok(proof)
}

fn set_generated_proof_source_index(node: &mut InternalProofNode, owning_source_index: usize) {
    match node {
        InternalProofNode::Match {
            source_index,
            arms,
            continuation,
            ..
        } => {
            *source_index = owning_source_index;
            for arm in arms {
                set_generated_proof_source_index(arm, owning_source_index);
            }
            set_generated_proof_source_index(continuation, owning_source_index);
        }
        InternalProofNode::Done => {}
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            for tactic in tactics {
                tactic.source_index = owning_source_index;
            }
            set_generated_proof_source_index(continuation, owning_source_index);
        }
        InternalProofNode::Open {
            source_index,
            body,
            continuation,
            ..
        } => {
            *source_index = owning_source_index;
            set_generated_proof_source_index(body, owning_source_index);
            set_generated_proof_source_index(continuation, owning_source_index);
        }
        InternalProofNode::If {
            source_index,
            then_branch,
            else_branch,
            continuation,
            ..
        }
        | InternalProofNode::Branch {
            source_index,
            then_branch,
            else_branch,
            continuation,
            ..
        }
        | InternalProofNode::CallOutcomes {
            source_index,
            returned_branch: then_branch,
            threw_branch: else_branch,
            continuation,
            ..
        } => {
            *source_index = owning_source_index;
            set_generated_proof_source_index(then_branch, owning_source_index);
            set_generated_proof_source_index(else_branch, owning_source_index);
            set_generated_proof_source_index(continuation, owning_source_index);
        }
    }
}

fn detach_generated_suffix_from_source_indices(
    node: &mut InternalProofNode,
    first_generated_tactic_index: usize,
) {
    match node {
        InternalProofNode::Match {
            index,
            source_index,
            arms,
            continuation,
            ..
        } => {
            if *index >= first_generated_tactic_index {
                *source_index = usize::MAX;
            }
            for arm in arms {
                detach_generated_suffix_from_source_indices(arm, first_generated_tactic_index);
            }
            detach_generated_suffix_from_source_indices(continuation, first_generated_tactic_index);
        }
        InternalProofNode::Done => {}
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            for tactic in tactics {
                if tactic.index >= first_generated_tactic_index {
                    tactic.source_index = usize::MAX;
                }
            }
            detach_generated_suffix_from_source_indices(continuation, first_generated_tactic_index);
        }
        InternalProofNode::Open {
            index,
            source_index,
            body,
            continuation,
            ..
        } => {
            if *index >= first_generated_tactic_index {
                *source_index = usize::MAX;
            }
            detach_generated_suffix_from_source_indices(body, first_generated_tactic_index);
            detach_generated_suffix_from_source_indices(continuation, first_generated_tactic_index);
        }
        InternalProofNode::If {
            index,
            source_index,
            then_branch,
            else_branch,
            continuation,
            ..
        }
        | InternalProofNode::Branch {
            index,
            source_index,
            then_branch,
            else_branch,
            continuation,
            ..
        }
        | InternalProofNode::CallOutcomes {
            index,
            source_index,
            returned_branch: then_branch,
            threw_branch: else_branch,
            continuation,
        } => {
            if *index >= first_generated_tactic_index {
                *source_index = usize::MAX;
            }
            detach_generated_suffix_from_source_indices(then_branch, first_generated_tactic_index);
            detach_generated_suffix_from_source_indices(else_branch, first_generated_tactic_index);
            detach_generated_suffix_from_source_indices(continuation, first_generated_tactic_index);
        }
    }
}

fn build_internal_proof_at(
    tactics: &[ProofTactic],
    index_offset: usize,
    source_index_offset: usize,
) -> Result<InternalProofNode, ClickError> {
    let Some((control_index, control_tactic)) = tactics.iter().enumerate().find(|(_, tactic)| {
        matches!(
            tactic,
            ProofTactic::If(_)
                | ProofTactic::Branch(_)
                | ProofTactic::CallOutcomes(_)
                | ProofTactic::Open(_)
                | ProofTactic::Match(_)
        )
    }) else {
        if tactics.is_empty() {
            return Ok(InternalProofNode::Done);
        }
        return Ok(InternalProofNode::Linear {
            tactics: indexed_linear_tactics(tactics, index_offset, source_index_offset),
            continuation: Box::new(InternalProofNode::Done),
        });
    };

    let index = index_offset + control_index;
    let source_index = source_index_offset
        + tactics[..control_index]
            .iter()
            .map(source_tactic_width)
            .sum::<usize>();
    let control = match control_tactic {
        ProofTactic::Match(proof_match) => {
            let mut next_source = source_index + 1;
            let mut arms = Vec::with_capacity(proof_match.arms.len());
            for arm in &proof_match.arms {
                arms.push(build_internal_proof_at(
                    &arm.tactics,
                    index + 1,
                    next_source,
                )?);
                next_source += source_tactic_count(&arm.tactics);
            }
            InternalProofNode::Match {
                index,
                source_index,
                proof_match: proof_match.clone(),
                arms,
                continuation: Box::new(build_internal_proof_at(
                    &tactics[control_index + 1..],
                    index + 1,
                    next_source,
                )?),
            }
        }
        ProofTactic::If(proof_if) => {
            let then_width = source_tactic_count(&proof_if.then_tactics);
            InternalProofNode::If {
                index,
                source_index,
                condition: proof_if.condition.clone(),
                ensuring: proof_if.ensuring.clone(),
                then_branch: Box::new(build_internal_proof_at(
                    &proof_if.then_tactics,
                    index + 1,
                    source_index + 1,
                )?),
                else_branch: Box::new(build_internal_proof_at(
                    &proof_if.else_tactics,
                    index + 1,
                    source_index + 1 + then_width,
                )?),
                continuation: Box::new(build_internal_proof_at(
                    &tactics[control_index + 1..],
                    index + 1,
                    source_index + source_tactic_width(control_tactic),
                )?),
            }
        }
        ProofTactic::Branch(proof_branch) => {
            let then_width = source_tactic_count(&proof_branch.then_tactics);
            InternalProofNode::Branch {
                index,
                source_index,
                ensuring: proof_branch.ensuring.clone(),
                then_branch: Box::new(build_internal_proof_at(
                    &proof_branch.then_tactics,
                    index + 1,
                    source_index + 1,
                )?),
                else_branch: Box::new(build_internal_proof_at(
                    &proof_branch.else_tactics,
                    index + 1,
                    source_index + 1 + then_width,
                )?),
                continuation: Box::new(build_internal_proof_at(
                    &tactics[control_index + 1..],
                    index + 1,
                    source_index + source_tactic_width(control_tactic),
                )?),
            }
        }
        ProofTactic::CallOutcomes(outcomes) => {
            let returned_width = source_tactic_count(&outcomes.returned_tactics);
            InternalProofNode::CallOutcomes {
                index,
                source_index,
                returned_branch: Box::new(build_internal_proof_at(
                    &outcomes.returned_tactics,
                    index + 1,
                    source_index + 1,
                )?),
                threw_branch: Box::new(build_internal_proof_at(
                    &outcomes.threw_tactics,
                    index + 1,
                    source_index + 1 + returned_width,
                )?),
                continuation: Box::new(build_internal_proof_at(
                    &tactics[control_index + 1..],
                    index + 1,
                    source_index + source_tactic_width(control_tactic),
                )?),
            }
        }
        ProofTactic::Open(proof_open) => InternalProofNode::Open {
            index,
            source_index,
            resource: proof_open.resource.clone(),
            body: Box::new(build_internal_proof_at(
                &proof_open.tactics,
                index + 1,
                source_index + 1,
            )?),
            continuation: Box::new(build_internal_proof_at(
                &tactics[control_index + 1..],
                index + 1,
                source_index + source_tactic_width(control_tactic),
            )?),
        },
        _ => unreachable!("control-tactic search only returns structured tactics"),
    };

    if control_index == 0 {
        Ok(control)
    } else {
        Ok(InternalProofNode::Linear {
            tactics: indexed_linear_tactics(
                &tactics[..control_index],
                index_offset,
                source_index_offset,
            ),
            continuation: Box::new(control),
        })
    }
}

fn indexed_linear_tactics(
    tactics: &[ProofTactic],
    index_offset: usize,
    source_index_offset: usize,
) -> Vec<IndexedTactic> {
    let mut source_index = source_index_offset;
    tactics
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, tactic)| {
            if let ProofTactic::Synthetic(inner) = tactic {
                // A synthetic tactic is no source site: its index lies past
                // every source position, so no site lookup can match it.
                return IndexedTactic {
                    index: index_offset + index,
                    source_index: SYNTHETIC_SOURCE_INDEX_BASE + index_offset + index,
                    tactic: *inner,
                };
            }
            let indexed = IndexedTactic {
                index: index_offset + index,
                source_index,
                tactic,
            };
            source_index += source_tactic_width(&indexed.tactic);
            indexed
        })
        .collect()
}

/// Where synthetic tactics are numbered: far past any source script.
const SYNTHETIC_SOURCE_INDEX_BASE: usize = usize::MAX / 2;

pub(super) fn source_tactic_count(tactics: &[ProofTactic]) -> usize {
    tactics.iter().map(source_tactic_width).sum()
}

fn source_tactic_width(tactic: &ProofTactic) -> usize {
    match tactic {
        ProofTactic::Synthetic(_) => 0,
        ProofTactic::Match(proof_match) => {
            1 + proof_match
                .arms
                .iter()
                .map(|arm| source_tactic_count(&arm.tactics))
                .sum::<usize>()
        }
        ProofTactic::If(proof_if) => {
            1 + source_tactic_count(&proof_if.then_tactics)
                + source_tactic_count(&proof_if.else_tactics)
        }
        ProofTactic::Cases(proof_cases) => {
            1 + proof_cases
                .arms()
                .iter()
                .map(|arm| source_tactic_count(arm.tactics()))
                .sum::<usize>()
        }
        ProofTactic::StructuralInduct { arms, .. } => {
            1 + arms
                .iter()
                .map(|arm| source_tactic_count(&arm.tactics))
                .sum::<usize>()
        }
        ProofTactic::Branch(proof_branch) => {
            1 + source_tactic_count(&proof_branch.then_tactics)
                + source_tactic_count(&proof_branch.else_tactics)
        }
        ProofTactic::CallOutcomes(outcomes) => {
            1 + source_tactic_count(&outcomes.returned_tactics)
                + source_tactic_count(&outcomes.threw_tactics)
        }
        ProofTactic::Open(proof_open) => 1 + source_tactic_count(&proof_open.tactics),
        ProofTactic::Loop(clause) => {
            1 + clause
                .initialize_proof()
                .map_or(0, proof_source_tactic_count)
                + clause.preserve_proof().map_or(0, proof_source_tactic_count)
        }
        _ => 1,
    }
}

/// Whether `wanted` names this linear tactic or a source tactic nested inside
/// it. A `loop` is one linear tactic whose `initialize` and `preserve` proofs
/// number their own source tactics directly after it, so an expansion site
/// inside a loop body is contained by the loop tactic's source span. The span
/// is measured only when `wanted` lies after this tactic, so the walk costs
/// the selected tactic's subtree, not every nested proof.
fn indexed_tactic_contains_source_index(indexed: &IndexedTactic, wanted: usize) -> bool {
    indexed.source_index == wanted
        || (wanted > indexed.source_index
            && wanted - indexed.source_index
                < source_tactic_count(std::slice::from_ref(&indexed.tactic)))
}

fn internal_proof_contains_source_index(node: &InternalProofNode, wanted: usize) -> bool {
    match node {
        InternalProofNode::Match {
            source_index,
            arms,
            continuation,
            ..
        } => {
            *source_index == wanted
                || arms
                    .iter()
                    .any(|arm| internal_proof_contains_source_index(arm, wanted))
                || internal_proof_contains_source_index(continuation, wanted)
        }
        InternalProofNode::Done => false,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            tactics
                .iter()
                .any(|tactic| indexed_tactic_contains_source_index(tactic, wanted))
                || internal_proof_contains_source_index(continuation, wanted)
        }
        InternalProofNode::Open {
            body, continuation, ..
        } => {
            internal_proof_contains_source_index(body, wanted)
                || internal_proof_contains_source_index(continuation, wanted)
        }
        InternalProofNode::If {
            then_branch,
            else_branch,
            continuation,
            ..
        }
        | InternalProofNode::Branch {
            then_branch,
            else_branch,
            continuation,
            ..
        }
        | InternalProofNode::CallOutcomes {
            returned_branch: then_branch,
            threw_branch: else_branch,
            continuation,
            ..
        } => {
            internal_proof_contains_source_index(then_branch, wanted)
                || internal_proof_contains_source_index(else_branch, wanted)
                || internal_proof_contains_source_index(continuation, wanted)
        }
    }
}

pub(super) fn proof_source_tactic_count(proof: &SourceProof) -> usize {
    match proof {
        SourceProof::Default => 0,
        SourceProof::Tactic(_) => 1,
        SourceProof::Script(tactics) => source_tactic_count(tactics),
    }
}

#[derive(Clone, Copy)]
pub(super) enum FunctionClaimRef<'a> {
    Ensure(usize, &'a EnsureClause),
    ExceptionalEnsure(usize, &'a EnsureClause),
}

impl<'a> FunctionClaimRef<'a> {
    pub(super) fn key(self) -> CFunctionContractClaimKey {
        match self {
            Self::Ensure(index, _) => CFunctionContractClaimKey::Ensure(index),
            Self::ExceptionalEnsure(index, _) => {
                CFunctionContractClaimKey::ExceptionalEnsure(index)
            }
        }
    }

    pub(super) fn proof(self) -> &'a SourceProof {
        match self {
            Self::Ensure(_, clause) | Self::ExceptionalEnsure(_, clause) => clause.proof(),
        }
    }

    pub(super) fn clause(self) -> &'a EnsureClause {
        match self {
            Self::Ensure(_, clause) | Self::ExceptionalEnsure(_, clause) => clause,
        }
    }

    pub(super) fn applies_to(self, outcome: &CFunctionOutcome) -> bool {
        matches!(
            (self, outcome),
            (Self::Ensure(_, _), CFunctionOutcome::Return { .. })
                | (
                    Self::ExceptionalEnsure(_, _),
                    CFunctionOutcome::Throw { .. }
                )
        )
    }

    pub(super) fn is_vacuous_for(self, outcome: &CFunctionOutcome) -> bool {
        matches!(
            (self, outcome),
            (Self::Ensure(_, _), CFunctionOutcome::Throw { .. })
                | (
                    Self::ExceptionalEnsure(_, _),
                    CFunctionOutcome::Return { .. }
                )
        )
    }

    fn verified_claim(self) -> VerifiedClaim {
        match self {
            Self::Ensure(index, clause) => VerifiedClaim::Ensure {
                index,
                clause: clause.clone(),
            },
            Self::ExceptionalEnsure(index, clause) => VerifiedClaim::ExceptionalEnsure {
                index,
                clause: clause.clone(),
            },
        }
    }
}

pub(super) fn function_claims(function_block: &FunctionBlock) -> Vec<FunctionClaimRef<'_>> {
    function_block
        .ensures()
        .iter()
        .enumerate()
        .map(|(index, clause)| FunctionClaimRef::Ensure(index, clause))
        .chain(
            function_block
                .exceptional_ensures()
                .iter()
                .enumerate()
                .map(|(index, clause)| FunctionClaimRef::ExceptionalEnsure(index, clause)),
        )
        .collect()
}

/// The entry a function proof was built from, kept with the theorems the
/// proof issues so that certifying the contract starts from the same entry
/// instead of building it again.
#[derive(Clone, Debug)]
pub(in crate::surface) struct ProofEntryContext {
    pub(in crate::surface) state: CState,
    pub(in crate::surface) arguments: Vec<CExpression>,
    pub(in crate::surface) pure_facts: PureFactList,
}

impl PartialEq for ProofEntryContext {
    fn eq(&self, other: &Self) -> bool {
        self.state == other.state
            && self.arguments == other.arguments
            && *self.pure_facts == *other.pure_facts
    }
}

impl Eq for ProofEntryContext {}

#[derive(Clone)]
pub(super) struct InitialClaimContext {
    pub(super) state: CState,
    pub(super) arguments: Vec<CExpression>,
    /// The entry facts, with the context the setup built from them kept
    /// for the proof and certification to extend.
    pub(super) pure_facts: PureFactList,
    pub(super) entry_fact_origins: Vec<EntryFactOrigin>,
    pub(super) surface_propositions: SurfacePropositionMap,
}

pub(super) fn initial_claim_context(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
) -> Result<
    (
        CState,
        Vec<CExpression>,
        PureFactList,
        SurfacePropositionMap,
    ),
    ClickError,
> {
    let context = initial_claim_context_with_caller_owner(
        function_block,
        parsed_function,
        resource_environment,
        spec_definitions,
        claim_label,
        None,
    )?;
    Ok((
        context.state,
        context.arguments,
        context.pure_facts,
        context.surface_propositions,
    ))
}

/// The surface spelling `name == 0 or name == 1` of a `_Bool` parameter's
/// range entry fact.
fn bool_range_surface(name: &str) -> ClickProposition {
    let equals = |constant: &str| ClickProposition::Comparison {
        left: ContractExpression::CBinding(name.to_string()),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::IntegerLiteral(constant.to_string()),
    };
    ClickProposition::Or(Box::new(equals("0")), Box::new(equals("1")))
}

pub(super) fn initial_claim_context_with_caller_owner(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    caller_owner: Option<&CallerSourceOwnerId>,
) -> Result<InitialClaimContext, ClickError> {
    let (mut state, arguments) = if let Some(startup) = &parsed_function.program_entry_state {
        if !function_block.requires().is_empty() || !parsed_function.parameters().is_empty() {
            return Err(ClickError::new(
                "program-entry main currently requires no parameters or preconditions; static ownership comes from startup",
            ));
        }
        (
            crate::kernel::initialize_c_function_globals(
                &startup
                    .as_ref()
                    .clone()
                    .with_population_creation_tracking()
                    .with_typed_access_policy(
                        parsed_function
                            .to_kernel_function()
                            .contract_interface()
                            .typed_access_policy(),
                    ),
                &parsed_function.to_kernel_function(),
            ),
            vec![],
        )
    } else {
        let authority_definitions = crate::surface::verification::composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )?;
        // Entry output footprints must use the same lowered interface as
        // modular calls, before any resource cell is materialized.
        let (requires, _, ensures, exceptional_ensures, mutable, claims, opaque, _, _) =
            function_contract_summary(
                function_block,
                parsed_function,
                spec_definitions,
                resource_environment,
            )?;
        let (resource_requires, resource_ensures) =
            crate::surface::verification::function_resource_summary(
                function_block,
                parsed_function,
                spec_definitions,
                resource_environment,
            )?;
        let entry_function = parsed_function
            .to_kernel_function()
            .with_contract(requires, ensures, mutable, claims, opaque)
            .with_exceptional_ensures(exceptional_ensures)
            .with_resource_summary(resource_requires, resource_ensures)
            .with_composite_resource_definitions(authority_definitions.clone());
        initial_call_state(
            function_block.requires(),
            parsed_function.parameters(),
            &entry_function,
            &authority_definitions,
        )?
    };
    crate::surface::proof_diagnostics::render::enter_ambient_naming(ParameterBinding::new(
        parsed_function.parameters(),
        &arguments,
    ));
    let mut observed_population_families = BTreeSet::new();
    let mut pending_predicates = BTreeSet::new();
    for requirement in function_block.requires() {
        if let Some(proposition) = requirement.proposition() {
            collect_resource_count_families(proposition, &mut observed_population_families);
            collect_called_predicates(proposition, &mut pending_predicates);
        }
    }
    for ensure in function_block
        .ensures()
        .iter()
        .chain(function_block.exceptional_ensures())
    {
        if let Ensure::Proposition(proposition) = ensure.ensure() {
            collect_resource_count_families(proposition, &mut observed_population_families);
            collect_called_predicates(proposition, &mut pending_predicates);
        }
    }
    // Predicate facts carry their resource-state snapshot opaquely. Register
    // every family a reachable predicate may observe before constructing
    // those facts so zero populations remain observable across later opaque
    // calls.
    let mut visited_predicates = BTreeSet::new();
    while let Some(name) = pending_predicates.pop_first() {
        if !visited_predicates.insert(name.clone()) {
            continue;
        }
        let Some(definition) = spec_definitions.predicates.get(&name) else {
            continue;
        };
        collect_resource_count_families(definition.body(), &mut observed_population_families);
        collect_called_predicates(definition.body(), &mut pending_predicates);
    }
    // Count observations are lowered by the same checked
    // ownership rule at contract boundaries and in proof expressions.
    for family in &observed_population_families {
        state = state.with_observed_population_family(family.clone());
    }
    // Keep an authority-only snapshot before folded composite cells or
    // observable body facts are materialized.  Those conveniences are valid
    // for lowering the proof's later pure context, but they must not help the
    // entry resource evaluator bootstrap a load that the clause set does not
    // supply.
    let entry_authority_state = state.clone();
    let entry_loadability_facts = explicit_entry_loadability_facts(
        function_block,
        parsed_function,
        &arguments,
        &entry_authority_state,
        spec_definitions,
    )?;
    state = materialize_folded_composite_resource_cells(
        resource_environment,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        state,
        claim_label,
        spec_definitions,
    )?;
    let include_owned_composite_cores = Some(resources::OwnedCores::AttachedToOwner);
    let mut projection_state = state.clone();
    for iteration in 0..=function_block.requires().len() {
        if iteration > 0
            && requirement_propositions(
                function_block.requires(),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &projection_state,
                spec_definitions,
            )
            .is_ok()
        {
            break;
        }
        let available_pure_facts = available_initial_requirement_propositions(
            function_block.requires(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &projection_state,
            spec_definitions,
        );
        let projected = project_initial_composite_resource_cores(
            resource_environment,
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            projection_state.clone(),
            &available_pure_facts,
            claim_label,
            Some(resources::OwnedCores::Standing),
            spec_definitions,
        )?;
        if projected == projection_state {
            break;
        }
        projection_state = projected;
    }
    state = state.with_memory(projection_state.memory().clone());
    let lowered_requirement_facts =
        crate::surface::lowering::requirement_propositions_with_sources_and_assumptions(
            function_block.requires(),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            spec_definitions,
            &PureFactContext::new(),
        )?;
    let mut requirement_pure_facts = Vec::with_capacity(lowered_requirement_facts.len());
    let mut entry_fact_origins = Vec::with_capacity(lowered_requirement_facts.len());
    for lowered in lowered_requirement_facts {
        requirement_pure_facts.push(lowered.proposition);
        entry_fact_origins.push(match caller_owner {
            Some(owner) => EntryFactOrigin::Requirement {
                source_id: RequirementSourceId {
                    owner: owner.clone(),
                    outer_ordinal: lowered.source_ordinal,
                },
                role: match lowered.role {
                    crate::surface::lowering::LoweredRequirementFactRole::Principal => {
                        RequirementFactRole::Principal {
                            unfolding_path: Vec::new(),
                        }
                    }
                    crate::surface::lowering::LoweredRequirementFactRole::Guard(ordinal) => {
                        RequirementFactRole::LoweringGuard { ordinal }
                    }
                },
            },
            None => EntryFactOrigin::Derived,
        });
    }
    // Each `_Bool` parameter's range, `flag == 0 or flag == 1`, is a
    // derived entry fact the kernel certifies from the parameter's normalized
    // value; without it a disjunction such as `result == 0 or result == 1`
    // would need an explicit case split on the parameter. Its surface
    // spelling is recorded below so a proof search can case on it.
    let bool_range_facts = parsed_function
        .parameters()
        .iter()
        .zip(&arguments)
        .filter(|(parameter, _)| matches!(parameter.c_type(), syntax::C0Type::Bool))
        .filter_map(|(parameter, argument)| match argument {
            CExpression::Value(value) => crate::kernel::c_bool_range_fact(value)
                .map(|fact| (bool_range_surface(parameter.name()), fact)),
            _ => None,
        })
        .collect::<Vec<_>>();
    requirement_pure_facts.extend(bool_range_facts.iter().map(|(_, fact)| fact.clone()));
    // Each narrow integer parameter's type range, such as `0 <= x` and
    // `x <= 255` for a `uint8`, is likewise a derived entry fact the kernel
    // states from the parameter's value. It is filed here once, where the
    // value is introduced, so no use of the parameter has to restate it.
    for argument in &arguments {
        if let CExpression::Value(value) = argument
            && let Some(facts) = crate::kernel::c_narrow_integer_range_facts(value)
        {
            requirement_pure_facts.extend(facts);
        }
    }
    entry_fact_origins.resize(requirement_pure_facts.len(), EntryFactOrigin::Derived);
    // The lowerings of requirements that mention `defined(...)` at this
    // folded state; they are replaced at the definedness state below.
    let defined_requirement_ordinals = function_block
        .requires()
        .iter()
        .enumerate()
        .filter_map(|(ordinal, requirement)| {
            matches!(
                requirement,
                Requirement::Proposition(surface) if click_proposition_mentions_defined(surface)
            )
            .then_some(ordinal)
        })
        .collect::<BTreeSet<_>>();
    // Every requirement below is lowered under the one context of the
    // lowered requirement facts, built once rather than once per requirement
    // (which was quadratic in the requirement count).
    let requirement_context = assumptions_from_propositions(&requirement_pure_facts);
    let folded_defined_facts = function_block
        .requires()
        .iter()
        .filter(|requirement| {
            matches!(
                requirement,
                Requirement::Proposition(surface) if click_proposition_mentions_defined(surface)
            )
        })
        .map(|requirement| {
            requirement_propositions_with_assumptions(
                std::slice::from_ref(requirement),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &state,
                spec_definitions,
                &requirement_context,
            )
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let mut surface_propositions = SurfacePropositionMap::default();
    for (surface, kernel) in &bool_range_facts {
        surface_propositions.record_lowering(surface, kernel)?;
    }
    for requirement in function_block.requires() {
        let surface = match requirement {
            Requirement::Proposition(proposition) => Some(proposition.clone()),
            Requirement::LoadableSegment { segment } => Some(ClickProposition::Loadable {
                segment: segment.clone(),
            }),
            Requirement::Resource(_) => None,
        };
        let Some(surface) = surface else {
            continue;
        };
        // Recorded below at the definedness state instead.
        if click_proposition_mentions_defined(&surface) {
            continue;
        }
        let lowered = requirement_propositions_with_assumptions(
            std::slice::from_ref(requirement),
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            spec_definitions,
            &requirement_context,
        )?;
        if let Some(kernel) = lowered.first() {
            surface_propositions.record_lowering(&surface, kernel)?;
        }
    }
    let unfolded_requirement_facts = requirements_with_structural_unfolds(
        spec_definitions,
        function_block,
        &PureFactList::from(requirement_pure_facts),
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    // Structural setup only appends checked unfoldings. They are useful entry
    // facts, but Phase 1 keeps the written requirement's unique principal
    // fact as the selection authority; an appended unfolding is derived.
    entry_fact_origins.resize(unfolded_requirement_facts.len(), EntryFactOrigin::Derived);
    state = project_initial_composite_resource_cores(
        resource_environment,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        state,
        &unfolded_requirement_facts,
        claim_label,
        include_owned_composite_cores,
        spec_definitions,
    )?;
    requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        &state,
        &unfolded_requirement_facts,
        spec_definitions,
        claim_label,
    )?;
    entry_fact_origins.resize(requirement_pure_facts.len(), EntryFactOrigin::Derived);
    let definedness_state = project_initial_composite_resource_cores(
        resource_environment,
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        state.clone(),
        &requirement_pure_facts,
        claim_label,
        Some(resources::OwnedCores::Standing),
        spec_definitions,
    )?;
    // An explicit `defined(...)` requirement evaluates C loads, which need
    // the composite cores projected for that purpose. Lowered at the folded
    // entry state it reads no cell and collapses to `false`, which would make
    // the whole proof context vacuous. Re-lower those requirements at the
    // definedness state and replace their entry facts.
    let retained = requirement_pure_facts
        .into_iter()
        .zip(entry_fact_origins)
        .filter(|(fact, origin)| match origin {
            EntryFactOrigin::Requirement { source_id, .. } => {
                !defined_requirement_ordinals.contains(&source_id.outer_ordinal)
            }
            // Legacy setup callers have no source owner. Keep their previous
            // value-based replacement behavior; production execution proofs
            // always take the exact source-ID branch above.
            EntryFactOrigin::Derived => {
                caller_owner.is_some() || !folded_defined_facts.contains(fact)
            }
        })
        .collect::<Vec<_>>();
    (requirement_pure_facts, entry_fact_origins) = retained.into_iter().unzip();
    // Extended by the facts each re-lowered requirement adds, not rebuilt
    // per requirement.
    let mut definedness_context = PureFactContext::new();
    let mut definedness_context_facts = 0;
    for (source_ordinal, requirement) in function_block.requires().iter().enumerate() {
        let Requirement::Proposition(surface) = requirement else {
            continue;
        };
        if !click_proposition_mentions_defined(surface) {
            continue;
        }
        for fact in &requirement_pure_facts[definedness_context_facts..] {
            definedness_context = definedness_context
                .assume_proposition(crate::kernel::clone_proposition_iteratively(fact));
        }
        definedness_context_facts = requirement_pure_facts.len();
        let projected =
            crate::surface::lowering::requirement_propositions_with_sources_and_assumptions(
                std::slice::from_ref(requirement),
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                &definedness_state,
                spec_definitions,
                &definedness_context,
            )?;
        let Some(principal) = projected.iter().find(|fact| {
            matches!(
                fact.role,
                crate::surface::lowering::LoweredRequirementFactRole::Principal
            )
        }) else {
            continue;
        };
        surface_propositions.record_lowering(surface, &principal.proposition)?;
        for fact in projected {
            let origin = match caller_owner {
                Some(owner) => EntryFactOrigin::Requirement {
                    source_id: RequirementSourceId {
                        owner: owner.clone(),
                        outer_ordinal: source_ordinal,
                    },
                    role: match fact.role {
                        crate::surface::lowering::LoweredRequirementFactRole::Principal => {
                            RequirementFactRole::Principal {
                                unfolding_path: Vec::new(),
                            }
                        }
                        crate::surface::lowering::LoweredRequirementFactRole::Guard(ordinal) => {
                            RequirementFactRole::LoweringGuard { ordinal }
                        }
                    },
                },
                None => EntryFactOrigin::Derived,
            };
            if caller_owner.is_some() || !requirement_pure_facts.contains(&fact.proposition) {
                requirement_pure_facts.push(fact.proposition);
                entry_fact_origins.push(origin);
            }
        }
    }
    let definedness = requirement_definedness_propositions(
        function_block.requires(),
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        &definedness_state,
        spec_definitions,
    )?;
    for (surface, kernel) in &definedness {
        surface_propositions.record_lowering(surface, kernel)?;
    }
    // These facts are consequences of accepting the requirements. Keep them
    // out of resource-body projection, but include them in the certified entry
    // context and in the opaque rule exported for this function.
    for (_, kernel) in definedness.into_iter().rev() {
        if !requirement_pure_facts.contains(&kernel) {
            requirement_pure_facts.insert(0, kernel);
            entry_fact_origins.insert(0, EntryFactOrigin::Derived);
        }
    }
    // Resource projection can legitimately publish loadability observations
    // for proof planning, but those observations are not entry assumptions.
    // Rebuild the evaluator's pure context from the non-loadability facts and
    // the explicit loadability requirements captured before projection.
    let mut entry_pure_facts = requirement_pure_facts
        .iter()
        // Projection may expose a loadability atom alongside ordinary logical
        // content.  Remove only an unconditional conjunctive loadability atom;
        // retain the rest of the proposition so the entry evaluator sees the
        // same checked logical requirements without treating a branch,
        // negation, or quantifier as an unconditional read capability.
        .filter_map(entry_pure_fact_without_unconditional_loadability)
        .collect::<Vec<_>>();
    for fact in entry_loadability_facts {
        if !entry_pure_facts.contains(&fact) {
            entry_pure_facts.push(fact);
        }
    }
    // The entry evaluation reads these facts' context twice; the list keeps
    // the first build for the second.
    let entry_pure_facts = PureFactList::from(entry_pure_facts);
    // Resource terms are first built provisionally so dependent arguments can
    // retain their symbolic loads.  The kernel then evaluates the complete
    // clause section against its explicit supplies and the pure requirements;
    // this is the authority for both direct and named contracts.  A surface
    // segment diagnostic is used only to enrich a kernel refusal, never to
    // authorize a clause independently.
    let entry_partition_facts;
    let entry_quantity_facts;
    (state, entry_partition_facts, entry_quantity_facts) = evaluate_entry_resource_context(
        function_block,
        parsed_function,
        resource_environment,
        spec_definitions,
        state,
        &arguments,
        &entry_pure_facts,
        include_owned_composite_cores,
        claim_label,
        &entry_authority_state.resources().clone(),
        &entry_authority_state.memory().clone(),
    )?;
    // The entry partition facts are entry assumptions of this contract, on the
    // same footing as the `viewable(..)` fact a clause yields: they are
    // derived from the written clause list. They are the proof side's
    // spelling of what the kernel's contract entry states; a proof keeps one
    // only when the entry states it (`contract_entry_view`).
    for fact in entry_partition_facts {
        if !requirement_pure_facts.contains(&fact) {
            requirement_pure_facts.push(fact);
            entry_fact_origins.push(EntryFactOrigin::Derived);
        }
    }
    // Quantity guards are checked implicit requirements. Append them directly:
    // deduplicating each one by scanning all earlier facts makes a section
    // with many quantified clauses quadratic. The fact context indexes them.
    requirement_pure_facts.extend(entry_quantity_facts);
    entry_fact_origins.resize(requirement_pure_facts.len(), EntryFactOrigin::Derived);
    // From here the entry facts only grow, so every context read of them
    // below extends one built context.
    let mut requirement_pure_facts = PureFactList::from(requirement_pure_facts);
    state = materialize_checked_entry_input_cells(
        state,
        function_block.requires(),
        parsed_function.parameters(),
        &arguments,
        &requirement_pure_facts.context(),
    )?;
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement else {
            continue;
        };
        record_initial_composite_surface_facts(
            resource_environment,
            resource,
            ParameterBinding::new(parsed_function.parameters(), &arguments),
            &state,
            &requirement_pure_facts,
            &mut surface_propositions,
            spec_definitions,
            &mut BTreeSet::new(),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed while recording resource facts: {message}"
            ))
        })?;
    }
    // Contract entry lowering is one of the eight frontiers that decide a
    // matched instance's arms, and it consumes the same publication as the
    // other seven: the arms the requirements refute, and the facts of the arm
    // they leave. A requirement of any shape refutes here exactly as an
    // invariant of that shape refutes at a loop head. Published last, on the
    // finished entry state, so the same entry state reaches the checked
    // execution and the contract's certification; an earlier publication would
    // feed the resource projection and the two would no longer agree.
    let composite_definitions = crate::surface::verification::composite_resource_definitions(
        resource_environment,
        spec_definitions,
    )?;
    let publication = crate::kernel::publish_instance_arms(
        state.resources(),
        &composite_definitions,
        &state,
        &requirement_pure_facts.context(),
    );
    for fact in publication
        .model_facts
        .into_iter()
        .chain(publication.arm_facts)
    {
        if !requirement_pure_facts.contains(&fact) {
            requirement_pure_facts.push(fact);
            entry_fact_origins.push(EntryFactOrigin::Derived);
        }
    }
    debug_assert_eq!(requirement_pure_facts.len(), entry_fact_origins.len());
    // Export the selected function-entry input in the final execution lineage.
    // Clause evaluation used a separate context with projection-derived read
    // facts excluded; its prepared index cannot stand in for this one. Entry
    // construction owns this whole-input boundary, once before proof steps.
    // Permission lookup must only advance its checked resource/equality deltas.
    state
        .resources()
        .synchronize_memory_equalities(&requirement_pure_facts.context());
    refuse_overlapping_returned_places(
        function_block,
        parsed_function,
        &state,
        &arguments,
        &requirement_pure_facts.context(),
    )?;
    Ok(InitialClaimContext {
        state,
        arguments,
        pure_facts: requirement_pure_facts,
        entry_fact_origins,
        surface_propositions,
    })
}

/// A function cannot hand back two owners of overlapping memory. Identical
/// clauses are refused where the contract is parsed; this refuses clauses
/// that differ and still overlap, such as `owns *p; produces p->value;`, by
/// running the kernel's own check for overlapping owners on the places the
/// contract returns.
///
/// Only places built from parameters are compared. An `owns` clause is read
/// at entry and a `produces` clause at exit, and a place reached through
/// memory the function may change can differ between the two.
fn refuse_overlapping_returned_places(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    state: &CState,
    arguments: &[CExpression],
    assumptions: &crate::kernel::PureFactContext,
) -> Result<(), ClickError> {
    let parameters = parsed_function.parameters();
    let mut returned = crate::kernel::ResourceContext::new();
    let mut written = Vec::new();
    let mut places = 0;
    for clause in function_block.ensures() {
        if clause.condition().is_some() {
            continue;
        }
        let Ensure::Resource(resource @ ResourceClause::OwnMemory(segment)) = clause.ensure()
        else {
            continue;
        };
        let fixed_place = [&segment.base, &segment.start, &segment.end]
            .into_iter()
            .all(crate::surface::validation::c_expression_reads_no_memory);
        if !fixed_place {
            continue;
        }
        let Ok(fact) = crate::surface::lowering::lower_resource_clause_at_state(
            resource,
            ParameterBinding::new(parameters, arguments),
            state,
        ) else {
            continue;
        };
        if let Some(range) = fact.memory_own_range() {
            written.push((range.clone(), segment));
        }
        returned = returned.unchecked_with_fact(fact);
        places += 1;
    }
    if places < 2 {
        return Ok(());
    }
    let Some(crate::kernel::ResourceContextValidityError::OverlappingOwnedMemoryResources {
        left,
        right,
    }) = returned.validity_error(assumptions)
    else {
        return Ok(());
    };
    // Name each place as its clause wrote it.
    let spelled = |range: &crate::kernel::CMemoryRange| {
        written
            .iter()
            .find(|(candidate, _)| candidate == range)
            .map(|(_, segment)| crate::surface::diagnostics::describe_contract_segment(segment))
            .unwrap_or_else(|| {
                crate::surface::diagnostics::describe_memory_range(
                    range,
                    ParameterBinding::new(parameters, arguments),
                )
            })
    };
    Err(ClickError::new(format!(
        "`{}` would return overlapping places: `{}` and `{}`; a function cannot hand back two owners of the same memory",
        function_block.signature().name(),
        spelled(&left),
        spelled(&right),
    ))
    .with_kind(ClickErrorKind::Type))
}

/// Removes loadability that projection derived as an entry-evaluator fact.
///
/// Only `And` is structurally safe to split: an atom in an `Or`, implication,
/// negation, or quantifier is conditional and cannot become unconditional read
/// authority.  Those propositions are retained as whole logical facts, while
/// [`precondition_read_facts`] below recognizes only a standalone
/// `CMemoryLoadable` proposition as a checked read view.  This keeps unrelated
/// conjuncts from disappearing merely because one projected atom was removed.
fn entry_pure_fact_without_unconditional_loadability(
    proposition: &Proposition,
) -> Option<Proposition> {
    match proposition {
        Proposition::CMemoryLoadable { .. } => None,
        Proposition::And(left, right) => {
            let left = entry_pure_fact_without_unconditional_loadability(left);
            let right = entry_pure_fact_without_unconditional_loadability(right);
            match (left, right) {
                (Some(left), Some(right)) => {
                    Some(Proposition::And(Box::new(left), Box::new(right)))
                }
                (Some(proposition), None) | (None, Some(proposition)) => Some(proposition),
                (None, None) => None,
            }
        }
        // Do not inspect a conditional or bound body: retaining it preserves
        // its logic but never promotes a nested loadability atom to authority.
        Proposition::Or(..)
        | Proposition::Implies(..)
        | Proposition::Not(..)
        | Proposition::ForAll { .. }
        | Proposition::Exists { .. } => Some(proposition.clone()),
        _ => Some(proposition.clone()),
    }
}

/// Collects only loadability segments that are unconditional conjuncts of a
/// source requirement.  A separate lowered atom is used for each segment so
/// its checked read view can be supplied to the kernel entry evaluator without
/// lowering or authorizing the surrounding logical proposition.
fn collect_conjunctive_loadability_segments(
    proposition: &ClickProposition,
    segments: &mut Vec<ContractSegment>,
) {
    match proposition {
        ClickProposition::Initialized { .. } => {}
        ClickProposition::Loadable { segment } => segments.push(segment.clone()),
        ClickProposition::And(left, right) => {
            collect_conjunctive_loadability_segments(left, segments);
            collect_conjunctive_loadability_segments(right, segments);
        }
        // A loadability atom under a branch, negation, quantifier, snapshot,
        // or range binder is not unconditional entry authority.
        ClickProposition::Comparison { .. }
        | ClickProposition::FloatClassification { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::ValidPlace { .. }
        | ClickProposition::Defined { .. }
        | ClickProposition::At { .. }
        | ClickProposition::Or(..)
        | ClickProposition::Not(..)
        | ClickProposition::Implies(..)
        | ClickProposition::ForAll { .. }
        | ClickProposition::Exists { .. }
        | ClickProposition::RangeAll { .. }
        | ClickProposition::RangeAny { .. }
        | ClickProposition::PredicateCall { .. } => {}
    }
}

fn explicit_entry_loadability_facts(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    arguments: &[CExpression],
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<Proposition>, ClickError> {
    let mut facts = Vec::new();
    for requirement in function_block.requires() {
        match requirement {
            Requirement::LoadableSegment { .. } => {
                let lowered = crate::surface::lowering::requirement_propositions_with_assumptions(
                    std::slice::from_ref(requirement),
                    ParameterBinding::new(parsed_function.parameters(), arguments),
                    state,
                    spec_definitions,
                    &PureFactContext::new(),
                )?;
                for fact in lowered {
                    if matches!(fact, Proposition::CMemoryLoadable { .. }) && !facts.contains(&fact)
                    {
                        facts.push(fact);
                    }
                }
            }
            Requirement::Proposition(proposition) => {
                let mut segments = Vec::new();
                collect_conjunctive_loadability_segments(proposition, &mut segments);
                for segment in segments {
                    let loadable = Requirement::Proposition(ClickProposition::Loadable { segment });
                    let lowered =
                        crate::surface::lowering::requirement_propositions_with_assumptions(
                            std::slice::from_ref(&loadable),
                            ParameterBinding::new(parsed_function.parameters(), arguments),
                            state,
                            spec_definitions,
                            &PureFactContext::new(),
                        )?;
                    for fact in lowered {
                        if matches!(fact, Proposition::CMemoryLoadable { .. })
                            && !facts.contains(&fact)
                        {
                            facts.push(fact);
                        }
                    }
                }
            }
            Requirement::Resource(_) => {}
        }
    }
    Ok(facts)
}

/// Evaluates entry resource clauses once, after all pure requirements have
/// been lowered.  Surface entry setup needs a provisional resource context in
/// order to materialize folded composite cells, but that context is not
/// authority: the kernel section evaluator starts from only the named
/// instance identities that a `Named` clause must validate and derives every
/// other read supply from clauses that it successfully evaluates.
#[allow(clippy::too_many_arguments)]
fn evaluate_entry_resource_context(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    state: CState,
    arguments: &[CExpression],
    pure_facts: &PureFactList,
    include_owned_composite_cores: Option<resources::OwnedCores>,
    claim_label: &str,
    entry_resources: &ResourceContext,
    entry_memory: &CMemory,
) -> Result<(CState, Vec<Proposition>, Vec<Proposition>), ClickError> {
    let parameter_binding = ParameterBinding::new(parsed_function.parameters(), arguments);
    let (resource_specs, _) = crate::surface::verification::function_resource_summary(
        function_block,
        parsed_function,
        spec_definitions,
        resource_environment,
    )?;
    if resource_specs.is_empty() {
        return Ok((state, Vec::new(), Vec::new()));
    }

    // The kernel evaluator resolves source parameter names through its local
    // environment.  Entry lowering already has their exact symbolic values;
    // install those values without rebinding frames or inspecting a concrete
    // function body (named contracts deliberately have none).
    let values = crate::surface::lowering::parameter_values(ParameterBinding::new(
        parsed_function.parameters(),
        arguments,
    ))?;
    let explicit_entry_facts = entry_resources
        .facts()
        .iter()
        // Direct memory clauses are explicit entry authority too.  They are
        // safe to expose before evaluation: unlike composite facts, they do
        // not acquire any cells from a resource body.  In particular, a
        // quantity such as `pool->capacity of pool_slot(pool)` may read the
        // explicitly owned `*pool` clause before its containing
        // composite is evaluated.
        .filter(|fact| {
            matches!(
                fact.resource(),
                CResource::Instance(_) | CResource::Memory(_) | CResource::PopulationAuthority(_)
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    // A function assumes its explicit pure preconditions at entry.  A loadability
    // precondition is therefore a checked read capability for evaluating a
    // dependent resource argument, but it is never ownership or body
    // authority.  Keep a read view for each concrete loadability atom,
    // matching the projection used by certification.
    let precondition_read_facts = pure_facts
        .iter()
        .filter_map(|fact| {
            let Proposition::CMemoryLoadable { base, bytes, .. } = fact else {
                return None;
            };
            let range = match bytes {
                Bitvector32Term::Multiply(left, right)
                    if **right == Bitvector32Term::Constant(CType::Int32.byte_width()) =>
                {
                    CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(0),
                        left.as_ref().clone(),
                    )
                }
                Bitvector32Term::Multiply(left, right)
                    if **left == Bitvector32Term::Constant(CType::Int32.byte_width()) =>
                {
                    CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(0),
                        right.as_ref().clone(),
                    )
                }
                Bitvector32Term::Constant(bytes) if bytes % CType::Int32.byte_width() == 0 => {
                    CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(bytes / CType::Int32.byte_width()),
                    )
                }
                _ => CMemoryRange::new_with_element_width(
                    base.clone(),
                    Bitvector32Term::Constant(0),
                    bytes.clone(),
                    1,
                ),
            };
            Some(CResourceFact::view_memory(range))
        })
        .collect::<Vec<_>>();
    let assumptions = pure_facts.context();
    let mut evaluation_state = state.clone().with_resource_context(
        ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_facts(explicit_entry_facts)
            .unchecked_with_facts(precondition_read_facts),
    );
    evaluation_state = evaluation_state.with_memory(entry_memory.clone());
    for parameter in parsed_function.parameters() {
        if let Some(value) = values.get(parameter.name()) {
            evaluation_state = evaluation_state.with_local(parameter.name(), value.clone());
        }
    }
    let definitions = crate::surface::verification::composite_resource_definitions(
        resource_environment,
        spec_definitions,
    )?;
    let mut assumptions = assumptions;
    let mut budget = ExecutionBudget::for_new_execution();
    let quantity_assumptions = match crate::kernel::quantified_resource_requirement_assumptions(
        &evaluation_state,
        &resource_specs,
        &definitions,
        &assumptions,
        &mut budget,
    ) {
        Ok(Ok(propositions)) => propositions,
        Ok(Err(error)) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` setup failed: could not evaluate the contract entry resources: {}",
                crate::surface::diagnostics::describe_runtime_error(&error, parameter_binding)
            )));
        }
        Err(limit) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` setup failed: could not evaluate the contract entry resources: it stopped at {}",
                limit.describe()
            )));
        }
    };
    for proposition in &quantity_assumptions {
        assumptions = assumptions.assume_proposition(proposition.clone());
    }
    let (evaluated, entry_clauses) =
        match crate::kernel::evaluate_function_resource_context_with_metadata(
            &evaluation_state,
            &resource_specs,
            &definitions,
            &assumptions,
            &mut budget,
        ) {
            Ok(Ok(evaluated)) => evaluated,
            Ok(Err(error)) => {
                // Keep the established source-rich spelling for a dependent
                // memory segment.  This is a diagnostic projection of the
                // kernel's already-final refusal, not a second acceptance path;
                // declared/composite argument failures have no surface fallback
                // and retain the kernel's clause-positioned error.
                if let Err(surface_error) =
                    crate::surface::lowering::check_resource_segment_base_loadability(
                        function_block,
                        parameter_binding,
                        &state,
                        &assumptions,
                    )
                {
                    return Err(surface_error.with_context(format!("`{claim_label}` setup failed")));
                }
                return Err(ClickError::new(format!(
                    "`{claim_label}` setup failed: could not evaluate the contract entry resources: {}",
                    crate::surface::diagnostics::describe_runtime_error(&error, parameter_binding)
                )));
            }
            Err(limit) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` setup failed: could not evaluate the contract entry resources: it stopped at {}",
                    limit.describe()
                )));
            }
        };
    let state = state.with_resource_context(evaluated);
    // The entry partition (`kernel::contract_entry_partition_facts`): this
    // contract's transferred memory clauses are separate from its borrowed
    // `views` clauses. Read off the *clause list* the kernel just evaluated,
    // never off the resulting context, because a context also holds the
    // owner observation `views r` that `owns r` publishes, and that view is
    // not separate from its own owner. Contract certification derives the
    // same facts from the same clause list, so the two entry contexts agree.
    let entry_partition_facts = crate::kernel::contract_entry_partition_facts(&entry_clauses);
    // Quantity guards are implicit requirements, just as they are in the
    // kernel's certified entry. Retain them in the proof context as well;
    // otherwise the checked boundary loses the very premise used above to
    // admit a symbolic `owns n of ...` clause.
    let entry_quantity_facts = { quantity_assumptions };
    let state = project_initial_composite_resource_cores(
        resource_environment,
        parameter_binding,
        state,
        pure_facts,
        claim_label,
        include_owned_composite_cores,
        spec_definitions,
    )?;
    Ok((state, entry_partition_facts, entry_quantity_facts))
}

fn click_proposition_mentions_defined(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Defined { .. } => true,
        ClickProposition::At { proposition, .. } | ClickProposition::Not(proposition) => {
            click_proposition_mentions_defined(proposition)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            click_proposition_mentions_defined(left) || click_proposition_mentions_defined(right)
        }
        ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. }
        | ClickProposition::RangeAll { body, .. }
        | ClickProposition::RangeAny { body, .. } => click_proposition_mentions_defined(body),
        ClickProposition::Comparison { .. }
        | ClickProposition::FloatClassification { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Initialized { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::ValidPlace { .. }
        | ClickProposition::PredicateCall { .. } => false,
    }
}

fn available_initial_requirement_propositions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
) -> Vec<Proposition> {
    let mut propositions = Vec::new();
    for requirement in requires {
        let Ok(lowered) = requirement_propositions(
            std::slice::from_ref(requirement),
            parameter_binding,
            state,
            spec_definitions,
        ) else {
            continue;
        };
        for proposition in lowered {
            if !propositions.contains(&proposition) {
                propositions.push(proposition);
            }
        }
    }
    propositions
}

fn canonical_claim_caller_state(
    state: CState,
    has_verified_loops: bool,
    function: &CFunction,
    arguments: &[CExpression],
    pure_facts: &(impl PropositionSource + ?Sized),
    claim_label: &str,
) -> Result<CState, ClickError> {
    if !has_verified_loops {
        return Ok(state);
    }
    let entry = c_function_contract_entry_state(
        &state,
        function,
        arguments,
        &assumptions_from_propositions(pure_facts),
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` {message}")))?;
    Ok(state.with_resource_context(entry.resources().clone()))
}

fn install_borrowed_contract_inputs(
    state: CState,
    function: &CFunction,
    pure_facts: &(impl PropositionSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
    proof_label: &str,
) -> Result<CState, ClickError> {
    if let Some(message) = crate::kernel::guard_contract_refusal(function.contract_interface()) {
        return Err(ClickError::new(format!("`{proof_label}` {message}")));
    }
    crate::kernel::c_state_with_borrowed_contract_inputs(
        state,
        function,
        parameter_binding.arguments,
        &assumptions_from_propositions(pure_facts),
    )
    .map_err(|diagnostic| {
        ClickError::new(format!(
            "`{proof_label}` could not establish stable authority for a contract input view: {}",
            crate::surface::diagnostics::describe_loan_refusal(&diagnostic, parameter_binding,)
        ))
    })
}

pub(super) fn prove_claim_by_auto(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    // `auto` is exactly the script `execute(); simp();`.
    let tactics = [ProofTactic::SmartExecute, ProofTactic::Simp];
    let mut theorems = prove_claim_by_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function_source_registry,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    if function_block
        .structural_clauses()
        .iter()
        .any(|clause| matches!(clause.region(), CodeRegion::Loop(_)))
    {
        for theorem in &mut theorems.theorems {
            theorem.proof_kind = ProofKind::LoopVerification;
        }
    }
    Ok(theorems.theorems)
}

pub(super) fn prove_claim_by_simp(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if count_loop_regions(parsed_function) != 0 {
        return Err(ClickError::new(format!(
            "`simp` does not prove loop-backed claims for `{claim_label}`; use `by auto;`"
        )));
    }

    let tactics = [ProofTactic::Simp];
    let mut theorems = prove_claim_by_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function_source_registry,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    for theorem in &mut theorems.theorems {
        theorem.proof_kind = ProofKind::Simp;
    }
    Ok(theorems.theorems)
}

/// An explicit per-claim proof script. The completed proof unit is the
/// semantic result; retained provenance is serialized only for expansion.
#[allow(clippy::too_many_arguments)]
pub(super) fn prove_claim_by_script(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let theorems = prove_claim_by_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function_source_registry,
        tactics,
        ProofTacticSource::SourceSyntax,
    )?;
    Ok(theorems.theorems)
}

thread_local! {
    /// Set while a loop body the automatic closer planned is being checked,
    /// when that body joined a C `if` whose arms ended apart.
    static AUTOMATIC_BODY_JOINED_APART: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Restores the previous note when the check of a planned body ends.
struct AutomaticBodyJoinedApart(bool);

impl Drop for AutomaticBodyJoinedApart {
    fn drop(&mut self) {
        AUTOMATIC_BODY_JOINED_APART.with(|flag| flag.set(self.0));
    }
}

/// Notes, for as long as the returned guard lives, whether the planned loop
/// body under check joined a C `if` whose arms ended apart. A failure to
/// close an invariant then says so, since what failed to close may be
/// something only one arm established.
fn note_automatic_body_joined_apart(joined_apart: bool) -> AutomaticBodyJoinedApart {
    AutomaticBodyJoinedApart(AUTOMATIC_BODY_JOINED_APART.with(|flag| flag.replace(joined_apart)))
}

/// Whether the planned loop body under check joined a C `if` whose arms
/// ended apart.
fn automatic_body_joined_apart() -> bool {
    AUTOMATIC_BODY_JOINED_APART.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(in crate::surface) use proof_object::take_outcome_fact_reads;

#[cfg(test)]
pub(in crate::surface) use proof_object::take_terminal_publication_visits;
