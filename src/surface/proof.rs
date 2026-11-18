use super::diagnostics::*;
use super::validation::{collect_called_predicates, collect_resource_count_families, tactic_name};
use super::*;
#[cfg(test)]
use crate::kernel::CompareRelation;
use crate::kernel::MachineIntegerType;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{ExecutionFactSource, ExecutionFacts, StoredExecutionValue};
use crate::kernel::{bits32_constant, constant_u32};
use crate::surface::proof::driver::DriveProof as _;
use std::sync::Arc;

mod attempt;
#[path = "proof/driver/claims.rs"]
mod claim_proofs;
#[cfg(test)]
pub(in crate::surface) use claim_proofs::count_flat_proof_units;
pub(in crate::surface) use fixed_state_proofs::{
    FixedStateLoweringOptions, evaluate_fixed_state_array_ref_through_kernel,
    evaluate_fixed_state_expression_through_kernel, evaluate_program_expression_through_kernel,
    evaluate_resource_argument_through_kernel, evaluate_resource_fragment_through_kernel,
    lower_fixed_state_proposition_through_kernel,
    lower_fixed_state_proposition_through_kernel_with,
    lower_fixed_state_proposition_through_kernel_with_facts,
};
mod cursor_execution;
mod execution_planning;
pub(in crate::surface) use execution_planning::probe_open_obligations;
pub(in crate::surface) mod fact_reasoning;
pub(in crate::surface) mod fixed_state_proofs;
mod implicit_solve_scope;
pub use implicit_solve_scope::without_implicit_solve_for_claim;
pub(in crate::surface) mod driver;
mod language_context;
mod proof_object;

pub use proof_object::without_implicit_solve;
#[cfg(test)]
pub(in crate::surface) use proof_object::{
    count_checked_execution_interface_joins, count_checked_expanded_execution_ifs,
    count_finalization_view_constructions, join_arm_effect_facts,
};
mod checked_drivers;
mod execution_state;
mod guarded_consequents;
pub(in crate::surface) mod program_termination;
mod pure_theorems;
pub(in crate::surface) use pure_theorems::kernel_law_index_types;
mod raise_lower_audit;
mod raise_lower_census;
mod resources;
mod selected_arithmetic;
mod signed_definedness;
mod smart_closures;
mod smart_execution;
mod source_context;
mod structural;
mod surface_certificates;
mod surface_construction;
mod surface_lowering;
mod surface_synthesis;
mod theorem_application;
mod timing;
mod wide_arithmetic;
use crate::kernel::fresh_int32_variable_for_propositions;
use crate::kernel::proof::{
    ExceptionalContinuation, ExceptionalEntry, ExecutionFrontier, ExecutionProofCore,
    ExecutionRegionKind, FrontierPosition, LoopControlExit, PersistentOrderedSet,
    PersistentSequence, ProofExecutionContinuation, PureFactStore, exceptional_region,
    old_reference_state,
};

pub(in crate::surface) use crate::kernel::proof::{
    MemoryErasedPropositionKey, memory_erased_proposition_key,
};
use claim_proofs::finish_ordered_proof;
pub(super) use claim_proofs::{
    finish_contract_body_root, prove_claim_by_tactics, prove_claims_by_grouped_script,
    prove_claims_by_implicit_tail,
};
pub(in crate::surface) use cursor_execution::surface_program_point_selector;
#[cfg(test)]
pub(in crate::surface) use cursor_execution::take_step_diagnostic_resource_reads;
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
pub(super) use execution_planning::{StatementPrerequisitePolicy, certified_statement_transitions};
use execution_state::*;
pub(super) use execution_state::{
    capture_prepared_proof_site_expansion, capture_prepared_tactic_expansion,
    capture_program_proof_site_expansion, capture_program_tactic_expansion,
    capture_project_proof_site_expansion, capture_project_tactic_expansion,
};
#[cfg(test)]
pub(super) use fact_reasoning::describe_condition_search_miss;
use fact_reasoning::*;
pub(super) use fact_reasoning::{condition_polarity_equivalent, exactly_available_fact};
use fixed_state_proofs::*;
use language_context::*;
use proof_object::*;
#[cfg(test)]
pub(in crate::surface) use pure_theorems::PROVED_THEOREMS;
pub(super) use pure_theorems::{
    assumed_theorem_certification_authorities, is_kernel_standard_theorem_name,
    pure_theorem_array_refs, pure_theorem_parameter_values, verify_theorem_definition,
    verify_theorem_definitions,
};
#[cfg(test)]
use pure_theorems::{lower_pure_theorem_proposition, pure_theorem_context};
pub(super) use resources::instantiate_composite_resource_body_resources;
use resources::*;
use source_context::SourceContext;
use structural::*;
use surface_certificates::*;
use surface_construction::*;
#[cfg(test)]
pub(super) use surface_synthesis::synthesize_surface_proposition_at_entry_and_post;
#[cfg(test)]
use surface_synthesis::{SURFACE_SYNTHESIS_DEPTH_LIMIT, bitvector_term_is_load_free};
pub(super) use surface_synthesis::{callback_source_name, synthesize_surface_proposition};
use surface_synthesis::{
    surface_synthesis_exhaustion_description, surface_synthesis_failure,
    synthesize_surface_machine_expression,
    synthesize_surface_proposition_with_bound_variable_names,
};
use theorem_application::*;
use timing::TacticTiming;
pub(super) use timing::{SourceSiteKind, source_site_kind};

type NextTopLevelStatement = (
    ExecutionState,
    ExecutionState,
    ProgramStatement,
    Option<ProgramStatement>,
);

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
            format_forall_instantiation_error(error, &|missing| {
                crate::surface::diagnostics::describe_pure_fact_spelled(
                    missing,
                    ParameterBinding::default(),
                )
            })
        })
}

pub(super) fn format_forall_instantiation_error(
    error: crate::kernel::proof::fact_reasoning::ForallInstantiationError,
    spell: &dyn Fn(&Proposition) -> String,
) -> String {
    use crate::kernel::proof::fact_reasoning::ForallInstantiationError as Error;
    match error {
        Error::RequiresUniversal => {
            "`instantiate` requires a universally quantified fact".to_string()
        }
        Error::ArgumentSort => {
            "the argument is not a value of the universal binder's type".to_string()
        }
        // Spelled, not named by kind: "signed less-or-equal is true" does not
        // tell a reader which premise to supply, and a premise the hypothesis
        // owes is exactly what they have to write down.
        Error::MissingGuard(missing) => format!(
            "instantiated premise `{}` does not follow from the listed evidence",
            spell(&missing),
        ),
        Error::SubstitutionRefused(reason) => {
            format!("the universal's body could not be instantiated: {reason}")
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
        let pointer = Address {
            base: "data".into(),
            offset: AddressOffset::Constant(0),
        };
        let load = MachineTerm::MemoryLoad(
            crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
            Box::new(pointer),
            crate::kernel::LoadKind::Int32,
        );

        assert!(bitvector_term_is_load_free(&binary_node!(
            Int32,
            Add,
            Box::new(MachineTerm::Variable(Variable(1))),
            Box::new(MachineTerm::constant(1)),
        )));
        assert!(!bitvector_term_is_load_free(&binary_node!(
            Int32,
            Add,
            Box::new(load),
            Box::new(MachineTerm::constant(1)),
        )));
    }

    #[test]
    fn surface_synthesis_rejects_too_deep_terms_with_a_bounded_reason() {
        let mut term = MachineTerm::Variable(Variable(1));
        for _ in 0..=SURFACE_SYNTHESIS_DEPTH_LIMIT {
            term = binary_node!(
                Int32,
                Add,
                Box::new(term),
                Box::new(MachineTerm::constant(1))
            );
        }
        let proposition = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(term),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        );

        assert!(
            synthesize_surface_proposition(
                &proposition,
                ParameterBinding::default(),
                &ExecutionState::new()
            )
            .is_none()
        );
        let reason = surface_synthesis_failure("could not reconstruct test fact", &proposition);
        assert!(reason.contains("bounded bitvector search"), "{reason}");
        assert!(!reason.contains("Variable("), "{reason}");
    }

    #[test]
    fn state_annotation_rejects_deep_logic_without_using_the_native_stack() {
        let mut surface = ClickProposition::Comparison {
            left: ContractExpression::ProgramBinding("value".to_string()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(
                ProgramValue::Int32(MachineTerm::constant(0)),
            )),
        };
        for _ in 0..=PROGRAM_POINT_ANNOTATION_DEPTH_LIMIT {
            surface = ClickProposition::Not(Box::new(surface));
        }
        let point = ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        };

        let error = surface_at_program_point(&surface, &point)
            .expect_err("deep state annotation must stop structurally");
        assert!(
            error.message().contains("structural depth bound"),
            "{error}"
        );
    }

    #[test]
    fn state_index_finds_a_late_exact_selector_inside_a_quantifier() {
        let early_memory = SymbolicMemory::new().with_block("early", 4);
        let target_memory = SymbolicMemory::new().with_block("target", 4);
        let pointer = Address {
            base: "target".into(),
            offset: AddressOffset::Constant(0),
        };
        let kernel = Proposition::ForAll {
            name: Default::default(),
            var: Variable(7),
            sort: Sort::Bitvector32,
            body: Box::new(Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(MachineTerm::MemoryLoad(
                        crate::kernel::ProgramPoint::at(
                            &(crate::kernel::intern_memory(target_memory.clone())),
                        ),
                        Box::new(pointer),
                        crate::kernel::LoadKind::Int32,
                    )),
                    right: Box::new(MachineTerm::Variable(Variable(7))),
                },
                true,
            )),
        };
        let early = ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        };
        let late = ProgramPointRef {
            region: CodeRegionRef::Region(99),
            kind: ProgramPointKind::Entry,
        };
        let mut states = RecordedStates::new();
        states.insert(early, ExecutionState::new().with_memory(early_memory));
        states.insert(
            late.clone(),
            ExecutionState::new().with_memory(target_memory),
        );

        let (exact, compatible) = state_indexed_selectors(&kernel, &states);
        assert_eq!(
            exact
                .iter()
                .map(|(selector, _)| *selector)
                .collect::<Vec<_>>(),
            vec![&ProgramPointSelector::ProgramPoint(late)]
        );
        assert!(compatible.is_empty());
    }

    #[test]
    fn missing_state_form_reports_a_concise_indexed_failure() {
        let target_memory = SymbolicMemory::new().with_block("target", 4);
        let pointer = Address {
            base: "target".into(),
            offset: AddressOffset::Constant(0),
        };
        let kernel = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::MemoryLoad(
                    crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(target_memory))),
                    Box::new(pointer),
                    crate::kernel::LoadKind::Int32,
                )),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        );
        let state =
            ExecutionState::new().with_memory(SymbolicMemory::new().with_block("current", 4));

        let facts = PureFactStore::from_ordered(&[]);
        let error = checked_surface_comparison_fact_in_state_with_indexed_facts(
            ExecutionView::new(
                &ExecutionFrontier::default(),
                &ExecutionFacts::new(),
                &RecordedStates::new(),
                &SurfacePropositionMap::default(),
                None,
            ),
            &kernel,
            &facts,
            facts.assumptions(),
            ParameterBinding::default(),
            &state,
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
        )
        .expect_err("an unrecorded state should have no surface form");

        assert!(
            error
                .message()
                .contains("0 exact and 0 compatible recorded states"),
            "{error}"
        );
        assert!(!error.message().contains("SymbolicMemory"), "{error}");
    }

    #[test]
    fn state_variant_search_reaches_a_candidate_after_eight() {
        let base = ClickProposition::Comparison {
            left: ContractExpression::ProgramBinding("value".to_string()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(
                ProgramValue::Int32(MachineTerm::constant(0)),
            )),
        };
        let selectors = (0..20)
            .map(|index| {
                ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                })
            })
            .collect::<Vec<_>>();
        let variants = comparison_state_variants(&base, &selectors)
            .expect("comparison should have state variants");
        let position = variants
            .iter()
            .position(|candidate| {
                matches!(
                    candidate,
                    ClickProposition::Comparison {
                        left: ContractExpression::At {
                            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                                region: CodeRegionRef::Region(2),
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
            | InternalProofNode::Cases {
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
        let tactics = [ProofTactic::Step, ProofTactic::Known];
        let source = build_internal_proof(&tactics, "source").expect("source proof should build");
        let generated = build_generated_certificate_proof(&tactics, "generated", 7)
            .expect("generated certificate should build");

        assert_eq!(linear_tactic_coordinates(&source), vec![(0, 0), (1, 1)]);
        assert_eq!(linear_tactic_coordinates(&generated), vec![(0, 7), (1, 7)]);
    }

    #[test]
    fn sequential_control_tactics_build_walk_clone_and_drop_without_deep_recursion() {
        // A script of N sequential `branch`es is a continuation chain N nodes
        // deep. Building, walking, copying and freeing it must not take a
        // Rust stack frame per node: a recursive builder overflowed the main
        // thread's 8 MiB stack at about 250 branches.
        let branches = 2_000;
        let branch = ProofTactic::Branch(ProofBranch {
            ensuring: None,
            then_tactics: vec![ProofTactic::Step],
            else_tactics: vec![ProofTactic::Step],
        });
        let tactics = vec![branch; branches];
        // Each branch spans three source tactics; this is the last `else` step.
        let last_source_index = 3 * (branches - 1) + 2;
        std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(move || {
                let mut proof =
                    build_internal_proof(&tactics, "deep").expect("the chain should build");
                assert!(internal_proof_contains_source_index(
                    &proof,
                    last_source_index
                ));
                let copy = proof.clone();
                detach_generated_suffix_from_source_indices(&mut proof, 0);
                assert!(!internal_proof_contains_source_index(
                    &proof,
                    last_source_index
                ));
                assert!(internal_proof_contains_source_index(
                    &copy,
                    last_source_index
                ));
                set_generated_proof_source_index(&mut proof, 7);
                assert!(internal_proof_contains_source_index(&proof, 7));
                drop(copy);
                drop(proof);
            })
            .expect("the test thread should start")
            .join()
            .expect("a long sequential chain must not overflow a small stack");
    }

    #[test]
    fn deferred_tactics_retain_their_owning_source_occurrence() {
        let mut execution = ExecutionProofState::at_entry(
            ExecutionState::new(),
            ExecutionFrontier::default(),
            RecordedStates::new(),
            SurfacePropositionMap::default(),
            PersistentSequence::default(),
        );
        execution.defer_post_execution(9, 2, PostExecutionTactic::Solve, None);

        let mut deferred_entries = execution.post_execution_tactics.iter();
        let deferred = deferred_entries
            .next()
            .expect("expected one deferred tactic");
        assert!(deferred_entries.next().is_none());
        assert_eq!(deferred.tactic_index, 9);
        assert_eq!(deferred.source_index, 2);
        assert!(matches!(deferred.tactic, PostExecutionTactic::Solve));
    }

    #[test]
    fn timing_classifies_a_have_with_only_simple_tactics_as_simple() {
        let have = ProofTactic::Have(ProofHave {
            proposition: ClickProposition::Comparison {
                left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
            },
            proof: SourceProof::Script(vec![ProofTactic::Known]),
        });

        assert_eq!(source_site_kind(&have), SourceSiteKind::SimpleOperation);
    }

    #[test]
    fn timing_classifies_smart_and_structural_have_sites_separately() {
        let proposition = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
        };
        let smart = ProofTactic::Have(ProofHave {
            proposition: proposition.clone(),
            proof: SourceProof::Tactic(SmartTactic::Solve),
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
                left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
            },
            proof: SourceProof::Script(vec![ProofTactic::Known]),
        });

        assert_eq!(post_execution_tactic_timing(&have), ("have", "control"));
    }

    #[test]
    fn pure_certificate_check_is_transactional() {
        let file = parse(
            r#"
                theorem reflexive(x: int32) {
                    ensures x <= x;
                }
            "#,
        )
        .expect("theorem should parse");
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions())
            .with_contracts(file.contract_definitions(), &file.program_function_names);
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
            ContractEnvironment::new(&context.values, &context.array_refs),
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
            .driver()
            .apply_step(ProofStep::Intro)
            .err()
            .expect("a rejected candidate must not be reported as success");
        assert!(error.message().contains("intro"), "{}", error.message());
        assert!(root.certificate().steps().is_empty());
        let completed = root
            .driver()
            .apply_step(ProofStep::Known)
            .expect("failed validation must not mutate the retained root");
        assert_eq!(
            completed.completed_proposition().unwrap().proposition(),
            &goal
        );
    }

    #[test]
    fn direct_pure_solve_and_solve_retain_checked_simple_proofs() {
        let file = parse(
            r#"
                theorem required(x: int32) {
                    requires x >= 0;
                    ensures x >= 0;
                }

                theorem reflexive(x: int32) {
                    ensures x == x by solve();
                }

                theorem applied(x: int32) {
                    requires x >= 0;
                    ensures x >= 0 by {
                        apply(required(x)) using { x >= 0; }
                    }
                }

                theorem applied_then_solve(x: int32) {
                    requires x >= 0;
                    ensures (x >= 0) and (x >= 0) by {
                        apply(required(x));
                        solve();
                    }
                }

                theorem implication(x: int32) {
                    ensures (x >= 0) implies (x >= 0) by {
                        intro();
                        known();
                    }
                }

                theorem conjunction(x: int32) {
                    requires x >= 0;
                    requires x <= 10;
                    ensures (x >= 0) and (x <= 10) by solve();
                }

                theorem disjunction(x: int32) {
                    requires x >= 0;
                    ensures (x >= 0) or (x < 0);
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
            .with_contracts(file.contract_definitions(), &file.program_function_names);
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
            Some([ProofTactic::Known].as_slice())
        );
        assert_eq!(
            verified[1].proof_tactics().as_deref(),
            Some([ProofTactic::Known].as_slice())
        );
        assert!(matches!(
            verified[2].proof_tactics().as_deref(),
            Some([ProofTactic::ApplyTheoremUsing { .. }])
        ));
        assert!(matches!(
            verified[3].proof_tactics().as_deref(),
            Some([
                ProofTactic::Have(ProofHave { proof: SourceProof::Script(body), .. }),
                ProofTactic::ApplyTheoremUsing { application, premises },
                ProofTactic::Known,
            ]) if matches!(body.as_slice(), [ProofTactic::Known]) && application.name == "required" && premises.len() == 1
        ));
        assert_eq!(
            verified[4].proof_tactics().as_deref(),
            Some([ProofTactic::Intro, ProofTactic::Known].as_slice())
        );
        assert_eq!(
            verified[5].proof_tactics().as_deref(),
            Some([ProofTactic::Known].as_slice())
        );
        assert_eq!(
            verified[6].proof_tactics().as_deref(),
            Some([ProofTactic::Known].as_slice())
        );
        assert!(matches!(
            verified[7].proof_tactics().as_deref(),
            Some([ProofTactic::Contradiction(_)])
        ));
    }

    #[test]
    fn path_aligned_certificates_preserve_branch_structure() {
        let condition = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                ("x".to_string()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
        };
        let known = ProofCertificate::from_proof_tactics(&[ProofTactic::Known])
            .expect("known is a certificate");
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
                    certificate: known,
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
        assert_eq!(then_proof.to_proof_tactics(), vec![ProofTactic::Known]);
        assert_eq!(else_proof.to_proof_tactics(), vec![ProofTactic::Normalize]);
    }

    #[test]
    fn path_aligned_certificates_reject_incompatible_frontiers() {
        let condition = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                ("x".to_string()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
        };
        let other = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                ("y".to_string()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
        };
        let known = ProofCertificate::from_proof_tactics(&[ProofTactic::Known])
            .expect("known is a certificate");
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
                    certificate: known,
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
    /// `cases` on two sides of an available disjunction. A wider `cases`
    /// nests on the left, as `A or B or C` parses: `then_branch` is then
    /// itself a `Cases` on the earlier arms. Its arms rejoin and finish as
    /// a proof `if`'s do.
    Cases {
        index: usize,
        source_index: usize,
        disjunction: ClickProposition,
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
        payload_bindings: [Option<String>; 2],
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

/// Whether the script runner appends the implicit tail to `tactics`.
pub(in crate::surface) fn script_ends_with_implicit_tail(tactics: &[ProofTactic]) -> bool {
    claim_proofs::with_implicit_tail(tactics).1
}

fn build_internal_proof_with_source(
    tactics: &[ProofTactic],
    claim_label: &str,
    source: ProofTacticSource,
) -> Result<InternalProofNode, ClickError> {
    match source {
        ProofTacticSource::SourceSyntax => {
            // The tail's site follows the script's last written tactic, so
            // its execution and closing are charged to a smart budget there.
            let (tactics, _) = claim_proofs::with_implicit_tail(tactics);
            build_internal_proof(&tactics, claim_label)
        }
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
    let mut node = node;
    loop {
        match node {
            InternalProofNode::Done => return,
            InternalProofNode::Match {
                source_index, arms, ..
            } => {
                *source_index = owning_source_index;
                for arm in arms {
                    set_generated_proof_source_index(arm, owning_source_index);
                }
            }
            InternalProofNode::Linear { tactics, .. } => {
                for tactic in tactics {
                    tactic.source_index = owning_source_index;
                }
            }
            InternalProofNode::Open {
                source_index, body, ..
            } => {
                *source_index = owning_source_index;
                set_generated_proof_source_index(body, owning_source_index);
            }
            InternalProofNode::If {
                source_index,
                then_branch,
                else_branch,
                ..
            }
            | InternalProofNode::Cases {
                source_index,
                then_branch,
                else_branch,
                ..
            }
            | InternalProofNode::Branch {
                source_index,
                then_branch,
                else_branch,
                ..
            }
            | InternalProofNode::CallOutcomes {
                source_index,
                returned_branch: then_branch,
                threw_branch: else_branch,
                ..
            } => {
                *source_index = owning_source_index;
                set_generated_proof_source_index(then_branch, owning_source_index);
                set_generated_proof_source_index(else_branch, owning_source_index);
            }
        }
        node = node
            .continuation_mut()
            .expect("only `Done` lacks a continuation");
    }
}

fn detach_generated_suffix_from_source_indices(
    node: &mut InternalProofNode,
    first_generated_tactic_index: usize,
) {
    let detach = |index: usize, source_index: &mut usize| {
        if index >= first_generated_tactic_index {
            *source_index = usize::MAX;
        }
    };
    let mut node = node;
    loop {
        match node {
            InternalProofNode::Done => return,
            InternalProofNode::Match {
                index,
                source_index,
                arms,
                ..
            } => {
                detach(*index, source_index);
                for arm in arms {
                    detach_generated_suffix_from_source_indices(arm, first_generated_tactic_index);
                }
            }
            InternalProofNode::Linear { tactics, .. } => {
                for tactic in tactics {
                    detach(tactic.index, &mut tactic.source_index);
                }
            }
            InternalProofNode::Open {
                index,
                source_index,
                body,
                ..
            } => {
                detach(*index, source_index);
                detach_generated_suffix_from_source_indices(body, first_generated_tactic_index);
            }
            InternalProofNode::If {
                index,
                source_index,
                then_branch,
                else_branch,
                ..
            }
            | InternalProofNode::Cases {
                index,
                source_index,
                then_branch,
                else_branch,
                ..
            }
            | InternalProofNode::Branch {
                index,
                source_index,
                then_branch,
                else_branch,
                ..
            }
            | InternalProofNode::CallOutcomes {
                index,
                source_index,
                returned_branch: then_branch,
                threw_branch: else_branch,
                ..
            } => {
                detach(*index, source_index);
                detach_generated_suffix_from_source_indices(
                    then_branch,
                    first_generated_tactic_index,
                );
                detach_generated_suffix_from_source_indices(
                    else_branch,
                    first_generated_tactic_index,
                );
            }
        }
        node = node
            .continuation_mut()
            .expect("only `Done` lacks a continuation");
    }
}

impl InternalProofNode {
    /// The rest of the proof after this node, or `None` for `Done`.
    fn continuation_mut(&mut self) -> Option<&mut Box<InternalProofNode>> {
        match self {
            InternalProofNode::Done => None,
            InternalProofNode::Match { continuation, .. }
            | InternalProofNode::Linear { continuation, .. }
            | InternalProofNode::Open { continuation, .. }
            | InternalProofNode::If { continuation, .. }
            | InternalProofNode::Cases { continuation, .. }
            | InternalProofNode::Branch { continuation, .. }
            | InternalProofNode::CallOutcomes { continuation, .. } => Some(continuation),
        }
    }
}

/// The empty proof, for a driver that holds a borrowed node after consuming
/// the rest of a script.
static DONE_PROOF: InternalProofNode = InternalProofNode::Done;

impl Clone for InternalProofNode {
    /// Copies the continuation chain node by node in a loop, as `Drop` frees
    /// it, so a long run of sequential control tactics is copied without a
    /// Rust stack frame per node.
    fn clone(&self) -> Self {
        let mut copies = Vec::new();
        let mut node = self;
        loop {
            let (copy, continuation) = match node {
                InternalProofNode::Done => break,
                InternalProofNode::Match {
                    index,
                    source_index,
                    proof_match,
                    arms,
                    continuation,
                } => (
                    InternalProofNode::Match {
                        index: *index,
                        source_index: *source_index,
                        proof_match: proof_match.clone(),
                        arms: arms.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    },
                    continuation,
                ),
                InternalProofNode::Linear {
                    tactics,
                    continuation,
                } => (
                    InternalProofNode::Linear {
                        tactics: tactics.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    },
                    continuation,
                ),
                InternalProofNode::Open {
                    index,
                    source_index,
                    resource,
                    body,
                    continuation,
                } => (
                    InternalProofNode::Open {
                        index: *index,
                        source_index: *source_index,
                        resource: resource.clone(),
                        body: body.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    },
                    continuation,
                ),
                InternalProofNode::If {
                    index,
                    source_index,
                    condition,
                    ensuring,
                    then_branch,
                    else_branch,
                    continuation,
                } => (
                    InternalProofNode::If {
                        index: *index,
                        source_index: *source_index,
                        condition: condition.clone(),
                        ensuring: ensuring.clone(),
                        then_branch: then_branch.clone(),
                        else_branch: else_branch.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    },
                    continuation,
                ),
                InternalProofNode::Cases {
                    index,
                    source_index,
                    disjunction,
                    then_branch,
                    else_branch,
                    continuation,
                } => (
                    InternalProofNode::Cases {
                        index: *index,
                        source_index: *source_index,
                        disjunction: disjunction.clone(),
                        then_branch: then_branch.clone(),
                        else_branch: else_branch.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    },
                    continuation,
                ),
                InternalProofNode::Branch {
                    index,
                    source_index,
                    ensuring,
                    then_branch,
                    else_branch,
                    continuation,
                } => (
                    InternalProofNode::Branch {
                        index: *index,
                        source_index: *source_index,
                        ensuring: ensuring.clone(),
                        then_branch: then_branch.clone(),
                        else_branch: else_branch.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    },
                    continuation,
                ),
                InternalProofNode::CallOutcomes {
                    index,
                    source_index,
                    payload_bindings,
                    returned_branch,
                    threw_branch,
                    continuation,
                } => (
                    InternalProofNode::CallOutcomes {
                        index: *index,
                        source_index: *source_index,
                        payload_bindings: payload_bindings.clone(),
                        returned_branch: returned_branch.clone(),
                        threw_branch: threw_branch.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    },
                    continuation,
                ),
            };
            copies.push(copy);
            node = continuation;
        }
        link_proof_segments(copies)
    }
}

/// Links `segments`, each holding a `Done` continuation, into one chain in
/// order, from the back.
fn link_proof_segments(mut segments: Vec<InternalProofNode>) -> InternalProofNode {
    let mut proof = InternalProofNode::Done;
    while let Some(mut segment) = segments.pop() {
        **segment
            .continuation_mut()
            .expect("every segment holds a continuation") = proof;
        proof = segment;
    }
    proof
}

impl Drop for InternalProofNode {
    /// Unlinks the continuation chain so dropping a long run of sequential
    /// control tactics takes no Rust stack frame per node.
    fn drop(&mut self) {
        let Some(continuation) = self.continuation_mut() else {
            return;
        };
        if matches!(continuation.as_ref(), InternalProofNode::Done) {
            return;
        }
        let mut next = std::mem::replace(continuation.as_mut(), InternalProofNode::Done);
        while let Some(continuation) = next.continuation_mut() {
            next = std::mem::replace(continuation.as_mut(), InternalProofNode::Done);
        }
    }
}

/// Each control tactic holds the rest of its script as its continuation, so
/// a script of N sequential control tactics is a chain N nodes deep. The
/// chain is built front to back in a loop and linked from the back; only a
/// written nesting (an arm, a case, an `open` body) recurses.
fn build_internal_proof_at(
    tactics: &[ProofTactic],
    index_offset: usize,
    source_index_offset: usize,
) -> Result<InternalProofNode, ClickError> {
    let mut segments = Vec::new();
    let (mut tactics, mut index_offset, mut source_index_offset) =
        (tactics, index_offset, source_index_offset);
    loop {
        let Some((control_index, control_tactic)) =
            tactics.iter().enumerate().find(|(_, tactic)| {
                matches!(
                    tactic,
                    ProofTactic::If(_)
                        | ProofTactic::Cases(_)
                        | ProofTactic::Branch(_)
                        | ProofTactic::CallOutcomes(_)
                        | ProofTactic::Open(_)
                        | ProofTactic::Match(_)
                )
            })
        else {
            if !tactics.is_empty() {
                segments.push(InternalProofNode::Linear {
                    tactics: indexed_linear_tactics(tactics, index_offset, source_index_offset),
                    continuation: Box::new(InternalProofNode::Done),
                });
            }
            break;
        };

        let index = index_offset + control_index;
        let source_index = source_index_offset
            + tactics[..control_index]
                .iter()
                .map(source_tactic_width)
                .sum::<usize>();
        if control_index > 0 {
            segments.push(InternalProofNode::Linear {
                tactics: indexed_linear_tactics(
                    &tactics[..control_index],
                    index_offset,
                    source_index_offset,
                ),
                continuation: Box::new(InternalProofNode::Done),
            });
        }
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
                    continuation: Box::new(InternalProofNode::Done),
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
                    continuation: Box::new(InternalProofNode::Done),
                }
            }
            ProofTactic::Cases(proof_cases) => build_cases_node(
                proof_cases.arms(),
                index,
                source_index,
                source_index,
                source_index + 1,
            )?,
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
                    continuation: Box::new(InternalProofNode::Done),
                }
            }
            ProofTactic::CallOutcomes(outcomes) => {
                let returned_width = source_tactic_count(&outcomes.returned_tactics);
                InternalProofNode::CallOutcomes {
                    index,
                    source_index,
                    payload_bindings: outcomes.payload_bindings.clone(),
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
                    continuation: Box::new(InternalProofNode::Done),
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
                continuation: Box::new(InternalProofNode::Done),
            },
            _ => unreachable!("control-tactic search only returns structured tactics"),
        };
        segments.push(control);
        tactics = &tactics[control_index + 1..];
        index_offset = index + 1;
        source_index_offset = source_index + source_tactic_width(control_tactic);
    }

    Ok(link_proof_segments(segments))
}

/// Builds `cases` over `arms`, whose tactics start at source index
/// `arms_source_start`, as nested two-way splits: the last arm against the
/// disjunction of the earlier ones, which split again inside the left arm.
/// Only the outermost split is the written tactic; the inner ones are
/// numbered past every source position, so no site lookup names them. Each
/// inner number is taken from the written tactic's `written_source_index` and
/// the inner split's arm count, which falls by one at each level, so every
/// level of a wide `cases` has its own.
fn build_cases_node(
    arms: &[ProofCaseArm],
    index: usize,
    source_index: usize,
    written_source_index: usize,
    arms_source_start: usize,
) -> Result<InternalProofNode, ClickError> {
    let (last, earlier) = arms
        .split_last()
        .expect("the parser gives `cases` at least two arms");
    let earlier_width = earlier
        .iter()
        .map(|arm| source_tactic_count(arm.tactics()))
        .sum::<usize>();
    let then_branch = if let [only] = earlier {
        build_internal_proof_at(only.tactics(), index + 1, arms_source_start)?
    } else {
        // The earlier arms split again inside this arm and rejoin there
        // when the outer split's arms do; arms that finish the proof finish
        // it on their own as before.
        let mut inner = build_cases_node(
            earlier,
            index + 1,
            SYNTHETIC_CASES_SOURCE_INDEX_BASE
                + written_source_index * MAX_SYNTHETIC_CASES_DEPTH
                + earlier.len(),
            written_source_index,
            arms_source_start,
        )?;
        if let InternalProofNode::Cases { continuation, .. } = &mut inner {
            **continuation = InternalProofNode::Linear {
                tactics: Vec::new(),
                continuation: Box::new(InternalProofNode::Done),
            };
        }
        inner
    };
    Ok(InternalProofNode::Cases {
        index,
        source_index,
        disjunction: ProofCases::new(arms.to_vec()).disjunction(),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(build_internal_proof_at(
            last.tactics(),
            index + 1,
            arms_source_start + earlier_width,
        )?),
        continuation: Box::new(InternalProofNode::Done),
    })
}

/// Where the inner splits of a wide `cases` are numbered: past every source
/// script and every synthetic tactic.
const SYNTHETIC_CASES_SOURCE_INDEX_BASE: usize = usize::MAX / 4 * 3;
const MAX_SYNTHETIC_CASES_DEPTH: usize = 1 << 16;

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
pub(super) const SYNTHETIC_SOURCE_INDEX_BASE: usize = usize::MAX / 2;

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
    let mut node = node;
    loop {
        node = match node {
            InternalProofNode::Done => return false,
            InternalProofNode::Match {
                source_index,
                arms,
                continuation,
                ..
            } => {
                if *source_index == wanted
                    || arms
                        .iter()
                        .any(|arm| internal_proof_contains_source_index(arm, wanted))
                {
                    return true;
                }
                continuation
            }
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                if tactics
                    .iter()
                    .any(|tactic| indexed_tactic_contains_source_index(tactic, wanted))
                {
                    return true;
                }
                continuation
            }
            InternalProofNode::Open {
                body, continuation, ..
            } => {
                if internal_proof_contains_source_index(body, wanted) {
                    return true;
                }
                continuation
            }
            InternalProofNode::If {
                then_branch,
                else_branch,
                continuation,
                ..
            }
            | InternalProofNode::Cases {
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
                if internal_proof_contains_source_index(then_branch, wanted)
                    || internal_proof_contains_source_index(else_branch, wanted)
                {
                    return true;
                }
                continuation
            }
        };
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
    pub(super) fn key(self) -> FunctionContractClaimKey {
        match self {
            Self::Ensure(index, _) => FunctionContractClaimKey::Ensure(index),
            Self::ExceptionalEnsure(index, _) => FunctionContractClaimKey::ExceptionalEnsure(index),
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

    pub(super) fn applies_to(self, outcome: &FunctionOutcome) -> bool {
        match (self, outcome) {
            (Self::Ensure(_, _), FunctionOutcome::Return { .. })
            | (Self::ExceptionalEnsure(_, _), FunctionOutcome::Throw { .. }) => true,
            (Self::Ensure(_, clause), FunctionOutcome::Throw { .. }) => clause.borrowed(),
            _ => false,
        }
    }

    pub(super) fn is_vacuous_for(self, outcome: &FunctionOutcome) -> bool {
        match (self, outcome) {
            (Self::Ensure(_, clause), FunctionOutcome::Throw { .. }) => !clause.borrowed(),
            (Self::ExceptionalEnsure(_, _), FunctionOutcome::Return { .. }) => true,
            _ => false,
        }
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
    pub(in crate::surface) completion: Option<crate::kernel::WholeContractRoot>,
    pub(in crate::surface) strategy_root: Option<crate::kernel::WholeContractRoot>,
    pub(in crate::surface) cases: Arc<crate::kernel::PreparedContractEntryCases>,
    pub(in crate::surface) state: ExecutionState,
    pub(in crate::surface) arguments: Vec<ProgramExpression>,
    pub(in crate::surface) pure_facts: PureFactList,
}

impl PartialEq for ProofEntryContext {
    fn eq(&self, other: &Self) -> bool {
        self.state == other.state
            && self.arguments == other.arguments
            && self.pure_facts == other.pure_facts
    }
}

impl Eq for ProofEntryContext {}

/// The initial context already has one owner per source function. Reuse its
/// opened native entry directly, without a second declaration-key cache.
#[derive(Clone, Default)]
pub(super) struct SharedOpenedClaimEntry(
    Arc<std::sync::Mutex<Option<crate::kernel::proof::OpenedContractEntry>>>,
);

impl SharedOpenedClaimEntry {
    pub(super) fn get_or_open(
        &self,
        open: impl FnOnce() -> Result<crate::kernel::proof::OpenedContractEntry, ClickError>,
    ) -> Result<crate::kernel::proof::OpenedContractEntry, ClickError> {
        let mut slot = self.0.lock().expect("opened contract entry");
        if let Some(entry) = slot.as_ref() {
            return Ok(entry.clone());
        }
        let entry = open()?;
        *slot = Some(entry.clone());
        Ok(entry)
    }
}

#[derive(Clone)]
pub(super) struct InitialClaimContext {
    pub(super) opened_entry: SharedOpenedClaimEntry,
    pub(super) state: ExecutionState,
    pub(super) arguments: Vec<ProgramExpression>,
    /// The entry facts, with the context the setup built from them kept
    /// for the proof and certification to extend.
    pub(super) pure_facts: PureFactList,
    pub(super) entry_fact_origins: Vec<EntryFactOrigin>,
    pub(super) surface_propositions: SurfacePropositionMap,
}

#[cfg(test)]
pub(super) fn initial_claim_context(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
) -> Result<
    (
        ExecutionState,
        Vec<ProgramExpression>,
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

/// The surface spelling `name as int32 == 0 or name as int32 == 1` of a
/// `bool` parameter's range entry fact (rule C1).
fn bool_range_surface(name: &str) -> ClickProposition {
    let cast = ContractExpression::CUnary {
        operand: Box::new(ContractExpression::ProgramBinding(name.to_string())),
        lowered: ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Variable(name.into())),
            target_type: crate::kernel::ProgramType::Int32,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    };
    let equals = |constant: &str| ClickProposition::Comparison {
        left: cast.clone(),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::IntegerLiteral(constant.to_string()),
    };
    ClickProposition::Or(Box::new(equals("0")), Box::new(equals("1")))
}

/// The hosted boundary supplies the one stream exported by the projected
/// header. A main contract can name it, but cannot supply its own inputs.
fn bind_hosted_startup(
    state: ExecutionState,
    function: &FunctionBlock,
    parsed: &crate::languages::interface::ImportedFunction,
) -> Result<ExecutionState, ClickError> {
    use crate::kernel::{AlgebraicTerm, AlgebraicTermNode, ResourceFieldType, ResourceInstance};
    let invalid = || {
        ClickError::new(
            "program-entry main currently requires no parameters or preconditions; ownership comes from startup",
        )
    };
    if !parsed.parameters().is_empty() {
        return Err(invalid());
    }
    let requirement = match function.requires() {
        [] => return Ok(state),
        [Requirement::Resource(requirement @ ResourceClause::Named { .. })] => requirement,
        _ => return Err(invalid()),
    };
    let Some(ProgramValue::Pointer(stdout)) = parsed
        .globals()
        .get("stdout")
        .and_then(|global| global.hosted_stdout())
    else {
        return Err(invalid());
    };
    let atom = super::lowering::lower_resource_clause_at_state(
        requirement,
        ParameterBinding::new(&[], &[]),
        &state,
    )?;
    let Resource::Instance(instance) = atom.resource() else {
        return Err(invalid());
    };
    if instance.name() != "stream" || !instance.resource_arguments().is_empty() {
        return Err(invalid());
    }
    let arguments = instance.arguments().native_values();
    let [AlgebraicValue::Program(ProgramValue::Pointer(file))] = arguments.as_ref() else {
        return Err(invalid());
    };
    if file.address() != stdout.address() {
        return Err(ClickError::new(
            "program-entry stream ownership requires the hosted stdout handle",
        ));
    }
    let [(field, ResourceFieldType::Algebraic(history))] = instance.schema().fields() else {
        return Err(invalid());
    };
    if field != "write_history" {
        return Err(invalid());
    }
    let empty = AlgebraicValue::Algebraic(AlgebraicTerm {
        algebraic_type: history.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Nil".to_string(),
            fields: Vec::new(),
        },
    });
    let stream = ResourceInstance::new(
        instance.identity(),
        instance.name().to_string(),
        instance.arguments().clone(),
        instance.schema().clone(),
        vec![empty].into(),
    )
    .ok_or_else(invalid)?;
    // The entry state has static storage and no stream instance yet.
    let resources = state
        .resources()
        .clone()
        .unchecked_with_fact(ResourceFact::own(Resource::Instance(stream)));
    Ok(state.with_resource_context(resources))
}

pub(super) fn initial_claim_context_with_caller_owner(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    caller_owner: Option<&CallerSourceOwnerId>,
) -> Result<InitialClaimContext, ClickError> {
    let (mut state, arguments, entry_assumptions) = if let Some(startup) =
        &parsed_function.program_entry_state
    {
        let state = crate::kernel::initialize_program_function_globals(
            &startup.as_ref().clone().with_population_creation_tracking(),
            &parsed_function.to_kernel_function(),
        );
        (
            bind_hosted_startup(state, function_block, parsed_function)?,
            vec![],
            PureFactContext::new(),
        )
    } else {
        let authority_definitions = crate::surface::verification::composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )?;
        let (requires, _, ensures, exceptional, mutable, claims, supported, _, _) =
            function_contract_summary(
                function_block,
                parsed_function,
                spec_definitions,
                resource_environment,
            )?;
        let declared = parsed_function
            .to_kernel_function()
            .with_contract(requires, ensures, mutable, claims, supported)
            .with_exceptional_ensures(exceptional);
        initial_call_state(
            function_block.requires(),
            parsed_function.parameters(),
            &declared,
            &authority_definitions,
            spec_definitions,
        )?
    };
    // The entry lowers its requirements one at a time; the index lets each
    // read only the parameters it names.
    let parameter_index = crate::surface::ParameterIndex::new(parsed_function.parameters());
    let parameter_binding = ParameterBinding::new(parsed_function.parameters(), &arguments)
        .with_index(&parameter_index);
    crate::surface::proof_diagnostics::render::enter_ambient_naming(
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        &state,
    );
    crate::surface::diagnostics::enter_ambient_object_fields(parsed_function);
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
    // Predicate facts carry their resource-state state opaquely. Register
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
    // Keep an authority-only state before folded composite cells or
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
        parameter_binding,
        state,
        claim_label,
        spec_definitions,
        &entry_assumptions,
    )?;
    let include_owned_composite_cores = Some(resources::OwnedCores::AttachedToOwner);
    let mut projection_state = state.clone();
    for iteration in 0..=function_block.requires().len() {
        if iteration > 0
            && requirement_propositions(
                function_block.requires(),
                parameter_binding,
                &projection_state,
                spec_definitions,
            )
            .is_ok()
        {
            break;
        }
        let available_pure_facts = available_initial_requirement_propositions(
            function_block.requires(),
            parameter_binding,
            &projection_state,
            spec_definitions,
        );
        let projected = project_initial_composite_resource_cores(
            resource_environment,
            parameter_binding,
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
    state = state.with_memory_of(&projection_state);
    let lowered_requirement_facts =
        crate::surface::lowering::requirement_propositions_with_sources_and_assumptions(
            function_block.requires(),
            parameter_binding,
            &state,
            spec_definitions,
            &PureFactContext::new(),
        )?;
    let mut requirement_pure_facts = Vec::with_capacity(lowered_requirement_facts.len());
    let mut entry_fact_origins = Vec::with_capacity(lowered_requirement_facts.len());
    let mut surface_propositions = SurfacePropositionMap::default();
    for lowered in lowered_requirement_facts {
        // Retain the producer's exact principal, including its captured count
        // state. Re-lowering the source would allocate a different lineage.
        if matches!(
            lowered.role,
            crate::surface::lowering::LoweredRequirementFactRole::Principal
        ) {
            let surface = match &function_block.requires()[lowered.source_ordinal] {
                Requirement::Proposition(proposition) => Some(proposition.clone()),
                Requirement::LoadableSegment { segment } => Some(ClickProposition::Loadable {
                    segment: segment.clone(),
                }),
                Requirement::Resource(_) => None,
            };
            if let Some(surface) = surface
                && !click_proposition_mentions_defined(&surface)
            {
                surface_propositions.record_lowering(&surface, &lowered.proposition)?;
            }
        }
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
    // Each `bool` parameter's cast has the range `flag as int32 == 0 or
    // flag as int32 == 1` (rule C1), filed below with the narrow ranges;
    // without it a disjunction such as `result == 0 or result == 1` would
    // need an explicit case split on the parameter. Its surface spelling is
    // recorded below so a proof search can case on it.
    let bool_range_facts = parsed_function
        .parameters()
        .iter()
        .zip(&arguments)
        .filter(|(parameter, _)| {
            matches!(
                parameter.interface_type(),
                crate::languages::interface::InterfaceType::Bool
            )
        })
        .filter_map(|(parameter, argument)| match argument {
            ProgramExpression::Value(value) => crate::kernel::program_bool_cast_range_facts(value)
                .and_then(|facts| facts.last().cloned())
                .map(|fact| (bool_range_surface(parameter.name()), fact)),
            _ => None,
        })
        .collect::<Vec<_>>();
    // A `bool` parameter's cast range is likewise a derived entry fact the
    // kernel states from the parameter's value (rule C1b). A narrow integer
    // parameter is a value of its own format, whose range is the format's.
    for argument in &arguments {
        if let ProgramExpression::Value(value) = argument
            && let Some(facts) = crate::kernel::program_bool_cast_range_facts(value)
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
    // Every requirement below is lowered at `state` with these arguments, so
    // one lowering state serves them all.
    let lowering_state = crate::surface::lowering::RequirementLoweringState::default();
    let lower_one = |requirement: &Requirement| {
        crate::surface::lowering::requirement_propositions_sharing_lowering_state(
            std::slice::from_ref(requirement),
            parameter_binding,
            &state,
            spec_definitions,
            &requirement_context,
            &lowering_state,
        )
        .map(|facts| {
            facts
                .into_iter()
                .map(|fact| fact.proposition)
                .collect::<Vec<_>>()
        })
    };
    let folded_defined_facts = function_block
        .requires()
        .iter()
        .filter(|requirement| {
            matches!(
                requirement,
                Requirement::Proposition(surface) if click_proposition_mentions_defined(surface)
            )
        })
        .map(lower_one)
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    for (surface, kernel) in &bool_range_facts {
        surface_propositions.record_lowering(surface, kernel)?;
    }
    // Two requirements can lower to the same fact (`requires viewable(a[0..n])`
    // beside `views a[0..n]`, and their shared range guards). Resource
    // projection keeps one occurrence of each fact and appends its own, so
    // drop repeats here together with their origins: each retained fact keeps
    // its first source, and the origins stay aligned with the projected list.
    let mut seen = BTreeSet::new();
    (requirement_pure_facts, entry_fact_origins) = requirement_pure_facts
        .into_iter()
        .zip(entry_fact_origins)
        .filter(|(fact, _)| seen.insert(fact.clone()))
        .unzip();
    let requirement_facts = PureFactList::from(requirement_pure_facts);
    state = project_initial_composite_resource_cores(
        resource_environment,
        parameter_binding,
        state,
        &requirement_facts,
        claim_label,
        include_owned_composite_cores,
        spec_definitions,
    )?;
    requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        parameter_binding,
        &state,
        &requirement_facts,
        spec_definitions,
        claim_label,
    )?
    .into_vec();
    debug_assert!(requirement_pure_facts.len() >= entry_fact_origins.len());
    entry_fact_origins.resize(requirement_pure_facts.len(), EntryFactOrigin::Derived);
    let definedness_state = project_initial_composite_resource_cores(
        resource_environment,
        parameter_binding,
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
                parameter_binding,
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
        parameter_binding,
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
        entry_pure_facts.store(),
        include_owned_composite_cores,
        claim_label,
        &entry_authority_state.resources().clone(),
        &entry_authority_state,
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
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement else {
            continue;
        };
        record_initial_composite_surface_facts(
            resource_environment,
            resource,
            parameter_binding,
            &state,
            requirement_pure_facts.store(),
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
        }
    }
    // Publishing an arm fact can also materialize consequences of entry
    // requirements. Both the published facts and their consequences are derived.
    entry_fact_origins.resize(requirement_pure_facts.len(), EntryFactOrigin::Derived);
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
        opened_entry: SharedOpenedClaimEntry::default(),
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
    parsed_function: &crate::languages::interface::ImportedFunction,
    state: &ExecutionState,
    arguments: &[ProgramExpression],
    assumptions: &crate::kernel::PureFactContext,
) -> Result<(), ClickError> {
    let parameters = parsed_function.parameters();
    let parameter_index = crate::surface::ParameterIndex::new(parameters);
    let parameter_binding =
        ParameterBinding::new(parameters, arguments).with_index(&parameter_index);
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
            .all(crate::surface::validation::program_expression_reads_no_memory);
        if !fixed_place {
            continue;
        }
        let Ok(fact) = crate::surface::lowering::lower_resource_clause_at_state(
            resource,
            parameter_binding,
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
    let spelled = |range: &crate::kernel::MemoryRange| {
        written
            .iter()
            .find(|(candidate, _)| candidate == range)
            .map(|(_, segment)| crate::surface::diagnostics::describe_contract_segment(segment))
            .unwrap_or_else(|| {
                crate::surface::diagnostics::describe_memory_range(range, parameter_binding)
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
/// [`explicit_entry_loadability_facts`] below takes only an unconditional,
/// conjunctive loadability requirement as a checked read view.  This keeps
/// unrelated conjuncts from disappearing merely because one projected atom was removed.
fn entry_pure_fact_without_unconditional_loadability(
    proposition: &Proposition,
) -> Option<Proposition> {
    match proposition {
        Proposition::MemoryLoadable { .. } => None,
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
        ClickProposition::Value(_) => {}
        ClickProposition::Loadable { segment } => segments.push(segment.clone()),
        ClickProposition::And(left, right) => {
            collect_conjunctive_loadability_segments(left, segments);
            collect_conjunctive_loadability_segments(right, segments);
        }
        // A loadability atom under a branch, negation, quantifier, state,
        // or range binder is not unconditional entry authority.
        ClickProposition::Comparison { .. }
        | ClickProposition::FloatClassification { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::ResourceViewable { .. }
        | ClickProposition::Contains { .. }
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
    parsed_function: &crate::languages::interface::ImportedFunction,
    arguments: &[ProgramExpression],
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<Proposition>, ClickError> {
    // Every requirement is lowered at `state` with these arguments, so one
    // lowering state serves them all; a set keeps each fact once.
    let lowering_state = crate::surface::lowering::RequirementLoweringState::default();
    let lower_one = |requirement: &Requirement| {
        crate::surface::lowering::requirement_propositions_sharing_lowering_state(
            std::slice::from_ref(requirement),
            ParameterBinding::new(parsed_function.parameters(), arguments),
            state,
            spec_definitions,
            &PureFactContext::new(),
            &lowering_state,
        )
        .map(|facts| facts.into_iter().map(|fact| fact.proposition))
    };
    let mut facts = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for requirement in function_block.requires() {
        match requirement {
            Requirement::LoadableSegment { .. } => {
                let lowered = lower_one(requirement)?;
                for fact in lowered {
                    if matches!(fact, Proposition::MemoryLoadable { .. })
                        && seen.insert(fact.clone())
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
                    let lowered = lower_one(&loadable)?;
                    for fact in lowered {
                        if matches!(fact, Proposition::MemoryLoadable { .. })
                            && seen.insert(fact.clone())
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
    parsed_function: &crate::languages::interface::ImportedFunction,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    state: ExecutionState,
    arguments: &[ProgramExpression],
    pure_facts: &PureFactStore,
    include_owned_composite_cores: Option<resources::OwnedCores>,
    claim_label: &str,
    entry_resources: &ResourceContext,
    entry_memory_state: &ExecutionState,
) -> Result<(ExecutionState, Vec<Proposition>, Vec<Proposition>), ClickError> {
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
                Resource::Instance(_) | Resource::Memory(_) | Resource::PopulationAuthority(_)
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
        .occurrences()
        .filter_map(|fact| {
            let Proposition::MemoryLoadable { base, bytes, .. } = fact else {
                return None;
            };
            let range = match bytes.native_compat() {
                binary_term!(Int32, Multiply, left, right)
                    if **right == MachineTerm::constant(ProgramType::Int32.byte_width()) =>
                {
                    MemoryRange::new(
                        base.clone(),
                        MachineTerm::constant(0),
                        left.as_ref().clone(),
                    )
                }
                binary_term!(Int32, Multiply, left, right)
                    if **left == MachineTerm::constant(ProgramType::Int32.byte_width()) =>
                {
                    MemoryRange::new(
                        base.clone(),
                        MachineTerm::constant(0),
                        right.as_ref().clone(),
                    )
                }
                bits32_constant!(bytes)
                    if constant_u32(*bytes).is_multiple_of(ProgramType::Int32.byte_width()) =>
                {
                    MemoryRange::new(
                        base.clone(),
                        MachineTerm::constant(0),
                        MachineTerm::constant(
                            constant_u32(*bytes) / ProgramType::Int32.byte_width(),
                        ),
                    )
                }
                _ => MemoryRange::new_with_element_width(
                    base.clone(),
                    MachineTerm::constant(0),
                    bytes.native_compat().clone(),
                    1,
                ),
            };
            Some(ResourceFact::view_memory(range))
        })
        .collect::<Vec<_>>();
    let assumptions = pure_facts.assumptions().clone();
    let mut evaluation_state = state.clone().with_resource_context(
        ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_facts(explicit_entry_facts)
            .unchecked_with_facts(precondition_read_facts),
    );
    // The entry memory is the entry state's, so stand where that state
    // stood rather than at a new point that returns to older memory.
    evaluation_state = evaluation_state.with_memory_of(entry_memory_state);
    for parameter in parsed_function.parameters() {
        if let Some(value) = values.get(parameter.name()) {
            evaluation_state = evaluation_state.with_local(parameter.binding_name(), value.clone());
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
            &assumptions.clone().assume_entry_clause_spans(),
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
    let evaluated = crate::kernel::admit_declared_entry_resources(
        evaluated,
        &entry_clauses,
        &evaluation_state,
        &definitions,
        &assumptions,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` setup failed: {}",
            crate::surface::diagnostics::describe_runtime_error(&error, parameter_binding)
        ))
    })?;
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
        ClickProposition::Value(expression) => {
            let mut found = false;
            fixed_state_proofs::conversion_conditions::walk_written_expressions(
                expression,
                &mut |term| {
                    if let ContractExpression::Proposition(body) = term {
                        found |= click_proposition_mentions_defined(body);
                    }
                },
            );
            found
        }
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
        | ClickProposition::ResourceViewable { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::PredicateCall { .. } => false,
    }
}

pub(in crate::surface) fn available_initial_requirement_propositions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
) -> Vec<Proposition> {
    // Each requirement is lowered on its own, at one shared lowering state;
    // a set keeps the first of each proposition without comparing every
    // pair.
    let lowering_state = crate::surface::lowering::RequirementLoweringState::default();
    let mut propositions = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for requirement in requires {
        let Ok(lowered) = crate::surface::lowering::requirement_propositions_sharing_lowering_state(
            std::slice::from_ref(requirement),
            parameter_binding,
            state,
            spec_definitions,
            &PureFactContext::new(),
            &lowering_state,
        ) else {
            continue;
        };
        for fact in lowered {
            if seen.insert(fact.proposition.clone()) {
                propositions.push(fact.proposition);
            }
        }
    }
    propositions
}

fn canonical_claim_caller_state(
    state: ExecutionState,
    has_verified_loops: bool,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    pure_facts: &(impl PropositionSource + ?Sized),
    claim_label: &str,
) -> Result<ExecutionState, ClickError> {
    if !has_verified_loops {
        return Ok(state);
    }
    let entry = program_function_contract_entry_state(
        &state,
        function,
        arguments,
        &assumptions_from_propositions(pure_facts),
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` {message}")))?;
    Ok(state.with_resource_context(entry.resources().clone()))
}

fn install_borrowed_contract_inputs(
    state: ExecutionState,
    function: &ProgramFunction,
    pure_facts: &(impl PropositionSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
    proof_label: &str,
) -> Result<ExecutionState, ClickError> {
    if let Some(message) = crate::kernel::guard_contract_refusal(function.contract_interface()) {
        return Err(ClickError::new(format!("`{proof_label}` {message}")));
    }
    crate::kernel::execution_state_with_borrowed_contract_inputs(
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

pub(super) fn prove_claim_by_implicit_tail(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    // The implicit tail executes the remaining C, then solves each goal.
    let tactics = [ProofTactic::SmartExecute, ProofTactic::ImplicitSolve];
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
    if function_block.structural_clauses().any_loop() {
        for theorem in &mut theorems.theorems {
            theorem.proof_kind = ProofKind::LoopVerification;
        }
    }
    Ok(theorems.theorems)
}

pub(super) fn prove_claim_by_solve(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    if count_loop_regions(parsed_function) != 0 {
        return Err(ClickError::new(format!(
            "`solve` does not prove loop-backed claims for `{claim_label}`; omit the proof"
        )));
    }

    let tactics = [ProofTactic::Solve];
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
        theorem.proof_kind = ProofKind::Solve;
    }
    Ok(theorems.theorems)
}

/// An explicit per-claim proof script. The completed proof unit is the
/// semantic result; retained evidence is serialized only for expansion.
#[allow(clippy::too_many_arguments)]
pub(super) fn prove_claim_by_script(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
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
    /// Set while one loop preservation proof is checked, after a `cases` in
    /// it rejoined its arms: the written tactic index of the last such
    /// `cases`.
    static PRESERVATION_CASES_REJOINED: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// Restores the previous note when the check of a preservation proof ends.
struct PreservationCasesRejoined(Option<usize>);

impl Drop for PreservationCasesRejoined {
    fn drop(&mut self) {
        PRESERVATION_CASES_REJOINED.with(|note| note.set(self.0));
    }
}

/// Starts the check of one preservation proof with no `cases` rejoined yet,
/// for as long as the returned guard lives.
fn begin_preservation_cases_note() -> PreservationCasesRejoined {
    PreservationCasesRejoined(PRESERVATION_CASES_REJOINED.with(|note| note.replace(None)))
}

/// Notes that the `cases` written at `index` rejoined its arms. A path that
/// leaves it keeps only the facts every arm proved, so a back edge that then
/// fails to close says so.
fn note_preservation_cases_rejoined(index: usize) {
    PRESERVATION_CASES_REJOINED.with(|note| note.set(Some(index)));
}

/// The written tactic index of the last `cases` that rejoined its arms in the
/// preservation proof under check.
fn preservation_cases_rejoined() -> Option<usize> {
    PRESERVATION_CASES_REJOINED.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(in crate::surface) use proof_object::take_outcome_fact_reads;

#[cfg(test)]
pub(in crate::surface) use proof_object::take_terminal_join_materialized_facts;
#[cfg(test)]
pub(in crate::surface) use proof_object::take_terminal_publication_visits;
