use super::diagnostics::*;
use super::validation::collect_click_function_calls;
use super::validation::{collect_called_predicates, collect_resource_count_families, tactic_name};
use super::*;

mod attempt;
mod claim_proofs;
#[cfg(test)]
pub(in crate::surface) use claim_proofs::count_flat_proof_units;
pub(in crate::surface) use fixed_state_proofs::{
    evaluate_fixed_state_expression_through_kernel, lower_fixed_state_proposition_through_kernel,
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
    count_execution_context_exports, count_explicit_linear_fallbacks,
    count_finalization_view_constructions, count_smart_loop_effect_frame_candidates,
    count_source_certificate_checks,
};
mod checked_drivers;
mod execution_state;
mod pure_theorems;
mod resources;
mod smart_closures;
mod smart_execution;
mod structural;
mod surface_certificates;
mod surface_construction;
mod surface_lowering;
mod surface_synthesis;
mod theorem_application;
mod timing;
use crate::kernel::fresh_int32_variable_for_propositions;
#[cfg(test)]
use crate::kernel::proof::quantified_equivalence_index_key;
use crate::kernel::proof::{
    CheckedFrameAuthority, ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind,
    FrontierPosition, LoopEffectGoal, PersistentOrderedSet, PersistentSequence,
    PersistentSequenceIter, ProofExecutionContinuation, ProofFacts, SharedVec, old_reference_state,
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
    verify_loop_execution_proofs,
};
use execution_state::*;
pub(super) use execution_state::{capture_c0_proof_site_expansion, capture_c0_tactic_expansion};
use fact_reasoning::*;
pub(super) use fact_reasoning::{
    condition_polarity_equivalent, exactly_available_fact, search_condition_derivation,
};
use fixed_state_proofs::*;
use language_context::*;
#[cfg(test)]
pub(in crate::surface) use proof_object::collect_execution_context_export_labels;
use proof_object::*;
#[cfg(test)]
use pure_theorems::{
    lower_pure_theorem_proposition, pure_theorem_context, validate_pure_theorem_certificate,
};
pub(super) use pure_theorems::{
    pure_theorem_array_refs, pure_theorem_parameter_values, verify_theorem_definitions,
};
pub(super) use resources::instantiate_composite_resource_body_resources;
use resources::*;
use structural::*;
use surface_certificates::*;
use surface_construction::*;
#[cfg(test)]
use surface_synthesis::{SURFACE_SYNTHESIS_DEPTH_LIMIT, bitvector_term_is_load_free};
use surface_synthesis::{
    surface_synthesis_exhaustion_description, surface_synthesis_failure,
    synthesize_surface_proposition_with_bound_variable_names,
};
pub(super) use surface_synthesis::{
    synthesize_surface_equality_across_points, synthesize_surface_proposition,
};
use theorem_application::*;
use timing::TacticTiming;
pub(super) use timing::{SourceSiteKind, source_site_kind};

/// Checked kernel evidence used as the input to constructing one
/// [`ProofStep`]. Evidence never forms an ordered checkable program of
/// its own: search consumes it transiently to write the surface step, and the
/// resulting operation is checked by `Proof`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) enum ConstructionEvidence {
    CertifiedStatementStep {
        planned_transition: Option<usize>,
    },
    CertifiedLoopSummaryStep {
        prerequisite_derivations: Vec<PropositionDerivation>,
        exact_premises: Vec<Proposition>,
        planned_transition: Option<usize>,
    },
    CertifiedFactTransport {
        source: Proposition,
        target: Proposition,
        theorem: Theorem,
    },
    FinishCertifiedFactTransports(Vec<Proposition>),
    CertifiedPathAssumption {
        occurrence: usize,
        condition: ClickProposition,
        value: bool,
        facts: Vec<Proposition>,
        theorem: Theorem,
    },
}

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

fn apply_logical_goal_tactic(
    tactic: &ProofTactic,
    goal: &mut Proposition,
    available: &mut Vec<Proposition>,
    contradiction_fact: Option<Proposition>,
) -> Result<bool, String> {
    match tactic {
        ProofTactic::Intro => match goal.clone() {
            Proposition::Implies(antecedent, consequent) => {
                if !available.contains(&antecedent) {
                    available.push(*antecedent);
                }
                *goal = *consequent;
                Ok(false)
            }
            Proposition::ForAll { var, body, .. } => {
                let (_, body) = crate::kernel::freshen_int32_forall_body(var, &body, available);
                *goal = body;
                Ok(false)
            }
            Proposition::Not(body) => {
                if !available.contains(&body) {
                    available.push(*body);
                }
                *goal = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
                Ok(false)
            }
            _ => Err(format!(
                "`intro` requires an implication, negation, or universal goal, got {goal:?}"
            )),
        },
        ProofTactic::Split => {
            let Proposition::And(left, right) = goal else {
                return Err(format!("`split` requires a conjunction goal, got {goal:?}"));
            };
            if !available.contains(left.as_ref()) || !available.contains(right.as_ref()) {
                return Err(format!(
                    "`split` requires both conjuncts as exact facts: {left:?} and {right:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Left => {
            let Proposition::Or(left, _) = goal else {
                return Err(format!("`left` requires a disjunction goal, got {goal:?}"));
            };
            if !available
                .iter()
                .any(|fact| condition_polarity_equivalent(fact, left))
            {
                return Err(format!(
                    "`left` requires its selected disjunct as an exact fact: {left:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Right => {
            let Proposition::Or(_, right) = goal else {
                return Err(format!("`right` requires a disjunction goal, got {goal:?}"));
            };
            if !available
                .iter()
                .any(|fact| condition_polarity_equivalent(fact, right))
            {
                return Err(format!(
                    "`right` requires its selected disjunct as an exact fact: {right:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Enumerate => {
            // Close a constant-bounded universal goal from its written
            // instances: the goal's guards fix each binder's constant range
            // (exactly the kernel `FiniteForAll` table), and every in-range
            // instance must either normalize context-free (a vacuous guard)
            // or be an exact available fact. Work is proportional to the
            // instantiation table; nothing is searched.
            let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
                return Err(format!(
                    "`enumerate` requires a universal goal whose guards bound every binder to a constant range, got {goal:?}"
                ));
            };
            for (_, instance) in instances {
                if normalizes_context_free(&instance) {
                    continue;
                }
                if !pure_fact_is_available(&instance, available) {
                    return Err(format!(
                        "`enumerate` requires each in-range instance as an exact available fact; missing {}",
                        describe_pure_fact(&instance, &[], &[]),
                    ));
                }
            }
            Ok(true)
        }
        ProofTactic::Contradiction(_) => {
            let fact = contradiction_fact
                .ok_or_else(|| "`contradiction` is missing its lowered fact".to_string())?;
            let negated = Proposition::Not(Box::new(fact.clone()));
            let opposite_condition = match &fact {
                Proposition::ConditionIs(condition, polarity) => {
                    Some(Proposition::ConditionIs(condition.clone(), !polarity))
                }
                _ => None,
            };
            if !available.contains(&fact)
                || (!available.contains(&negated)
                    && !opposite_condition
                        .as_ref()
                        .is_some_and(|opposite| available.contains(opposite))
                    && !normalizes_context_free(&negated))
            {
                return Err(format!(
                    "`contradiction` requires an exact fact and its exact negation or opposite condition polarity: {fact:?}"
                ));
            }
            Ok(true)
        }
        _ => Err("not a logical goal tactic".to_string()),
    }
}

/// Checks a bitvector equality target by transitive chaining of the listed
/// equality premises, with load terms in canonical form as term identity. The
/// decide engine chains constants and variables; certificates also chain
/// through load terms recorded at intermediate states.
fn pointer_offsets_match_by_term_equivalence(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    terms_equivalent: &impl Fn(&Bitvector32Term, &Bitvector32Term) -> bool,
) -> bool {
    match (left, right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => left == right,
        (PointerOffsetTerm::Variable(left), PointerOffsetTerm::Variable(right)) => left == right,
        (
            PointerOffsetTerm::Int32Scaled {
                value: left,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right,
                byte_width: right_width,
            },
        ) => left_width == right_width && terms_equivalent(left, right),
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            (pointer_offsets_match_by_term_equivalence(left_a, right_a, terms_equivalent)
                && pointer_offsets_match_by_term_equivalence(left_b, right_b, terms_equivalent))
                || (pointer_offsets_match_by_term_equivalence(left_a, right_b, terms_equivalent)
                    && pointer_offsets_match_by_term_equivalence(left_b, right_a, terms_equivalent))
        }
        _ => false,
    }
}

fn pointer_offset_equality_by_frame(target: &Proposition, available: &[Proposition]) -> bool {
    let Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) = target
    else {
        return false;
    };
    let framing_facts = available
        .iter()
        .filter(|fact| {
            !matches!(
                fact,
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), _)
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let assumptions = assumptions_from_propositions(&framing_facts);
    let terms_equivalent = |left: &Bitvector32Term, right: &Bitvector32Term| {
        left == right
            || crate::kernel::explicit_atomic_equality_from_memory_derivations(
                left,
                right,
                &assumptions,
            )
            || matches!((left, right), (
                Bitvector32Term::MemoryLoad(left_memory, left_pointer),
                Bitvector32Term::MemoryLoad(right_memory, right_pointer),
            ) if left_pointer == right_pointer
                && (crate::kernel::c_memory_load_is_unchanged(
                    left_memory,
                    right_memory,
                    left_pointer,
                    &assumptions,
                ) || crate::kernel::c_memory_load_is_unchanged(
                    right_memory,
                    left_memory,
                    left_pointer,
                    &assumptions,
                )))
    };
    pointer_offsets_match_by_term_equivalence(left, right, &terms_equivalent)
}

fn equal_by_premise_chain(
    premises: &[Proposition],
    target: &Proposition,
    available: &[Proposition],
) -> bool {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(target_left, target_right), true) =
        crate::kernel::c_condition_fact_with_canonicalized_loads(target)
    else {
        return false;
    };
    let framing_facts = available
        .iter()
        .filter(|fact| {
            !matches!(
                fact,
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), _)
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let frame_assumptions = assumptions_from_propositions(&framing_facts);
    // Two forms denote the same term when identical, or when they load
    // the same pointer from memories the recorded effect facts prove
    // unchanged between (frame-justified, never by ignoring havoc alone).
    let terms_equivalent = |left: &Bitvector32Term, right: &Bitvector32Term| {
        left == right
            || crate::kernel::explicit_atomic_equality_from_memory_derivations(
                left,
                right,
                &frame_assumptions,
            )
            || matches!((left, right), (
                Bitvector32Term::MemoryLoad(left_memory, left_pointer),
                Bitvector32Term::MemoryLoad(right_memory, right_pointer),
            ) if left_pointer == right_pointer
                && (crate::kernel::c_memory_load_is_unchanged(
                    left_memory,
                    right_memory,
                    left_pointer,
                    &frame_assumptions,
                ) || crate::kernel::c_memory_load_is_unchanged(
                    right_memory,
                    left_memory,
                    left_pointer,
                    &frame_assumptions,
                )))
    };
    let mut classes: Vec<Vec<Bitvector32Term>> = Vec::new();
    {
        let mut add_equality = |left: &Bitvector32Term, right: &Bitvector32Term| {
            let left = left.clone();
            let right = right.clone();
            let left_class = classes.iter().position(|class| class.contains(&left));
            let right_class = classes.iter().position(|class| class.contains(&right));
            match (left_class, right_class) {
                (Some(a), Some(b)) if a != b => {
                    let merged = classes.remove(a.max(b));
                    classes[a.min(b)].extend(merged);
                }
                (Some(_), Some(_)) => {}
                (Some(a), None) => classes[a].push(right),
                (None, Some(b)) => classes[b].push(left),
                (None, None) => classes.push(vec![left, right]),
            }
        };
        // Ambient equality facts are execution-certified (store equations,
        // recorded aliases) and may link the listed premises, the same way
        // frame facts justify load unification. Keep the raw edge as well as its
        // canonical form: canonicalizing a store equation can reduce its written
        // load to the stored value and erase the edge needed to reach a later
        // memory-load term.
        for premise in premises.iter().chain(available) {
            if let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                premise
            {
                add_equality(left, right);
            }
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                crate::kernel::c_condition_fact_with_canonicalized_loads(premise)
            else {
                continue;
            };
            add_equality(&left, &right);
        }
    }
    let target_left = *target_left;
    let target_right = *target_right;
    let terms_linked = |left: &Bitvector32Term, right: &Bitvector32Term| {
        left == right
            || classes
                .iter()
                .any(|class| class.contains(left) && class.contains(right))
    };
    let address_terms_linked = |left: &Bitvector32Term, right: &Bitvector32Term| {
        terms_linked(left, right)
            || classes.iter().any(|class| {
                class.iter().any(|term| terms_equivalent(term, left))
                    && class.iter().any(|term| terms_equivalent(term, right))
            })
            || terms_equivalent(left, right)
    };
    if terms_linked(&target_left, &target_right)
        || terms_equivalent(&target_left, &target_right)
        || classes.iter().any(|class| {
            class
                .iter()
                .any(|term| terms_equivalent(term, &target_left))
                && class
                    .iter()
                    .any(|term| terms_equivalent(term, &target_right))
        })
    {
        return true;
    }
    let Bitvector32Term::MemoryLoad(target_memory, target_pointer) = &target_left else {
        return false;
    };
    premises.iter().chain(available).any(|premise| {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = premise
        else {
            return false;
        };
        let (Bitvector32Term::MemoryLoad(memory, pointer), value) = (left.as_ref(), right.as_ref())
        else {
            return false;
        };
        let same_block = target_pointer.block == pointer.block;
        let same_value = terms_linked(&target_right, value);
        let same_offset = pointer_offsets_match_by_term_equivalence(
            &target_pointer.offset,
            &pointer.offset,
            &address_terms_linked,
        );
        same_block
            && same_value
            && same_offset
            && (crate::kernel::c_memory_load_is_unchanged(
                target_memory,
                memory,
                target_pointer,
                &frame_assumptions,
            ) || crate::kernel::c_memory_load_is_unchanged(
                memory,
                target_memory,
                pointer,
                &frame_assumptions,
            ))
    })
}

/// Language-facing diagnostic adapter for the kernel's instantiated-guard
/// check. Surface certificate planning shares the same checked rule without
/// gaining successor authority.
pub(super) fn discharge_instantiated_guards(
    instantiated: Proposition,
    premises: &[Proposition],
) -> Result<(Vec<Proposition>, Proposition), String> {
    crate::kernel::proof::fact_reasoning::discharge_instantiated_guards(instantiated, premises)
        .map_err(format_forall_int32_instantiation_error)
}

/// Language-facing diagnostic adapter for the kernel's explicit `int32`
/// specialization check. `ProofObject::apply_instantiate` additionally owns
/// fact availability and publishing the checked conclusion.
pub(super) fn check_forall_int32_instantiation(
    quantified: &Proposition,
    argument: Bitvector32Term,
    premises: &[Proposition],
) -> Result<Proposition, String> {
    crate::kernel::proof::fact_reasoning::check_forall_int32_instantiation(
        quantified, argument, premises,
    )
    .map_err(format_forall_int32_instantiation_error)
}

pub(super) fn format_forall_int32_instantiation_error(
    error: crate::kernel::proof::fact_reasoning::ForallInt32InstantiationError,
) -> String {
    use crate::kernel::proof::fact_reasoning::ForallInt32InstantiationError as Error;
    match error {
        Error::RequiresUniversal => {
            "`instantiate` requires a universally quantified fact".to_string()
        }
        Error::UnsupportedSort => "`instantiate` supports only int32 universals".to_string(),
        Error::MissingGuard(missing) => format!(
            "instantiated premise `{}` does not follow from the listed evidence",
            describe_pure_fact(&missing, &[], &[]),
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

pub(super) fn check_atomic_premise_derivation_goal(
    target: &Proposition,
    premises: Vec<Proposition>,
    goal: &Proposition,
    available: &[Proposition],
) -> Result<(), String> {
    let target_matches_goal = target == goal
        || quantified_equivalent_available_fact(goal, std::slice::from_ref(target)).is_some();
    if !target_matches_goal {
        return Err(format!(
            "atomic premise derivation target does not match the current goal\n  target: {}\n  goal: {}",
            describe_pure_fact(target, &[], &[]),
            describe_pure_fact(goal, &[], &[]),
        ));
    }
    // An empty premise derivation is sound only for a context-free goal. Any
    // proof that needs frame or ambient facts must keep at least one explicit
    // premise in the smart tactic's selected evidence.
    if premises.is_empty() && !normalizes_context_free(target) {
        return Err("atomic derivation requires at least one explicit premise".to_string());
    }
    let premise_part_available = |part: &Proposition| {
        available.iter().any(|available| {
            let mut conjuncts = Vec::new();
            atomic_conjuncts(available, &mut conjuncts);
            conjuncts.into_iter().any(|available| {
                *available == *part
                    || condition_polarity_equivalent(available, part)
                    || (matches!(available, Proposition::ForAll { .. })
                        && matches!(part, Proposition::ForAll { .. })
                        && assumptions_from_propositions(&[available.clone()])
                            .derive_simp_proposition(part)
                            .is_some())
            })
        })
    };
    if let Some(missing) = premises.iter().find(|premise| {
        // A conjunction premise is available when each conjunct is; facts
        // are often assumed split even when the certificate lists them
        // joined.
        let mut parts = Vec::new();
        atomic_conjuncts(premise, &mut parts);
        !parts.into_iter().all(premise_part_available)
    }) {
        return Err(format!(
            "atomic derivation is missing an exact listed premise: {}",
            describe_pure_fact(missing, &[], &[]),
        ));
    }
    if matches!(normalize_proposition(target), SimpProposition::True) {
        return Ok(());
    }
    let premise_assumptions = assumptions_from_propositions(&premises);
    let premise_only_derivation = premise_assumptions
        .derive_atomic_proposition(target)
        .or_else(|| premise_assumptions.derive_simp_atomic_proposition(target));
    if premise_only_derivation.is_some() {
        return Ok(());
    }
    // Overflow side-conditions are execution-certified facts with no Surface
    // surface form, so a certificate can never list them; check consumes
    // them from the ambient record, and this check may too. Only that shape
    // widens the premise set — evidence for everything else stays listed.
    let ambient_overflow_facts = available
        .iter()
        .filter(|fact| {
            matches!(
                fact,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedAddOverflows(_, _)
                        | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
                        | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
                        | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
                        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _),
                    false,
                )
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    if !ambient_overflow_facts.is_empty() {
        let mut widened = premises.clone();
        widened.extend(ambient_overflow_facts);
        let widened_assumptions = assumptions_from_propositions(&widened);
        if widened_assumptions
            .derive_atomic_proposition(target)
            .or_else(|| widened_assumptions.derive_simp_atomic_proposition(target))
            .is_some()
        {
            return Ok(());
        }
    }
    let explicit_assumptions = assumptions_from_propositions(available);
    let explicit_terms_equal = |left: &Bitvector32Term, right: &Bitvector32Term| {
        left == right
            || crate::kernel::explicit_atomic_equality_from_memory_derivations(
                left,
                right,
                &explicit_assumptions,
            )
    };
    let explicit_dag_equality = matches!(
        target,
        Proposition::ConditionIs(condition, true)
            if match condition {
                ConditionTerm::Bitvector32Equal(left, right) => {
                    explicit_terms_equal(left, right)
                }
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    pointer_offsets_match_by_term_equivalence(
                        left,
                        right,
                        &explicit_terms_equal,
                    )
                }
                ConditionTerm::PointerEqual(left, right) => {
                    left.block == right.block
                        && pointer_offsets_match_by_term_equivalence(
                            &left.offset,
                            &right.offset,
                            &explicit_terms_equal,
                        )
                }
                _ => false,
            }
    );
    if explicit_dag_equality
        || pointer_offset_equality_by_frame(target, available)
        || equal_by_premise_chain(&premises, target, available)
    {
        return Ok(());
    }
    // Effect summaries and certified-write records are deterministic
    // execution artifacts with no surface form; certificate generation
    // deliberately omits them from the premise list (mirroring its
    // loadability carve-out), so the check environment supplies them.
    // Only these two shapes ride along: everything else the derivation
    // consumes must be a listed premise.
    let effect_context = available
        .iter()
        .filter(|fact| {
            matches!(
                fact,
                Proposition::CMemoryMutatesOnly { .. }
                    | Proposition::CMemoryEffectSummary { .. }
                    | Proposition::CHeapAllocationFreed { .. }
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let with_effect_context = |facts: &[Proposition]| {
        let mut combined = facts.to_vec();
        combined.extend(effect_context.iter().cloned());
        combined
    };
    let derive_from = |facts: &[Proposition], target: &Proposition| {
        let assumptions = assumptions_from_propositions(facts);
        assumptions
            .derive_atomic_proposition(target)
            .or_else(|| assumptions.derive_proposition(target))
            .or_else(|| assumptions.derive_simp_atomic_proposition(target))
            .or_else(|| assumptions.derive_simp_proposition(target))
    };
    let derivation = derive_from(&premises, target)
        .or_else(|| derive_from(&with_effect_context(&premises), target));
    // Premises recorded at different program points can write the same load
    // through different snapshots; retry with loads in canonical form so the chain
    // unifies.
    let derivation = derivation.or_else(|| {
        let canonical_premises = premises
            .iter()
            .map(crate::kernel::c_condition_fact_with_canonicalized_loads)
            .collect::<Vec<_>>();
        let canonical_target = crate::kernel::c_condition_fact_with_canonicalized_loads(target);
        if canonical_premises == premises && &canonical_target == target {
            return None;
        }
        derive_from(&canonical_premises, &canonical_target)
            .or_else(|| derive_from(&with_effect_context(&canonical_premises), &canonical_target))
    });
    if crate::instrumentation::deadline_exceeded() {
        return Err(format!(
            "tactic budget exhausted: {}",
            crate::instrumentation::deadline_context()
        ));
    }
    if derivation.is_none()
        && (pointer_offset_equality_by_frame(target, available)
            || equal_by_premise_chain(&premises, target, available))
    {
        return Ok(());
    }
    if derivation.is_none() {
        return Err(format!(
            "atomic derivation could not check the target from exactly the listed premises: {}\n  premises: {}",
            describe_pure_fact(target, &[], &[]),
            describe_pure_facts(&premises),
        ));
    }
    Ok(())
}

/// Plan `simp() using` against only the propositions named by the user.
///
/// Availability is checked against the ambient proof state, but ambient facts
/// are deliberately not included in the simplifier context. The returned
/// derivation is a smart-tactic plan; expansion must lower it to simple rules
/// before it can become a certificate.
pub(super) fn plan_restricted_simp_goal(
    target: &Proposition,
    premises: Vec<Proposition>,
    goal: &Proposition,
    available: &[Proposition],
) -> Result<PropositionDerivation, String> {
    if target != goal
        && quantified_equivalent_available_fact(goal, std::slice::from_ref(target)).is_none()
    {
        return Err(format!(
            "`simp` target does not match the current goal\n  target: {}\n  goal: {}",
            describe_pure_fact(target, &[], &[]),
            describe_pure_fact(goal, &[], &[]),
        ));
    }
    let premise_part_available = |part: &Proposition| {
        available.iter().any(|available| {
            let mut conjuncts = Vec::new();
            atomic_conjuncts(available, &mut conjuncts);
            conjuncts.into_iter().any(|available| {
                *available == *part || condition_polarity_equivalent(available, part)
            })
        })
    };
    if let Some(missing) = premises.iter().find(|premise| {
        let mut parts = Vec::new();
        atomic_conjuncts(premise, &mut parts);
        !parts.into_iter().all(premise_part_available)
    }) {
        return Err(format!(
            "`simp` is missing an exact listed premise: {}",
            describe_pure_fact(missing, &[], &[]),
        ));
    }
    let assumptions = assumptions_from_propositions(&premises);
    let Some(derivation) = assumptions.derive_simp_proposition(target) else {
        return Err(format!(
            "`simp() using` could not prove the current goal from only its listed premises\n  goal: {}",
            describe_pure_fact(target, &[], &[]),
        ));
    };
    derivation
        .check(&assumptions)
        .then_some(derivation)
        .ok_or_else(|| "`simp() using` planned a derivation that failed validation".to_string())
}

pub(in crate::surface) fn normalizes_context_free(goal: &Proposition) -> bool {
    crate::kernel::proof::fact_reasoning::normalizes_context_free(goal)
}

fn pure_goal_proof_certificate_gateway<T>(
    claim_label: &str,
    planner: impl FnOnce() -> Result<ProofCertificate, ClickError>,
    check: impl FnOnce(&ProofCertificate) -> Result<T, ClickError>,
) -> Result<(ProofCertificate, T), ClickError> {
    pure_goal_proof_certificate_gateway_with_checked_result(
        claim_label,
        || planner().map(|certificate| (certificate, None)),
        check,
    )
}

fn pure_goal_proof_certificate_gateway_with_checked_result<T>(
    claim_label: &str,
    planner: impl FnOnce() -> Result<(ProofCertificate, Option<T>), ClickError>,
    check: impl FnOnce(&ProofCertificate) -> Result<T, ClickError>,
) -> Result<(ProofCertificate, T), ClickError> {
    let function = claim_label
        .split_once('.')
        .map_or(claim_label, |(function, _)| function);
    let (certificate, checked_result) = crate::instrumentation::measure_operation(
        function,
        claim_label,
        "surface certificate construction",
        planner,
    )?;
    let checked_result = match checked_result {
        Some(checked_result) => checked_result,
        None => crate::instrumentation::measure_operation(
            function,
            claim_label,
            "generated certificate validation",
            || check(&certificate),
        )
        .map_err(|error| {
            ClickError::new(format!(
                "pure goal `{claim_label}` certificate failed round-trip validation:\n{}\n{}",
                format_proof_certificate(&certificate),
                error.message()
            ))
        })?,
    };
    Ok((certificate, checked_result))
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

        assert!(synthesize_surface_proposition(&proposition, &[], &[], &CState::new()).is_none());
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
                )),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let state = CState::new().with_memory(CMemory::new().with_block("current", 4));

        let error = checked_surface_comparison_fact_in_state(
            ExecutionView::new(
                &ExecutionFrontier::default(),
                &[],
                &RecordedSnapshots::new(),
                &SurfacePropositionMap::default(),
                None,
            ),
            &kernel,
            SurfaceFactMatch::CanonicalExact,
            &[],
            &[],
            &[],
            &state,
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
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
    fn pure_fact_check_availability_ignores_quantifier_binder_ids() {
        let quantified_equality = |variable| Proposition::ForAll {
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Variable(variable)),
                ),
                true,
            )),
        };
        let available = quantified_equality(Variable(2_000_000));
        let checked = quantified_equality(Variable(3_000_000));

        assert!(pure_fact_is_available(&checked, &[available]));
    }

    #[test]
    fn pure_certificate_check_is_transactional() {
        let file = parse(
            r#"
                theorem reflexive(x: int32) {
                    ensures x == x by auto;
                }
            "#,
        )
        .expect("theorem should parse");
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem = &file.theorem_definitions()[0];
        let context =
            pure_theorem_context(theorem, &predicate_environment, &click_function_environment)
                .expect("theorem context should lower");
        let Ensure::Proposition(surface_goal) = theorem.ensures()[0].ensure() else {
            panic!("expected proposition goal");
        };
        let goal = lower_pure_theorem_proposition(
            theorem.name(),
            surface_goal,
            &context.values,
            &context.array_refs,
            &context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("goal should lower");
        let failing = ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple tactic");
        let succeeding = ProofCertificate::from_proof_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a simple tactic");

        let failed = pure_goal_proof_certificate_gateway(
            "reflexive.ensures_0",
            || Ok(failing.clone()),
            |certificate| {
                validate_pure_theorem_certificate(
                    "reflexive.ensures_0",
                    &context.requires,
                    &goal,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                    &context,
                    certificate,
                    None,
                )
            },
        );
        let error =
            failed.expect_err("a perturbed smart certificate must not be reported as success");
        assert!(
            error
                .message()
                .contains("certificate failed round-trip validation"),
            "unexpected gateway error: {}",
            error.message()
        );
        let succeeded = validate_pure_theorem_certificate(
            "reflexive.ensures_0",
            &context.requires,
            &goal,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &context,
            &succeeding,
            None,
        );
        succeeded.expect("failed validation must not mutate the shared proof inputs");
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
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());

        let (verified, events) = crate::instrumentation::collect(|| {
            verify_theorem_definitions(
                file.theorem_definitions(),
                &predicate_environment,
                &click_function_environment,
            )
        });
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
            Some([
                ProofTactic::ApplyTheoremUsing { application, premises },
                ProofTactic::Split,
            ]) if application.name == "required" && premises.len() == 1
        ));
        assert_eq!(
            verified[4].proof_tactics().as_deref(),
            Some([ProofTactic::Intro, ProofTactic::Assumption].as_slice())
        );
        assert_eq!(
            verified[5].proof_tactics().as_deref(),
            Some([ProofTactic::Split].as_slice())
        );
        assert_eq!(
            verified[6].proof_tactics().as_deref(),
            Some([ProofTactic::Left].as_slice())
        );
        assert!(matches!(
            verified[7].proof_tactics().as_deref(),
            Some([ProofTactic::Contradiction(_)])
        ));
        assert!(
            events.iter().all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                    if matches!(
                        claim.as_str(),
                        "required.ensures_0"
                            | "reflexive.ensures_0"
                            | "applied.ensures_0"
                            | "applied_then_simp.ensures_0"
                            | "implication.ensures_0"
                            | "conjunction.ensures_0"
                            | "disjunction.ensures_0"
                            | "impossible.ensures_0"
                    )
                        && name == "generated certificate validation"
            )),
            "checked smart pure proofs must not pass through ordinary certificate validation: {events:#?}"
        );
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
                    }],
                    certificate: assumption,
                },
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: condition.clone(),
                        value: false,
                    }],
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
                    }],
                    certificate: assumption,
                },
                PathCertificate {
                    case_path: vec![ProofCaseChoice {
                        condition: other,
                        value: false,
                    }],
                    certificate: normalize,
                },
            ],
        )
        .expect_err("unrelated branch conditions must not be flattened together");

        assert!(error.message().contains("incompatible next branch"));
    }
}

struct ExpandedProofCase {
    tactics: Vec<ProofTactic>,
    assumptions: Vec<ProofCaseAssumption>,
}

struct ProofCaseAssumption {
    tactic_index: usize,
    kind: ProofCaseAssumptionKind,
}

#[derive(Clone)]
enum ProofCaseAssumptionKind {
    /// Excluded-middle case split from proof-level `if`: assume the written
    /// condition with the given polarity. Sound without an availability check.
    Condition {
        proposition: ClickProposition,
        value: bool,
    },
    /// Disjunction elimination from `cases`: proof checking requires the written
    /// disjunction is an available fact at the split point, then assumes
    /// exactly the selected disjunct.
    Disjunct {
        disjunction: ClickProposition,
        left: bool,
    },
}

// Pure proofs and fixed-state `have` proofs use flat logical cases. Execution
// proofs use `InternalProofNode` for frontier-local control structure.
fn expand_proof_if_cases(tactics: &[ProofTactic]) -> Result<Vec<ExpandedProofCase>, ClickError> {
    expand_structured_proof_cases(tactics)
}

fn expand_structured_proof_cases(
    tactics: &[ProofTactic],
) -> Result<Vec<ExpandedProofCase>, ClickError> {
    let Some((control_index, control_tactic)) = tactics
        .iter()
        .enumerate()
        .find(|(_, tactic)| matches!(tactic, ProofTactic::If(_) | ProofTactic::Cases(_)))
    else {
        return Ok(vec![ExpandedProofCase {
            tactics: tactics.to_vec(),
            assumptions: Vec::new(),
        }]);
    };
    let prefix = &tactics[..control_index];
    let branches: [(ProofCaseAssumptionKind, &[ProofTactic]); 2] = match control_tactic {
        ProofTactic::If(proof_if) => [
            (
                ProofCaseAssumptionKind::Condition {
                    proposition: proof_if.condition.clone(),
                    value: true,
                },
                proof_if.then_tactics.as_slice(),
            ),
            (
                ProofCaseAssumptionKind::Condition {
                    proposition: proof_if.condition.clone(),
                    value: false,
                },
                proof_if.else_tactics.as_slice(),
            ),
        ],
        ProofTactic::Cases(proof_cases) => [
            (
                ProofCaseAssumptionKind::Disjunct {
                    disjunction: proof_cases.disjunction.clone(),
                    left: true,
                },
                proof_cases.left_tactics.as_slice(),
            ),
            (
                ProofCaseAssumptionKind::Disjunct {
                    disjunction: proof_cases.disjunction.clone(),
                    left: false,
                },
                proof_cases.right_tactics.as_slice(),
            ),
        ],
        _ => unreachable!("control-tactic search only returns proof if or cases"),
    };
    let suffix_cases = expand_structured_proof_cases(&tactics[control_index + 1..])?;
    let mut cases = Vec::new();
    for (kind, branch_tactics) in branches {
        for branch in expand_structured_proof_cases(branch_tactics)? {
            for suffix in &suffix_cases {
                let boundary = prefix.len() + branch.tactics.len();
                let mut linear = prefix.to_vec();
                linear.extend(branch.tactics.iter().cloned());
                linear.extend(suffix.tactics.iter().cloned());
                let mut assumptions = vec![ProofCaseAssumption {
                    tactic_index: prefix.len(),
                    kind: kind.clone(),
                }];
                assumptions.extend(branch.assumptions.iter().map(|assumption| {
                    ProofCaseAssumption {
                        tactic_index: prefix.len() + assumption.tactic_index,
                        kind: assumption.kind.clone(),
                    }
                }));
                assumptions.extend(suffix.assumptions.iter().map(|assumption| {
                    ProofCaseAssumption {
                        tactic_index: boundary + assumption.tactic_index,
                        kind: assumption.kind.clone(),
                    }
                }));
                cases.push(ExpandedProofCase {
                    tactics: linear,
                    assumptions,
                });
            }
        }
    }
    Ok(cases)
}

#[derive(Clone)]
struct IndexedTactic {
    index: usize,
    source_index: usize,
    tactic: ProofTactic,
}

enum InternalProofNode {
    Done,
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
            ProofTactic::If(_) | ProofTactic::Branch(_) | ProofTactic::Open(_)
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
        ProofTactic::If(proof_if) => {
            let then_width = source_tactic_count(&proof_if.then_tactics);
            InternalProofNode::If {
                index,
                source_index,
                condition: proof_if.condition.clone(),
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

pub(super) fn source_tactic_count(tactics: &[ProofTactic]) -> usize {
    tactics.iter().map(source_tactic_width).sum()
}

fn source_tactic_width(tactic: &ProofTactic) -> usize {
    match tactic {
        ProofTactic::If(proof_if) => {
            1 + source_tactic_count(&proof_if.then_tactics)
                + source_tactic_count(&proof_if.else_tactics)
        }
        ProofTactic::Cases(proof_cases) => {
            1 + source_tactic_count(&proof_cases.left_tactics)
                + source_tactic_count(&proof_cases.right_tactics)
        }
        ProofTactic::Branch(proof_branch) => {
            1 + source_tactic_count(&proof_branch.then_tactics)
                + source_tactic_count(&proof_branch.else_tactics)
        }
        ProofTactic::Open(proof_open) => 1 + source_tactic_count(&proof_open.tactics),
        ProofTactic::Loop(clause) => {
            1 + clause
                .initialize_proof()
                .map_or(0, proof_source_tactic_count)
                + clause.preserve_proof().map_or(0, proof_source_tactic_count)
                + clause
                    .items()
                    .iter()
                    .filter(|item| item.is_effect_kind())
                    .map(|item| proof_source_tactic_count(item.proof()))
                    .sum::<usize>()
        }
        _ => 1,
    }
}

fn internal_proof_contains_source_index(node: &InternalProofNode, wanted: usize) -> bool {
    match node {
        InternalProofNode::Done => false,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            tactics.iter().any(|tactic| tactic.source_index == wanted)
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
    Effect(usize, &'a EffectClause),
    Ensure(usize, &'a EnsureClause),
}

impl<'a> FunctionClaimRef<'a> {
    pub(super) fn proof(self) -> &'a SourceProof {
        match self {
            Self::Effect(_, clause) => clause.proof(),
            Self::Ensure(_, clause) => clause.proof(),
        }
    }

    fn verified_claim(self) -> VerifiedClaim {
        match self {
            Self::Effect(index, clause) => VerifiedClaim::Effect {
                index,
                clause: clause.clone(),
            },
            Self::Ensure(index, clause) => VerifiedClaim::Ensure {
                index,
                clause: clause.clone(),
            },
        }
    }
}

pub(super) fn function_claims(function_block: &FunctionBlock) -> Vec<FunctionClaimRef<'_>> {
    function_block
        .effects()
        .iter()
        .enumerate()
        .map(|(index, clause)| FunctionClaimRef::Effect(index, clause))
        .chain(
            function_block
                .ensures()
                .iter()
                .enumerate()
                .map(|(index, clause)| FunctionClaimRef::Ensure(index, clause)),
        )
        .collect()
}

pub(super) fn initial_claim_context(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    resource_environment: &ResourceEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<
    (
        CState,
        Vec<CExpression>,
        Vec<Proposition>,
        SurfacePropositionMap,
    ),
    ClickError,
> {
    let (mut state, arguments) =
        initial_call_state(function_block.requires(), parsed_function.parameters())?;
    let mut observed_population_families = BTreeSet::new();
    let mut pending_predicates = BTreeSet::new();
    for requirement in function_block.requires() {
        if let Some(proposition) = requirement.proposition() {
            collect_resource_count_families(proposition, &mut observed_population_families);
            collect_called_predicates(proposition, &mut pending_predicates);
        }
    }
    for ensure in function_block.ensures() {
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
        let Some(definition) = predicate_environment.get(&name) else {
            continue;
        };
        collect_resource_count_families(definition.body(), &mut observed_population_families);
        collect_called_predicates(definition.body(), &mut pending_predicates);
    }
    for family in &observed_population_families {
        state = state.with_observed_population_family(family.clone());
    }
    let (population_state, population_facts) = materialize_counted_population_bodies(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        &observed_population_families,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    state = population_state;
    state = materialize_folded_composite_resource_cells(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        claim_label,
    )?;
    let include_owned_composite_cores = function_block
        .structural_clauses()
        .iter()
        .any(|clause| matches!(clause.region(), CodeRegion::Loop(_)))
        || function_block
            .grouped_proof()
            .is_some_and(proof_contains_frontier_loop);
    let mut projection_state = state.clone();
    for iteration in 0..=function_block.requires().len() {
        if iteration > 0
            && requirement_propositions(
                function_block.requires(),
                parsed_function.parameters(),
                &arguments,
                &projection_state,
                predicate_environment,
                click_function_environment,
            )
            .is_ok()
        {
            break;
        }
        let available_pure_facts = available_initial_requirement_propositions(
            function_block.requires(),
            parsed_function.parameters(),
            &arguments,
            &projection_state,
            predicate_environment,
            click_function_environment,
        );
        let projected = project_initial_composite_resource_cores(
            resource_environment,
            parsed_function.parameters(),
            &arguments,
            projection_state.clone(),
            &available_pure_facts,
            claim_label,
            true,
            predicate_environment,
            click_function_environment,
        )?;
        if projected == projection_state {
            break;
        }
        projection_state = projected;
    }
    state = state.with_memory(projection_state.memory().clone());
    let mut requirement_pure_facts = requirement_propositions(
        function_block.requires(),
        parsed_function.parameters(),
        &arguments,
        &state,
        predicate_environment,
        click_function_environment,
    )?;
    requirement_pure_facts.extend(population_facts);
    // The lowerings of requirements that mention `defined(...)` at this
    // folded state; they are replaced at the definedness state below.
    let folded_defined_facts = function_block
        .requires()
        .iter()
        .filter(|requirement| {
            matches!(
                requirement.inner(),
                Requirement::Proposition(surface) if click_proposition_mentions_defined(surface)
            )
        })
        .map(|requirement| {
            requirement_propositions_with_assumptions(
                std::slice::from_ref(requirement),
                parsed_function.parameters(),
                &arguments,
                &state,
                predicate_environment,
                click_function_environment,
                &assumptions_from_propositions(&requirement_pure_facts),
            )
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let mut surface_propositions = SurfacePropositionMap::default();
    for requirement in function_block.requires() {
        let surface = match requirement.inner() {
            Requirement::Proposition(proposition) => Some(proposition.clone()),
            Requirement::LoadableSegment { segment } => Some(ClickProposition::Loadable {
                segment: segment.clone(),
            }),
            Requirement::Resource(_) | Requirement::Labeled { .. } => None,
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
            parsed_function.parameters(),
            &arguments,
            &state,
            predicate_environment,
            click_function_environment,
            &assumptions_from_propositions(&requirement_pure_facts),
        )?;
        if let [kernel] = lowered.as_slice() {
            surface_propositions.record_lowering(&surface, kernel)?;
        }
    }
    requirement_pure_facts = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_pure_facts,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    state = project_initial_composite_resource_cores(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        &requirement_pure_facts,
        claim_label,
        include_owned_composite_cores,
        predicate_environment,
        click_function_environment,
    )?;
    requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        &state,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    let definedness_state = project_initial_composite_resource_cores(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state.clone(),
        &requirement_pure_facts,
        claim_label,
        true,
        predicate_environment,
        click_function_environment,
    )?;
    // An explicit `defined(...)` requirement evaluates C loads, which need
    // the composite cores projected for that purpose. Lowered at the folded
    // entry state it reads no cell and collapses to `false`, which would make
    // the whole proof context vacuous. Re-lower those requirements at the
    // definedness state and replace their entry facts.
    requirement_pure_facts.retain(|fact| !folded_defined_facts.contains(fact));
    for requirement in function_block.requires() {
        let Requirement::Proposition(surface) = requirement.inner() else {
            continue;
        };
        if !click_proposition_mentions_defined(surface) {
            continue;
        }
        let projected = requirement_propositions_with_assumptions(
            std::slice::from_ref(requirement),
            parsed_function.parameters(),
            &arguments,
            &definedness_state,
            predicate_environment,
            click_function_environment,
            &assumptions_from_propositions(&requirement_pure_facts),
        )?;
        let [projected] = projected.as_slice() else {
            continue;
        };
        if !requirement_pure_facts.contains(projected) {
            requirement_pure_facts.push(projected.clone());
        }
        surface_propositions.record_lowering(surface, projected)?;
    }
    let definedness = requirement_definedness_propositions(
        function_block.requires(),
        parsed_function.parameters(),
        &arguments,
        &definedness_state,
        predicate_environment,
        click_function_environment,
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
        }
    }
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement.inner() else {
            continue;
        };
        record_initial_composite_surface_facts(
            resource_environment,
            resource,
            parsed_function.parameters(),
            &arguments,
            &state,
            &requirement_pure_facts,
            &mut surface_propositions,
            predicate_environment,
            click_function_environment,
            &mut BTreeSet::new(),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed while recording resource facts: {message}"
            ))
        })?;
    }
    Ok((
        state,
        arguments,
        requirement_pure_facts,
        surface_propositions,
    ))
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
        | ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::PredicateCall { .. } => false,
    }
}

pub(super) fn proof_contains_frontier_loop(proof: &SourceProof) -> bool {
    proof
        .tactics()
        .is_some_and(|tactics| tactics.iter().any(tactic_contains_frontier_loop))
}

fn tactic_contains_frontier_loop(tactic: &ProofTactic) -> bool {
    match tactic {
        ProofTactic::Loop(_) => true,
        ProofTactic::Have(have) => proof_contains_frontier_loop(&have.proof),
        ProofTactic::If(proof_if) => proof_if
            .then_tactics
            .iter()
            .chain(&proof_if.else_tactics)
            .any(tactic_contains_frontier_loop),
        ProofTactic::Branch(proof_branch) => proof_branch
            .then_tactics
            .iter()
            .chain(&proof_branch.else_tactics)
            .any(tactic_contains_frontier_loop),
        _ => false,
    }
}

fn available_initial_requirement_propositions(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Vec<Proposition> {
    let mut propositions = Vec::new();
    for requirement in requires {
        let Ok(lowered) = requirement_propositions(
            std::slice::from_ref(requirement),
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
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
    pure_facts: &[Proposition],
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

pub(super) fn prove_claim_by_auto(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut loop_verification_error = None;
    for tactics in auto_loop_verification_tactic_candidates(function_block, claim) {
        match prove_claim_by_tactics(
            expansion_capture.as_deref_mut(),
            source_path,
            function_block,
            parsed_function,
            claim,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            &tactics,
            ProofTacticSource::GeneratedBy { source_index: 0 },
        ) {
            Ok(mut theorems) => {
                for theorem in &mut theorems.theorems {
                    theorem.proof_kind = ProofKind::LoopVerification;
                }
                return Ok(theorems.theorems);
            }
            Err(error) => loop_verification_error = Some(error),
        }
    }

    let mut bounded_error = None;
    for tactics in bounded_execution_tactic_candidates(claim) {
        match prove_claim_by_tactics(
            expansion_capture.as_deref_mut(),
            source_path,
            function_block,
            parsed_function,
            claim,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            &tactics,
            ProofTacticSource::GeneratedBy { source_index: 0 },
        ) {
            Ok(theorems) => return Ok(theorems.theorems),
            Err(error) => bounded_error = Some(error),
        }
    }
    Err(loop_verification_error
        .or(bounded_error)
        .unwrap_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}`: `auto` had no proof candidate to try"
            ))
        }))
}

pub(super) fn prove_claim_by_frame(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if matches!(claim, FunctionClaimRef::Ensure(_, _)) {
        return Err(ClickError::new(format!(
            "`frame` only proves effect clauses for `{claim_label}`; use `by auto;` or `by simp;` for postconditions"
        )));
    }

    let tactics = [ProofTactic::SmartFrame(None)];
    let mut theorems = prove_claim_by_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    for theorem in &mut theorems.theorems {
        theorem.proof_kind = ProofKind::Frame;
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
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if matches!(claim, FunctionClaimRef::Effect(_, _)) {
        return Err(ClickError::new(format!(
            "`simp` does not prove effect clauses for `{claim_label}`; use `by frame;` or `by auto;`"
        )));
    }
    if count_loops(parsed_function.body()) != 0 {
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
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
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
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
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
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        tactics,
        ProofTacticSource::SourceSyntax,
    )?;
    Ok(theorems.theorems)
}
