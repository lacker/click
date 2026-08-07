use super::diagnostics::*;
use super::validation::tactic_name;
use super::*;

mod claim_proofs;
mod execution_planning;
mod fact_reasoning;
mod point_proofs;
mod pure_theorems;
mod replay_engine;
mod replay_state;
mod resources;
mod structural;
mod surface_certificates;
mod surface_replay;
mod surface_synthesis;
mod theorem_application;
mod timing;
use crate::kernel::fresh_int32_variable_for_propositions;
use claim_proofs::finish_ordered_proof_replay;
pub(super) use claim_proofs::{
    prove_claim_by_tactics, prove_claims_by_grouped_auto, prove_claims_by_grouped_tactics,
};
use execution_planning::*;
pub(super) use execution_planning::{
    StatementFactTransportPolicy, StatementPrerequisitePolicy, certified_statement_transitions,
    verify_loop_execution_proofs,
};
use fact_reasoning::*;
pub(super) use fact_reasoning::{condition_polarity_equivalent, search_condition_derivation};
use point_proofs::*;
#[cfg(test)]
use pure_theorems::{
    lower_pure_theorem_proposition, pure_theorem_context, replay_pure_theorem_certificate,
};
pub(super) use pure_theorems::{
    pure_theorem_array_refs, pure_theorem_parameter_values, verify_theorem_definitions,
};
use replay_engine::*;
use replay_state::*;
pub(super) use replay_state::{
    active_c0_tactic_expansion_request, capture_c0_proof_site_expansion,
    capture_c0_tactic_expansion,
};
pub(super) use resources::instantiate_composite_resource_body_resources;
use resources::*;
use structural::*;
use surface_certificates::*;
use surface_replay::*;
pub(super) use surface_synthesis::synthesize_surface_proposition;
#[cfg(test)]
use surface_synthesis::{SURFACE_SYNTHESIS_DEPTH_LIMIT, bitvector_term_is_load_free};
use surface_synthesis::{surface_synthesis_exhaustion_description, surface_synthesis_failure};
use theorem_application::*;
pub(super) use timing::{SourceTacticClass, source_tactic_class};
use timing::{TacticTiming, has_independent_source_timing};

type NextTopLevelStatement = (CState, CState, CStatement, Option<CStatement>);

fn check_verification_deadline() -> Result<(), ClickError> {
    if crate::instrumentation::deadline_exceeded() {
        Err(ClickError::new(format!(
            "verification time limit exceeded inside {}",
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
            Proposition::ForAll { body, .. } => {
                *goal = *body;
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
            if !available.contains(left.as_ref()) {
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
            if !available.contains(right.as_ref()) {
                return Err(format!(
                    "`right` requires its selected disjunct as an exact fact: {right:?}"
                ));
            }
            Ok(true)
        }
        ProofTactic::Contradiction(_) => {
            let fact = contradiction_fact
                .ok_or_else(|| "`contradiction` is missing its lowered fact".to_string())?;
            let negated = Proposition::Not(Box::new(fact.clone()));
            if !available.contains(&fact) || !available.contains(&negated) {
                return Err(format!(
                    "`contradiction` requires both exact facts: {fact:?} and {negated:?}"
                ));
            }
            Ok(true)
        }
        _ => Err("not a logical goal tactic".to_string()),
    }
}

/// Checks a bitvector equality target by transitive chaining of the listed
/// equality premises, with canonical load spellings as term identity. The
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
        crate::kernel::c_condition_fact_with_canonical_loads(target)
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
    // Two spellings denote the same term when identical, or when they load
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
        // snapshot spelling.
        for premise in premises.iter().chain(available) {
            if let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                premise
            {
                add_equality(left, right);
            }
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                crate::kernel::c_condition_fact_with_canonical_loads(premise)
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

pub(super) fn check_atomic_derivation_goal(
    tactic: &ProofTactic,
    target: &Proposition,
    premises: Vec<Proposition>,
    goal: &Proposition,
    available: &[Proposition],
) -> Result<(), String> {
    let target_matches_goal = target == goal
        || quantified_replay_equivalent_available_fact(goal, std::slice::from_ref(target))
            .is_some();
    if !target_matches_goal {
        return Err(format!(
            "`{}` target does not match the current goal\n  target: {}\n  goal: {}",
            tactic_name(tactic),
            describe_pure_fact(target, &[], &[]),
            describe_pure_fact(goal, &[], &[]),
        ));
    }
    // Surface Click deliberately has no contextual `derive using {}`: an
    // empty derivation is printed as `normalize()`, so it is sound only for a
    // context-free goal. Any proof that needs frame or ambient facts must keep
    // at least one explicit premise in its certificate.
    if matches!(tactic, ProofTactic::Derive(_))
        && premises.is_empty()
        && !normalizes_context_free(target)
    {
        return Err("`derive` requires at least one explicit premise".to_string());
    }
    if snapshot_bridged_fact_is_available(target, available, &[]) {
        return Ok(());
    }
    let premise_part_available = |part: &Proposition| {
        let normalized = normalize_direct_atomic_memory_loads(part);
        available.iter().any(|available| {
            let mut conjuncts = Vec::new();
            atomic_conjuncts(available, &mut conjuncts);
            conjuncts.into_iter().any(|available| {
                let available = normalize_direct_atomic_memory_loads(available);
                available == normalized
                    || condition_polarity_equivalent(&available, &normalized)
                    || (matches!(available, Proposition::ForAll { .. })
                        && matches!(normalized, Proposition::ForAll { .. })
                        && assumptions_from_propositions(&[available])
                            .derive_simp_proposition(&normalized)
                            .is_some())
            })
        }) || snapshot_bridged_fact_is_available(&normalized, available, &[])
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
            "`{}` is missing an exact listed premise: {}",
            tactic_name(tactic),
            describe_pure_fact(missing, &[], &[]),
        ));
    }
    let normalized_premises = premises
        .iter()
        .map(normalize_direct_atomic_memory_loads)
        .collect::<Vec<_>>();
    let normalized_target = normalize_direct_atomic_memory_loads(target);
    if matches!(
        normalize_proposition(&normalized_target),
        SimpProposition::True
    ) {
        return Ok(());
    }
    let premise_assumptions = assumptions_from_propositions(&premises);
    let premise_only_derivation = match tactic {
        ProofTactic::Derive(_) => premise_assumptions
            .derive_atomic_proposition(target)
            .or_else(|| premise_assumptions.derive_simp_atomic_proposition(target)),
        _ => None,
    };
    if premise_only_derivation.is_some() {
        return Ok(());
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
    // execution artifacts with no surface spelling; certificate generation
    // deliberately omits them from the premise list (mirroring its
    // loadability carve-out), so the replay environment supplies them.
    // Only these two shapes ride along: everything else the derivation
    // consumes must be a listed premise.
    let effect_context = available
        .iter()
        .filter(|fact| {
            matches!(
                fact,
                Proposition::CMemoryMutatesOnly { .. }
                    | Proposition::CMemoryEffectSummary { .. }
                    | Proposition::CHeapLifetimeRetired { .. }
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
        match tactic {
            ProofTactic::Derive(_) => assumptions
                .derive_atomic_proposition(target)
                .or_else(|| assumptions.derive_proposition(target))
                .or_else(|| assumptions.derive_simp_atomic_proposition(target))
                .or_else(|| assumptions.derive_simp_proposition(target)),
            _ => None,
        }
    };
    // Try the premises as spelled before normalizing: snapshot-bridging
    // derivations can depend on the recorded load spellings that
    // normalization rewrites.
    if !matches!(tactic, ProofTactic::Derive(_)) {
        return Err("not a derivation tactic".to_string());
    }
    let derivation = derive_from(&premises, target)
        .or_else(|| derive_from(&with_effect_context(&premises), target))
        .or_else(|| derive_from(&normalized_premises, &normalized_target))
        .or_else(|| {
            derive_from(
                &with_effect_context(&normalized_premises),
                &normalized_target,
            )
        });
    // Premises recorded at different program points can spell the same load
    // through different snapshots; retry with canonical loads so the chain
    // unifies.
    let derivation = derivation.or_else(|| {
        let canonical_premises = normalized_premises
            .iter()
            .map(crate::kernel::c_condition_fact_with_canonical_loads)
            .collect::<Vec<_>>();
        let canonical_target =
            crate::kernel::c_condition_fact_with_canonical_loads(&normalized_target);
        if canonical_premises == normalized_premises && canonical_target == normalized_target {
            return None;
        }
        derive_from(&canonical_premises, &canonical_target)
            .or_else(|| derive_from(&with_effect_context(&canonical_premises), &canonical_target))
    });
    if crate::instrumentation::deadline_exceeded() {
        return Err(format!(
            "tactic time limit exceeded: {}",
            crate::instrumentation::deadline_context()
        ));
    }
    if derivation.is_none()
        && (pointer_offset_equality_by_frame(&normalized_target, available)
            || equal_by_premise_chain(&normalized_premises, &normalized_target, available))
    {
        return Ok(());
    }
    if derivation.is_none() {
        return Err(format!(
            "`{}` could not check the target from exactly the listed premises: {}\n  premises: {}",
            tactic_name(tactic),
            describe_pure_fact(target, &[], &[]),
            describe_pure_facts(&normalized_premises),
        ));
    }
    Ok(())
}

fn normalizes_context_free(goal: &Proposition) -> bool {
    matches!(normalize_proposition(goal), SimpProposition::True)
        || Assumptions::new()
            .derive_atomic_proposition(goal)
            .or_else(|| Assumptions::new().derive_proposition(goal))
            .is_some()
}

fn pure_goal_certificate_gateway<T>(
    claim_label: &str,
    planner: impl FnOnce() -> Result<TacticCertificate, ClickError>,
    replay: impl FnOnce(&TacticCertificate) -> Result<T, ClickError>,
) -> Result<(TacticCertificate, T), ClickError> {
    let certificate = planner()?;
    TacticCertificate::from_proof_tactics(certificate.tactics()).map_err(|error| {
        ClickError::new(format!(
            "pure goal `{claim_label}` planner returned a non-surface certificate: {error:?}"
        ))
    })?;
    let replayed = replay(&certificate).map_err(|error| {
        ClickError::new(format!(
            "pure goal `{claim_label}` certificate failed ordinary replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    Ok((certificate, replayed))
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
    fn source_site_annotation_rejects_deep_logic_without_using_the_native_stack() {
        let mut surface = ClickProposition::Comparison {
            left: ContractExpression::CBinding("value".to_string()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(0),
            ))),
        };
        for _ in 0..=SOURCE_SITE_ANNOTATION_DEPTH_LIMIT {
            surface = ClickProposition::Not(Box::new(surface));
        }
        let point = ProgramPointRef {
            region: CodeRegionRef::Statement(0),
            kind: ProgramPointKind::Entry,
        };

        let error = surface_with_source_site(&surface, &point)
            .expect_err("deep source-site reconstruction must stop structurally");
        assert!(
            error.message().contains("structural depth bound"),
            "{error:?}"
        );
    }

    #[test]
    fn snapshot_index_finds_a_late_exact_point_inside_a_quantifier() {
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
        let mut states = ProgramPointStates::new();
        states.insert(early, CState::new().with_memory(early_memory));
        states.insert(late.clone(), CState::new().with_memory(target_memory));

        let (exact, compatible) = snapshot_indexed_program_points(&kernel, &states);
        assert_eq!(
            exact.iter().map(|(point, _)| *point).collect::<Vec<_>>(),
            vec![&late]
        );
        assert!(compatible.is_empty());
    }

    #[test]
    fn missing_snapshot_spelling_reports_a_concise_indexed_failure() {
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
        let replay = TacticReplayState::default();
        let state = CState::new().with_memory(CMemory::new().with_block("current", 4));

        let error = checked_surface_comparison_fact_at_point(
            &replay,
            &kernel,
            SurfaceFactMatch::CanonicalExact,
            &[],
            &[],
            &[],
            &state,
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
        )
        .expect_err("an unrecorded snapshot should have no surface spelling");

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
        let points = (0..20)
            .map(|index| ProgramPointRef {
                region: CodeRegionRef::Statement(index),
                kind: ProgramPointKind::Entry,
            })
            .collect::<Vec<_>>();
        let variants = comparison_program_point_variants(&base, &points)
            .expect("comparison should have snapshot variants");
        let position = variants
            .iter()
            .position(|candidate| {
                matches!(
                    candidate,
                    ClickProposition::Comparison {
                        left: ContractExpression::At {
                            selector: VisitSelector::ProgramPoint(ProgramPointRef {
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

    #[test]
    fn fresh_heap_separation_is_not_spelled_as_an_ambient_step_premise() {
        let range = |block| {
            CResource::Memory(CMemoryRange::new(
                Pointer {
                    block,
                    offset: PointerOffsetTerm::Constant(0),
                },
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            ))
        };
        let separation = Proposition::CResourceSeparate {
            left: range(PointerBlock::ExternalArgument),
            right: range(PointerBlock::Heap(7)),
        };

        assert!(Assumptions::new().proves(&separation));
        assert!(
            !statement_step_permission_needs_surface_premise(&separation, &[]),
            "fresh heap provenance is replayable without a potentially stale surface spelling"
        );
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
        let mut replay = TacticReplayState::default();
        replay.defer_post_execution(9, 2, PostExecutionTactic::Simp);

        let [deferred] = replay.post_execution_tactics.as_slice() else {
            panic!("expected one deferred tactic");
        };
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
            proof: Proof::Script(vec![ProofTactic::Assumption]),
        });

        assert_eq!(source_tactic_class(&have), SourceTacticClass::Simple);
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
            proof: Proof::Tactic(SmartTactic::Simp),
        });
        let structural = ProofTactic::Have(ProofHave {
            proposition,
            proof: Proof::Script(Vec::new()),
        });

        assert_eq!(source_tactic_class(&smart), SourceTacticClass::Smart);
        assert_eq!(source_tactic_class(&structural), SourceTacticClass::Control);
    }

    #[test]
    fn generated_alternatives_are_charged_to_the_owning_smart_tactic() {
        let alternatives = ProofTactic::CertifiedAlternatives(Vec::new());

        assert_eq!(
            source_tactic_class(&alternatives),
            SourceTacticClass::Control
        );
        assert!(
            !has_independent_source_timing(&alternatives),
            "the internal alternatives container must not hide smart execute time"
        );
        assert!(has_independent_source_timing(&ProofTactic::Step));
    }

    #[test]
    fn post_execution_timing_charges_have_as_control_flow() {
        let have = PostExecutionTactic::Have(ProofHave {
            proposition: ClickProposition::Comparison {
                left: ContractExpression::CFragment(CExpression::Value(int32(1))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(1))),
            },
            proof: Proof::Script(vec![ProofTactic::Assumption]),
        });

        assert_eq!(post_execution_tactic_timing(&have), ("have", "control"));
    }

    #[test]
    fn pure_fact_replay_availability_ignores_quantifier_binder_ids() {
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
        let replayed = quantified_equality(Variable(3_000_000));

        assert!(pure_fact_is_replay_available(&replayed, &[available]));
    }

    #[test]
    fn pure_certificate_replay_is_transactional() {
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
        let failing = TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple tactic");
        let succeeding = TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a simple tactic");

        let error = pure_goal_certificate_gateway(
            "reflexive.ensures_0",
            || Ok(failing.clone()),
            |certificate| {
                replay_pure_theorem_certificate(
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
        )
        .expect_err("a perturbed smart certificate must not be reported as success");
        assert!(
            error
                .message()
                .contains("certificate failed ordinary replay"),
            "unexpected gateway error: {}",
            error.message()
        );
        replay_pure_theorem_certificate(
            "reflexive.ensures_0",
            &context.requires,
            &goal,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &context,
            &succeeding,
            None,
        )
        .expect("failed replay must not mutate the shared proof inputs");
    }

    #[test]
    fn path_aligned_certificates_preserve_branch_structure() {
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let assumption = TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a certificate");
        let normalize = TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize])
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

        let [ProofTactic::If(proof_if)] = merged.tactics() else {
            panic!("different path certificates should produce one proof branch");
        };
        assert_eq!(proof_if.condition, condition);
        assert_eq!(proof_if.then_tactics, vec![ProofTactic::Assumption]);
        assert_eq!(proof_if.else_tactics, vec![ProofTactic::Normalize]);
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
        let assumption = TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a certificate");
        let normalize = TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize])
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
    proposition: ClickProposition,
    value: bool,
}

// Pure proofs and point-local `have` proofs use flat logical cases. Execution
// proofs use `InternalProofNode` for frontier-local control flow.
fn expand_proof_if_cases(tactics: &[ProofTactic]) -> Result<Vec<ExpandedProofCase>, ClickError> {
    expand_structured_proof_cases(tactics)
}

fn expand_structured_proof_cases(
    tactics: &[ProofTactic],
) -> Result<Vec<ExpandedProofCase>, ClickError> {
    let Some((control_index, control_tactic)) = tactics
        .iter()
        .enumerate()
        .find(|(_, tactic)| matches!(tactic, ProofTactic::If(_)))
    else {
        return Ok(vec![ExpandedProofCase {
            tactics: tactics.to_vec(),
            assumptions: Vec::new(),
        }]);
    };
    let prefix = &tactics[..control_index];
    match control_tactic {
        ProofTactic::If(proof_if) => {
            let suffix_cases = expand_structured_proof_cases(&tactics[control_index + 1..])?;
            let mut cases = Vec::new();
            for (value, branch_tactics) in [
                (true, proof_if.then_tactics.as_slice()),
                (false, proof_if.else_tactics.as_slice()),
            ] {
                for branch in expand_structured_proof_cases(branch_tactics)? {
                    for suffix in &suffix_cases {
                        let boundary = prefix.len() + branch.tactics.len();
                        let mut linear = prefix.to_vec();
                        linear.extend(branch.tactics.iter().cloned());
                        linear.extend(suffix.tactics.iter().cloned());
                        let mut assumptions = vec![ProofCaseAssumption {
                            tactic_index: prefix.len(),
                            proposition: proof_if.condition.clone(),
                            value,
                        }];
                        assumptions.extend(branch.assumptions.iter().map(|assumption| {
                            ProofCaseAssumption {
                                tactic_index: prefix.len() + assumption.tactic_index,
                                proposition: assumption.proposition.clone(),
                                value: assumption.value,
                            }
                        }));
                        assumptions.extend(suffix.assumptions.iter().map(|assumption| {
                            ProofCaseAssumption {
                                tactic_index: boundary + assumption.tactic_index,
                                proposition: assumption.proposition.clone(),
                                value: assumption.value,
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
        _ => unreachable!("control-tactic search only returns proof if"),
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
    Linear {
        tactics: Vec<IndexedTactic>,
        continuation: Box<InternalProofNode>,
    },
    If {
        index: usize,
        condition: ClickProposition,
        then_branch: Box<InternalProofNode>,
        else_branch: Box<InternalProofNode>,
        continuation: Box<InternalProofNode>,
    },
    Branch {
        index: usize,
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
    let Some((control_index, control_tactic)) = tactics
        .iter()
        .enumerate()
        .find(|(_, tactic)| matches!(tactic, ProofTactic::If(_) | ProofTactic::Branch(_)))
    else {
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
        ProofTactic::Branch(proof_branch) => {
            1 + source_tactic_count(&proof_branch.then_tactics)
                + source_tactic_count(&proof_branch.else_tactics)
        }
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

pub(super) fn proof_source_tactic_count(proof: &Proof) -> usize {
    match proof {
        Proof::Default => 0,
        Proof::Tactic(_) => 1,
        Proof::Script(tactics) => source_tactic_count(tactics),
    }
}

#[derive(Clone, Copy)]
pub(super) enum FunctionClaimRef<'a> {
    Effect(usize, &'a EffectClause),
    Ensure(usize, &'a EnsureClause),
}

impl<'a> FunctionClaimRef<'a> {
    pub(super) fn proof(self) -> &'a Proof {
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
                projection_state.memory(),
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
            projection_state.memory(),
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
        state.memory(),
        predicate_environment,
        click_function_environment,
    )?;
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
        let lowered = requirement_propositions(
            std::slice::from_ref(requirement),
            parsed_function.parameters(),
            &arguments,
            state.memory(),
            predicate_environment,
            click_function_environment,
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

pub(super) fn proof_contains_frontier_loop(proof: &Proof) -> bool {
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
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Vec<Proposition> {
    let mut propositions = Vec::new();
    for requirement in requires {
        let Ok(lowered) = requirement_propositions(
            std::slice::from_ref(requirement),
            parameters,
            arguments,
            memory,
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
                if let Err(error) = certify_auto_claim_result(
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
                    &theorems,
                ) {
                    loop_verification_error = Some(error);
                    continue;
                }
                for theorem in &mut theorems {
                    theorem.proof_kind = ProofKind::LoopVerification;
                }
                return Ok(theorems);
            }
            Err(error) => loop_verification_error = Some(error),
        }
    }

    let mut bounded_error = None;
    let mut bounded_certificate_error = None;
    for tactics in bounded_execution_tactic_candidates(claim) {
        match prove_claim_by_tactics(
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
            Ok(theorems) => {
                if let Err(error) = certify_auto_claim_result(
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
                    &theorems,
                ) {
                    bounded_certificate_error.get_or_insert(error);
                    continue;
                }
                return Ok(theorems);
            }
            Err(error) => bounded_error = Some(error),
        }
    }
    Err(bounded_certificate_error
        .or(loop_verification_error)
        .or(bounded_error)
        .unwrap_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}`: `auto` had no certificate candidate to try"
            ))
        }))
}

#[allow(clippy::too_many_arguments)]
fn certify_auto_claim_result(
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
    verified: &[VerifiedCTheorem],
) -> Result<(), ClickError> {
    let certificate = verified
        .first()
        .ok_or_else(|| ClickError::new(format!("`auto` proved no paths for `{claim_label}`")))?
        .expanded_proof_certificate()
        .map_err(|error| {
            ClickError::new(format!(
                "`auto` succeeded internally for `{claim_label}` without a surface certificate: {}",
                error.message()
            ))
        })?;
    let replayed = prove_claim_by_tactics(
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
        certificate.tactics(),
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`auto` surface certificate failed complete replay for `{claim_label}`:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    if replayed.len() != verified.len() {
        return Err(ClickError::new(format!(
            "`auto` surface certificate replayed {} paths for `{claim_label}`, expected {}",
            replayed.len(),
            verified.len()
        )));
    }
    Ok(())
}

pub(super) fn prove_claim_by_frame(
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
    for theorem in &mut theorems {
        theorem.proof_kind = ProofKind::Frame;
    }
    Ok(theorems)
}

pub(super) fn prove_claim_by_simp(
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
    for theorem in &mut theorems {
        theorem.proof_kind = ProofKind::Simp;
    }
    Ok(theorems)
}

fn apply_branch_interface(
    target: &ProgramPointRef,
    assertions: &[ProofAssertion],
    tactic_index: usize,
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    claim_label: &str,
    stable_join_locals: &BTreeMap<String, CValue>,
    needs_abstraction: bool,
) -> Result<(), ClickError> {
    let mut concrete_facts = available_pure_facts.clone();
    let mut established_interface_resources = Vec::new();
    for assertion in assertions {
        match assertion {
            ProofAssertion::Fact(surface_fact) => {
                let fact = lower_point_proposition(
                        surface_fact,
                        &concrete_facts,
                        parameters,
                        arguments,
                        replay.old_reference_state(state),
                        state,
                        None,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `branch ensuring` fact: {message}"
                        ))
                })?;
                replay
                    .surface_propositions
                    .record_lowering(surface_fact, &fact)?;
                let assumptions = assumptions_from_propositions(&concrete_facts);
                if !concrete_facts.contains(&fact) && !assumptions.proves(&fact) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish fact: {}",
                        describe_missing_pure_fact(
                            &fact,
                            &concrete_facts,
                            state.resources().facts(),
                            parameters,
                            arguments,
                            &[]
                        )
                    )));
                }
                if !concrete_facts.contains(&fact) {
                    concrete_facts.push(fact);
                }
            }
            ProofAssertion::Resource(resource) => {
                let expected =
                    lower_resource_clause_at_state(resource, parameters, arguments, state)?;
                let assumptions = assumptions_from_propositions(&concrete_facts);
                let is_observed_core = resource_is_direct_observed_core(
                    resource,
                    &established_interface_resources,
                    resource_environment,
                    claim_label,
                    tactic_index,
                )?;
                if !is_observed_core && !state.resources().satisfies_fact(&expected, &assumptions) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `branch ensuring` did not establish resource fact: {}",
                        describe_missing_resource_fact(
                            &expected,
                            &concrete_facts,
                            state.resources().facts(),
                            parameters,
                            arguments,
                            &[]
                        )
                    )));
                }
                established_interface_resources.push(resource.clone());
            }
        }
    }
    if !needs_abstraction {
        *available_pure_facts = concrete_facts;
        return Ok(());
    }
    let entry_state = replay.execution_start_state(state).clone();
    let mut abstract_state =
        abstract_c_state_for_join(state, stable_join_locals).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not abstract `branch` target state: {message}"
            ))
        })?;

    // Branch abstraction discards incidental source-boundary snapshots, but
    // an explicit proof mark is a deliberate historical dependency. Preserve
    // marks that were common to every continuing arm.
    replay
        .program_point_states
        .retain(|point, _| matches!(point.region, CodeRegionRef::Mark(_)));
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());
    replay.unfolded_predicates.clear();
    replay.case_assumptions.clear();
    replay.execution_abstraction = true;

    let mut exported_resources = ResourceContext::new();
    let mut exported_pure_facts = Vec::new();
    for assertion in assertions {
        if let ProofAssertion::Resource(resource) = assertion {
            let fact =
                lower_resource_clause_at_state(resource, parameters, arguments, &abstract_state)?;
            exported_resources = exported_resources.unchecked_with_fact(fact);
            append_lowered_resource_clause_loadable_fact(
                resource,
                parameters,
                exported_resources
                    .facts()
                    .last()
                    .expect("exported resource was just appended"),
                &abstract_state,
                &mut exported_pure_facts,
            );
            // An `old(...)`-interface ensure needs the exported view's
            // loadability in its entry-memory spelling. Export it exactly
            // when the clause lowers at entry at all and the pre-advance
            // proof state establishes it, the same gate `fact` assertions
            // pass through.
            let mut entry_loadables = Vec::new();
            if let Ok(entry_lowered) =
                lower_resource_clause_at_state(resource, parameters, arguments, &entry_state)
            {
                append_lowered_resource_clause_loadable_fact(
                    resource,
                    parameters,
                    &entry_lowered,
                    &entry_state,
                    &mut entry_loadables,
                );
            }
            if !entry_loadables.is_empty() {
                let mut pre_advance_facts = concrete_facts.clone();
                for fact in &replay.effect_facts {
                    if !pre_advance_facts.contains(fact.proposition()) {
                        pre_advance_facts.push(fact.proposition().clone());
                    }
                }
                let pre_advance = assumptions_from_propositions(&pre_advance_facts);
                for fact in entry_loadables {
                    if pre_advance.proves(&fact) && !exported_pure_facts.contains(&fact) {
                        exported_pure_facts.push(fact);
                    }
                }
            }
            if let ResourceClause::Declared {
                kind: ResourceKind::Composite,
                name,
                ..
            } = resource
            {
                let definition = resource_environment.get(name).ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown resource `{name}`"
                    ))
                })?;
                let CResource::Composite {
                    arguments: resource_arguments,
                    ..
                } = exported_resources
                    .facts()
                    .last()
                    .expect("exported composite resource was just appended")
                    .resource()
                else {
                    unreachable!("composite resource clause lowered to another resource family")
                };
                let (memory, _) = apply_composite_observation_law(
                    definition,
                    resource_arguments,
                    parameters,
                    arguments,
                    &entry_state,
                    abstract_state.memory().clone(),
                    &CValue::Int32(Bitvector32Term::Constant(0)),
                    &mut exported_pure_facts,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not project `branch ensuring` resource `{name}`: {message}"
                    ))
                })?;
                abstract_state = abstract_state.with_memory(memory);
            }
        }
    }
    abstract_state = abstract_state.with_resource_context(exported_resources.clone());
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());

    for assertion in assertions {
        if let ProofAssertion::Fact(surface_fact) = assertion {
            let fact = lower_point_proposition(
                    surface_fact,
                    &exported_pure_facts,
                    parameters,
                    arguments,
                    &entry_state,
                    &abstract_state,
                    None,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not abstract `branch ensuring` fact: {message}"
                    ))
                })?;
            replay
                .surface_propositions
                .record_lowering(surface_fact, &fact)?;
            if !exported_pure_facts.contains(&fact) {
                exported_pure_facts.push(fact);
            }
        }
    }

    let exported_assumptions = assumptions_from_propositions(&exported_pure_facts);
    exported_resources = ResourceContext::new()
            .try_compose_with_facts(exported_resources.facts().iter().cloned(), &exported_assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: invalid `branch ensuring` resource interface: {error:?}"
                ))
            })?;
    abstract_state = abstract_state.with_resource_context(exported_resources);
    replay
        .program_point_states
        .insert(target.clone(), abstract_state.clone());
    *state = abstract_state;
    *available_pure_facts = exported_pure_facts;
    Ok(())
}

fn append_execution_effect_facts(
    target: &mut Vec<ExecutionPureFact>,
    source: &[ExecutionPureFact],
) {
    for fact in source {
        // Verified-call rule results are kernel-certified transition facts,
        // just like memory-effect summaries. Keep them available to later
        // explicit replay without making the surface certificate restate
        // opaque call identities or intermediate-memory equalities.
        if (is_memory_effect_proposition(fact.proposition()) || fact.is_certified())
            && !target.contains(fact)
        {
            target.push(fact.clone());
        }
    }
}

fn fact_transport_transition_facts(
    facts: &[ExecutionPureFact],
    source: &Proposition,
) -> Vec<ExecutionPureFact> {
    let source_memories = c_condition_fact_memories(source);
    let matching_effect = facts.iter().position(|fact| {
        let before = match fact.proposition() {
            Proposition::CMemoryMutatesOnly { before, .. }
            | Proposition::CMemoryEffectSummary { before, .. }
            | Proposition::CHeapLifetimeRetired { before, .. } => before,
            _ => return false,
        };
        source_memories.contains(before)
    });
    let Some(start) = matching_effect else {
        return facts.to_vec();
    };
    let end = facts[start + 1..]
        .iter()
        .position(|fact| is_memory_effect_proposition(fact.proposition()))
        .map(|offset| start + 1 + offset)
        .unwrap_or(facts.len());
    facts[start..end].to_vec()
}

fn is_memory_effect_proposition(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapLifetimeRetired { .. }
    )
}

fn is_implicit_fact_transport_context(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CResourceSeparate { .. }
    )
}

fn resource_is_direct_observed_core(
    required: &ResourceClause,
    established: &[ResourceClause],
    resource_environment: &ResourceEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<bool, ClickError> {
    for parent in established {
        let ResourceClause::Declared {
            kind: ResourceKind::Composite,
            name,
            ..
        } = parent
        else {
            continue;
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(body) = definition.composite_body() else {
            continue;
        };
        // A guarded composite only exposes its children after the guard has
        // been selected. A joined interface does not carry enough state into
        // this syntactic shortcut, so keep guarded children explicit.
        if body.condition().is_some() {
            continue;
        }
        let substitutions =
            resource_argument_substitutions(definition, parent, claim_label, tactic_index)?;
        for child in body.contains() {
            let child = instantiate_resource_clause(child, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate observed child of `{name}`: {message}"
                ))
            })?;
            let core = match child {
                ResourceClause::Read(segment) | ResourceClause::Write(segment) => {
                    ResourceClause::Read(segment)
                }
                ResourceClause::Declared {
                    kind,
                    name,
                    arguments,
                    parameter_types,
                    ..
                } => ResourceClause::Declared {
                    access: ResourceAccessMode::View,
                    kind,
                    name,
                    arguments,
                    parameter_types,
                },
            };
            if &core == required {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

#[allow(clippy::too_many_arguments)]
fn execute_branch_step_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    requested_branch: Option<bool>,
    certified_prerequisites: &[PropositionDerivation],
    prerequisite_policy: StatementPrerequisitePolicy,
    branch_step_policy: BranchStepPolicy,
    complete_empty_branch: bool,
) -> Result<bool, ClickError> {
    replay.completed_branch_regions.clear();
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    let (execution_start_state, mut current_state, statement, remaining) =
        next_top_level_statement_from_execution_point(
            replay,
            state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    let CStatement::If {
        condition,
        then_branch,
        else_branch,
    } = statement
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires the next C statement to be an `if`"
        )));
    };
    let SourceStatementKind::If {
        then_statement_index,
        else_statement_index,
    } = source_region.kind
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` found a C `if` outside its source region"
        )));
    };

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        certified_prerequisites,
        true,
    )?;
    let condition_was_proven = condition_transitions.len() == 1;
    if matches!(branch_step_policy, BranchStepPolicy::RequireProven)
        && condition_transitions.len() != 1
    {
        let expected = requested_branch.map_or("one exact truth value", |take_then| {
            if take_then { "true" } else { "false" }
        });
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove that the next C `if` condition `{}` is {expected}; got {} feasible condition paths\n  condition path facts: {:?}\n{}",
            describe_c_expression(&condition),
            condition_transitions.len(),
            condition_transitions
                .iter()
                .map(|transition| &transition.path_facts)
                .collect::<Vec<_>>(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let condition_transition = match branch_step_policy {
        BranchStepPolicy::RequireProven => condition_transitions
            .into_iter()
            .next()
            .expect("one condition transition was required"),
        BranchStepPolicy::Explore => {
            let requested_branch = requested_branch.expect("branch exploration selects an arm");
            let Some(transition) = condition_transitions
                .into_iter()
                .find(|transition| transition.is_true == requested_branch)
            else {
                return Ok(false);
            };
            transition
        }
    };
    let selected_then = condition_transition.is_true;
    if requested_branch.is_some_and(|take_then| selected_then != take_then) {
        let actual = if selected_then { "then" } else { "else" };
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requested the {} branch, but current pure facts prove the {actual} branch",
            if requested_branch == Some(true) {
                "then"
            } else {
                "else"
            }
        )));
    }

    if matches!(branch_step_policy, BranchStepPolicy::Explore)
        && !condition_was_proven
        && matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning)
    {
        let occurrence = replay.next_path_choice;
        replay.next_path_choice += 1;
        let statement_condition = surface_with_source_site(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        // Prefer a spelling in terms of the shared function-entry snapshot.
        // It remains available after independently explored paths are merged,
        // whereas a later statement-entry state can legitimately differ
        // across those paths and is therefore not retained in the common
        // replay interface. Sorting networks are the representative case:
        // the second comparison's current operand is an entry value selected
        // by the first comparison.
        let condition = replay
            .function_entry_state
            .as_ref()
            .and_then(|entry_state| {
                condition_transition.path_facts.iter().find_map(|fact| {
                    let Proposition::ConditionIs(_, _) = fact else {
                        return None;
                    };
                    let surface =
                        synthesize_surface_proposition(fact, parameters, arguments, entry_state)?;
                    let surface = surface_with_source_site(
                        &surface,
                        &ProgramPointRef {
                            region: CodeRegionRef::Function,
                            kind: ProgramPointKind::Entry,
                        },
                    )
                    .ok()?;
                    Some(if condition_transition.is_true {
                        surface
                    } else {
                        negate_click_proposition(&surface)
                    })
                })
            })
            .unwrap_or(statement_condition);
        replay
            .planned_tactics
            .push(ProofTactic::CertifiedPathAssumption {
                occurrence,
                condition,
                value: condition_transition.is_true,
                facts: condition_transition.path_facts.clone(),
                theorem: condition_transition.theorem.clone(),
            });
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_condition_transition_certificate(
            replay,
            &condition_transition,
            condition_was_proven || matches!(branch_step_policy, BranchStepPolicy::RequireProven),
        );
    }
    *available_pure_facts = condition_transition.pure_facts;
    current_state = crate::kernel::resolve_pending_heap_allocations(
        &current_state,
        &assumptions_from_propositions(available_pure_facts),
    );
    let selected_branch = if selected_then {
        *then_branch
    } else {
        *else_branch
    };
    replay
        .frontier
        .continuations
        .push(ProofExecutionContinuation {
            remaining,
            next_statement_index: source_region.continuation_node,
            kind: ProofExecutionContinuationKind::Branch { statement_index },
        });
    replay.frontier.next_statement_index = if selected_then {
        then_statement_index
    } else {
        else_statement_index
    };
    replay.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state;
    if complete_empty_branch && matches!(selected_branch, CStatement::Skip) {
        let Some(remaining) = resume_after_completed_region(replay, function_block, state) else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
            )));
        };
        replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
    } else {
        replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: selected_branch,
        };
    }
    record_current_statement_entry(
        replay,
        state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        tactic_name,
    )?;
    Ok(true)
}

#[allow(clippy::too_many_arguments)]
fn execute_concrete_loop_head_step(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    certified_prerequisites: &[PropositionDerivation],
    prerequisite_policy: StatementPrerequisitePolicy,
    statement_index: usize,
    loop_index: usize,
    continuation_node: usize,
    execution_start_state: CState,
    current_state: CState,
    loop_statement: CStatement,
    remaining: Option<CStatement>,
) -> Result<(), ClickError> {
    replay.concrete_loop_execution = true;
    let CStatement::While {
        condition, body, ..
    } = loop_statement.clone()
    else {
        unreachable!("concrete loop stepping requires a while statement");
    };

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    record_loop_program_point_state(
        replay,
        function_block,
        loop_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );

    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let condition_transitions = certified_condition_transitions(
        &current_state,
        available_pure_facts,
        &condition,
        &transition_label,
        prerequisite_policy,
        certified_prerequisites,
        true,
    )?;
    if condition_transitions.len() != 1 {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not prove one exact truth value for loop({loop_index}) condition `{}`; got {} feasible condition paths\n{}",
            describe_c_expression(&condition),
            condition_transitions.len(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let condition_transition = condition_transitions
        .into_iter()
        .next()
        .expect("one condition transition was required");
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_condition_transition_certificate(replay, &condition_transition, true);
    }
    *available_pure_facts = condition_transition.pure_facts;
    replay.frontier.execution_start_state = Some(execution_start_state);
    *state = current_state.clone();

    if condition_transition.is_true {
        let loop_head = match remaining {
            Some(remaining) => c_seq(loop_statement, remaining),
            None => loop_statement,
        };
        replay
            .frontier
            .continuations
            .push(ProofExecutionContinuation {
                remaining: Some(loop_head),
                next_statement_index: statement_index,
                kind: ProofExecutionContinuationKind::LoopIteration,
            });
        replay.frontier.next_statement_index = replay
            .source_layout
            .loop_body_entry(loop_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source body of loop({loop_index})"
                ))
            })?;
        replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining: *body };
        record_statement_program_point_state(
            replay,
            function_block,
            replay.frontier.next_statement_index,
            ProgramPointKind::Entry,
            current_state,
        );
        return Ok(());
    }

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    record_loop_program_point_state(
        replay,
        function_block,
        loop_index,
        ProgramPointKind::Exit,
        current_state.clone(),
    );
    let next = if let Some(remaining) = remaining {
        replay.frontier.next_statement_index = continuation_node;
        Some(remaining)
    } else {
        resume_after_completed_region(replay, function_block, &current_state)
    };
    let Some(remaining) = next else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
        )));
    };
    replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
    record_statement_program_point_state(
        replay,
        function_block,
        replay.frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn next_top_level_statement_from_execution_point(
    replay: &TacticReplayState,
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<NextTopLevelStatement, ClickError> {
    match &replay.frontier.point {
        ProofExecutionPoint::FunctionEntry => {
            let execution_start_state = state.clone();
            let current_state = c_function_entry_state(&execution_start_state, function, arguments)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                    ))
                })?;
            let (statement, remaining) =
                split_next_source_operation(function.body()).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                    ))
                })?;
            Ok((execution_start_state, current_state, statement, remaining))
        }
        ProofExecutionPoint::StatementEntry { remaining } => {
            let execution_start_state = replay
                .frontier
                .execution_start_state
                .clone()
                .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` has no execution start state"
                ))
            })?;
            let (statement, remaining) =
                split_next_source_operation(remaining).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `{tactic_name}` failed: {message}"
                    ))
                })?;
            Ok((execution_start_state, state.clone(), statement, remaining))
        }
        ProofExecutionPoint::FunctionExit { .. } => Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        ))),
    }
}

fn record_loop_program_point_state(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    loop_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    record_code_region_program_point_state(
        &mut replay.program_point_states,
        function_block,
        CodeRegion::Loop(loop_index),
        kind,
        state,
    );
}

fn record_statement_program_point_state(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    statement_index: usize,
    kind: ProgramPointKind,
    state: CState,
) {
    record_code_region_program_point_state(
        &mut replay.program_point_states,
        function_block,
        CodeRegion::Statement(statement_index),
        kind,
        state,
    );
}

fn record_code_region_program_point_state(
    program_point_states: &mut ProgramPointStates,
    function_block: &FunctionBlock,
    region: CodeRegion,
    kind: ProgramPointKind,
    state: CState,
) {
    let point_region = match region {
        CodeRegion::Function => CodeRegionRef::Function,
        CodeRegion::Loop(index) => CodeRegionRef::Loop(index),
        CodeRegion::Statement(index) => CodeRegionRef::Statement(index),
    };
    program_point_states.insert(
        ProgramPointRef {
            region: point_region,
            kind,
        },
        state.clone(),
    );
    for label in function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &region)
        .filter_map(StructuralClause::label)
    {
        program_point_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind,
            },
            state.clone(),
        );
    }
}

fn replay_certified_statement_transition(
    evidence: &CertifiedStatementReplay,
    current_state: &CState,
    statement: &CStatement,
    available_pure_facts: &[Proposition],
    context_label: &str,
) -> Result<CertifiedStatementTransition, ClickError> {
    let mut replay_facts = available_pure_facts.to_vec();
    for fact in evidence
        .transition
        .execution_facts
        .iter()
        .filter(|fact| fact.is_certified())
    {
        if !replay_facts.contains(fact.proposition()) {
            replay_facts.push(fact.proposition().clone());
        }
    }
    let mut proposition = evidence.transition.theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        let mut certified_by_derivation = false;
        for derivation in &evidence.transition.prerequisite_derivations {
            if derivation.conclusion() == premise.as_ref()
                && derivation_replays_with_materialized_context(derivation, &replay_facts)?
            {
                certified_by_derivation = true;
                break;
            }
        }
        let certified = exact_fact_is_available(premise, available_pure_facts)
            || materialization_equivalent_available_fact(premise, available_pure_facts).is_some()
            || matches!(normalize_proposition(premise), SimpProposition::True)
            || evidence
                .transition
                .execution_facts
                .iter()
                .any(|fact| fact.is_certified() && fact.proposition() == premise.as_ref())
            || certified_by_derivation;
        if !certified {
            return Err(ClickError::new(format!(
                "{context_label} certificate is missing prerequisite {premise:?}"
            )));
        }
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        state: theorem_state,
        statement: theorem_statement,
        outcome,
    } = proposition
    else {
        return Err(ClickError::new(format!(
            "{context_label} certificate has an unexpected theorem body: {proposition:?}"
        )));
    };
    if theorem_state != current_state || theorem_statement != statement {
        return Err(ClickError::new(format!(
            "{context_label} certificate does not match the current statement execution"
        )));
    }
    if outcome != &evidence.transition.outcome {
        return Err(ClickError::new(format!(
            "{context_label} certificate outcome does not match its execution theorem"
        )));
    }

    let mut transition = evidence.transition.clone();
    transition.pure_facts = available_pure_facts.to_vec();
    for fact in &transition.path_facts {
        if !transition.pure_facts.contains(fact) {
            transition.pure_facts.push(fact.clone());
        }
    }
    let internal_transports = transition
        .fact_transports
        .iter()
        .filter(|transport| transport.statement_local)
        .collect::<Vec<_>>();
    for transport in &internal_transports {
        if !exact_fact_is_available(&transport.source, &transition.pure_facts) {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport is missing exact statement-produced source {:?}",
                transport.source
            )));
        }
        let Proposition::Implies(theorem_source, theorem_target) = transport.theorem.proposition()
        else {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport theorem is not an implication"
            )));
        };
        if theorem_source.as_ref() != &transport.source
            || theorem_target.as_ref() != &transport.target
        {
            return Err(ClickError::new(format!(
                "{context_label} internal fact transport theorem does not match its source and target"
            )));
        }
    }
    let internal_sources = internal_transports
        .iter()
        .map(|transport| &transport.source)
        .collect::<Vec<_>>();
    transition
        .pure_facts
        .retain(|fact| !internal_sources.contains(&fact));
    for transport in internal_transports {
        if !transition.pure_facts.contains(&transport.target) {
            transition.pure_facts.push(transport.target.clone());
        }
    }
    transition.fact_transports.clear();
    Ok(transition)
}

const SOURCE_SITE_ANNOTATION_DEPTH_LIMIT: usize = 32;

fn surface_with_source_site(
    surface: &ClickProposition,
    point: &ProgramPointRef,
) -> Result<ClickProposition, ClickError> {
    if matches!(
        surface,
        ClickProposition::Loadable { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
    ) {
        return Ok(ClickProposition::At {
            selector: VisitSelector::ProgramPoint(point.clone()),
            proposition: Box::new(surface.clone()),
        });
    }
    let expression_at_source = |expression: &ContractExpression| {
        if matches!(expression, ContractExpression::Old(_)) {
            expression.clone()
        } else {
            ContractExpression::At {
                selector: VisitSelector::ProgramPoint(point.clone()),
                expression: Box::new(match expression {
                    ContractExpression::At { expression, .. } => expression.as_ref().clone(),
                    expression => expression.clone(),
                }),
            }
        }
    };
    fn annotate(
        proposition: &ClickProposition,
        expression_at_source: &impl Fn(&ContractExpression) -> ContractExpression,
        depth: usize,
    ) -> Result<ClickProposition, ClickError> {
        if depth >= SOURCE_SITE_ANNOTATION_DEPTH_LIMIT {
            return Err(ClickError::new(
                "Surface Click source-site annotation exceeded its structural depth bound",
            ));
        }
        Ok(match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: expression_at_source(left),
                operator: *operator,
                right: expression_at_source(right),
            },
            ClickProposition::Defined { expression } => ClickProposition::Defined {
                expression: expression_at_source(expression),
            },
            ClickProposition::At { .. } => proposition.clone(),
            ClickProposition::And(left, right) => ClickProposition::And(
                Box::new(annotate(left, expression_at_source, depth + 1)?),
                Box::new(annotate(right, expression_at_source, depth + 1)?),
            ),
            ClickProposition::Or(left, right) => ClickProposition::Or(
                Box::new(annotate(left, expression_at_source, depth + 1)?),
                Box::new(annotate(right, expression_at_source, depth + 1)?),
            ),
            ClickProposition::Not(body) => {
                ClickProposition::Not(Box::new(annotate(body, expression_at_source, depth + 1)?))
            }
            ClickProposition::Implies(left, right) => ClickProposition::Implies(
                Box::new(annotate(left, expression_at_source, depth + 1)?),
                Box::new(annotate(right, expression_at_source, depth + 1)?),
            ),
            ClickProposition::ForAll { c_type, name, body } => ClickProposition::ForAll {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::Exists { c_type, name, body } => ClickProposition::Exists {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAll {
                start: expression_at_source(start),
                end: expression_at_source(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => ClickProposition::RangeAny {
                start: expression_at_source(start),
                end: expression_at_source(end),
                item: item.clone(),
                body: Box::new(annotate(body, expression_at_source, depth + 1)?),
            },
            ClickProposition::PredicateCall { name, arguments } => {
                ClickProposition::PredicateCall {
                    name: name.clone(),
                    arguments: arguments.iter().map(expression_at_source).collect(),
                }
            }
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => proposition.clone(),
        })
    }
    annotate(surface, &expression_at_source, 0)
}

fn predicate_call_source_site(surface: &ClickProposition) -> Option<ProgramPointRef> {
    let ClickProposition::PredicateCall { arguments, .. } = surface else {
        return None;
    };
    arguments.iter().find_map(|argument| {
        let ContractExpression::At {
            selector: VisitSelector::ProgramPoint(point),
            ..
        } = argument
        else {
            return None;
        };
        Some(point.clone())
    })
}

#[allow(clippy::too_many_arguments)]
fn execute_step_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    _assumptions: &Assumptions,
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    certified_prerequisites: &[PropositionDerivation],
    certified_replay: Option<&CertifiedStatementReplay>,
    prerequisite_policy: StatementPrerequisitePolicy,
    fact_transport_policy: StatementFactTransportPolicy,
    loop_step_policy: LoopStepPolicy,
) -> Result<(), ClickError> {
    replay.completed_branch_regions.clear();
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve source statement({statement_index})"
        ))
    })?;
    if matches!(source_region.kind, SourceStatementKind::If { .. }) {
        let entered = execute_branch_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            claim_label,
            tactic_index,
            "step",
            None,
            certified_prerequisites,
            prerequisite_policy,
            BranchStepPolicy::RequireProven,
            false,
        )?;
        debug_assert!(entered);
        return Ok(());
    }
    let loop_index = match source_region.kind {
        SourceStatementKind::Loop { loop_index } => Some(loop_index),
        SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
    };
    let (execution_start_state, current_state, source_statement, remaining) =
        next_top_level_statement_from_execution_point(
            replay,
            state,
            function,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
        )?;
    if matches!(source_statement, CStatement::While { .. }) && loop_index.is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not resolve the source loop at statement({statement_index})"
        )));
    }
    if let (Some(loop_index), CStatement::While { .. }) = (loop_index, &source_statement)
        && matches!(loop_step_policy, LoopStepPolicy::EnterBody)
    {
        return execute_concrete_loop_head_step(
            replay,
            state,
            available_pure_facts,
            function_block,
            parameters,
            arguments,
            claim_label,
            tactic_index,
            tactic_name,
            certified_prerequisites,
            prerequisite_policy,
            statement_index,
            loop_index,
            source_region.continuation_node,
            execution_start_state,
            current_state,
            source_statement,
            remaining,
        );
    }
    let step_statement = source_statement;

    record_statement_program_point_state(
        replay,
        function_block,
        statement_index,
        ProgramPointKind::Entry,
        current_state.clone(),
    );
    if let Some(loop_index) = loop_index {
        record_loop_program_point_state(
            replay,
            function_block,
            loop_index,
            ProgramPointKind::Entry,
            current_state.clone(),
        );
    }
    let current_resources = current_state.resources().facts().to_vec();
    let transition_label = format!("`{claim_label}` tactic {tactic_index}: `{tactic_name}`");
    let direct_transition = certified_replay
        .map(|evidence| {
            replay_certified_statement_transition(
                evidence,
                &current_state,
                &step_statement,
                available_pure_facts,
                &transition_label,
            )
        })
        .transpose()?;
    let transitions = if let Some(transition) = direct_transition {
        replay.next_opaque_call = certified_replay
            .expect("a direct transition requires replay evidence")
            .next_opaque_call;
        replay.next_verification_variable = certified_replay
            .expect("a direct transition requires replay evidence")
            .next_verification_variable;
        vec![transition]
    } else {
        certified_statement_transitions(
            &current_state,
            available_pure_facts,
            &step_statement,
            function_environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &transition_label,
            &mut replay.next_opaque_call,
            &mut replay.next_verification_variable,
            prerequisite_policy,
            fact_transport_policy,
            certified_prerequisites,
        )?
        .0
    };
    if transitions.len() > 1
        && transitions
            .iter()
            .all(|transition| matches!(transition.outcome, CStatementOutcome::Return { .. }))
    {
        // A single source return can have several valid operational outcomes,
        // notably when it returns an unresolved malloc result. This is not C
        // control flow and needs no proof-level case split: all successors
        // complete the function at the same statement boundary.
        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
            let mut prerequisite_derivations = Vec::new();
            let mut exact_premises = Vec::new();
            for transition in &transitions {
                for derivation in &transition.prerequisite_derivations {
                    if !prerequisite_derivations.contains(derivation) {
                        prerequisite_derivations.push(derivation.clone());
                    }
                }
                if transition.consults_conditions {
                    for fact in ambient_condition_facts(available_pure_facts) {
                        if !exact_premises.contains(&fact) {
                            exact_premises.push(fact);
                        }
                    }
                }
                for obligation in &transition.obligations {
                    if exact_fact_is_available(obligation.proposition(), available_pure_facts)
                        && !exact_premises.contains(obligation.proposition())
                    {
                        exact_premises.push(obligation.proposition().clone());
                    }
                }
            }
            replay
                .planned_tactics
                .push(ProofTactic::CertifiedStatementStep {
                    prerequisite_derivations,
                    exact_premises,
                });
        }

        let mut common_pure_facts = transitions[0].pure_facts.clone();
        common_pure_facts.retain(|fact| {
            transitions
                .iter()
                .skip(1)
                .all(|transition| transition.pure_facts.contains(fact))
        });
        let mut completed_outcomes = Vec::new();
        for transition in transitions {
            let mut completed_execution_facts = transition.execution_facts;
            append_execution_effect_facts(&mut completed_execution_facts, &replay.effect_facts);
            let return_assumptions = assumptions_from_propositions(&transition.pure_facts);
            let (outcome, obligations) = c_function_outcome_from_statement_outcome(
                &execution_start_state,
                function,
                transition.outcome,
                transition.obligations,
                &return_assumptions,
            );
            completed_outcomes.push((outcome, completed_execution_facts, obligations));
        }
        let completed = c_function_execution_candidates_from_outcomes(
            execution_start_state.clone(),
            function.clone(),
            arguments.to_vec(),
            completed_outcomes,
        );
        let replay_state = execution_start_state.clone();
        set_replay_execution(
            replay,
            claim_label,
            tactic_index,
            tactic_name,
            execution_start_state,
            completed,
        )?;
        replay.frontier.next_statement_index = source_region.continuation_node;
        *available_pure_facts = common_pure_facts;
        *state = replay_state;
        return Ok(());
    }
    if transitions.len() != 1 {
        if matches!(prerequisite_policy, StatementPrerequisitePolicy::Exact) {
            let safe = transitions
                .iter()
                .filter(|transition| {
                    matches!(
                        transition.outcome,
                        CStatementOutcome::Normal(_) | CStatementOutcome::Return { .. }
                    )
                })
                .collect::<Vec<_>>();
            if let [safe] = safe.as_slice()
                && let Some(required) = safe
                    .pure_facts
                    .iter()
                    .find(|fact| !exact_fact_is_available(fact, available_pure_facts))
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` is missing exact prerequisite needed to select the safe statement transition: {required:?}"
                )));
            }
        }
        if let Some(kind) = transitions
            .iter()
            .find_map(|transition| match &transition.outcome {
                CStatementOutcome::UndefinedBehavior(kind) => Some(kind.clone()),
                _ => None,
            })
        {
            let outcome = CFunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &[]
                )
            )));
        }
        if let Some(error) = transitions
            .iter()
            .find_map(|transition| match &transition.outcome {
                CStatementOutcome::RuntimeError(error) => Some(error),
                _ => None,
            })
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced runtime error: {}\n{}",
                describe_runtime_error(error, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &[]
                )
            )));
        }
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires exactly one statement successor for {step_statement:?}, got {}\n{}",
            transitions.len(),
            describe_proof_context(
                available_pure_facts,
                &current_resources,
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let transition = transitions
        .into_iter()
        .next()
        .expect("one statement transition was required");
    if matches!(loop_step_policy, LoopStepPolicy::ApplyVerifiedRule)
        && let Some(loop_index) = loop_index
        && matches!(transition.outcome, CStatementOutcome::Normal(_))
        && let Some(loop_clause) = function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
    {
        // The verified loop rule exports its effect summaries first, followed
        // by one lowered fact for each invariant check in declaration order,
        // followed by facts from the false loop-condition path. Preserve that
        // structural association instead of searching the ambient context for
        // a proposition that happens to match.
        let mut invariant_targets = transition.pure_facts.iter().filter(|fact| {
            !available_pure_facts.contains(fact)
                && !matches!(
                    fact,
                    Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CHeapLifetimeRetired { .. }
                )
        });
        let mut mapped_invariants = Vec::new();
        for surface in loop_clause
            .items()
            .iter()
            .filter(|item| item.kind() == StructuralItemKind::Invariant)
            .filter_map(StructuralItem::proposition)
        {
            let target = if let Some((_, target)) = mapped_invariants
                .iter()
                .find(|(mapped_surface, _)| *mapped_surface == surface)
            {
                *target
            } else {
                invariant_targets.next().ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: verified loop summary omitted an exported fact for an invariant"
                    ))
                })?
            };
            mapped_invariants.push((surface, target));
            let exit_point = ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Exit,
            };
            let exit_surface = surface_with_source_site(surface, &exit_point)?;
            replay
                .surface_propositions
                .record_lowering(&exit_surface, target)?;
        }
    }
    if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        append_statement_transition_certificate(
            replay,
            &transition,
            if loop_index.is_some() {
                loop_step_policy
            } else {
                LoopStepPolicy::EnterBody
            },
        );
    }
    // Preserve a surface name for each store while its exact source statement
    // is still known. The certified equation records the address evaluated
    // before the write and the memory immediately after it; a later attempt
    // to reconstruct that name from the final state can only re-evaluate the
    // address and loses this association for deep, state-dependent indices.
    let store_exit_point = ProgramPointRef {
        region: CodeRegionRef::Statement(statement_index),
        kind: ProgramPointKind::Exit,
    };
    for equation in crate::kernel::certified_store_equations(&transition.execution_facts) {
        if let Some(ClickProposition::Comparison {
            left,
            operator,
            right,
        }) = synthesize_surface_proposition(&equation, parameters, arguments, &current_state)
        {
            let store_entry_point = ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            };
            let at =
                |point: &ProgramPointRef, expression: ContractExpression| ContractExpression::At {
                    selector: VisitSelector::ProgramPoint(point.clone()),
                    expression: Box::new(expression),
                };
            // The neutral pointer addition makes the Index use the outer
            // exit snapshot's memory while its base and index retain their
            // entry values.
            let exit_load = if let ContractExpression::Index(base, index) = left {
                ContractExpression::Index(
                    Box::new(ContractExpression::Add(
                        Box::new(at(&store_entry_point, *base)),
                        Box::new(ContractExpression::CFragment(CExpression::Value(int32(0)))),
                    )),
                    Box::new(at(&store_entry_point, *index)),
                )
            } else {
                left
            };
            let surface = ClickProposition::Comparison {
                left: at(&store_exit_point, exit_load),
                operator,
                right: at(&store_entry_point, right),
            };
            replay
                .surface_propositions
                .record_lowering(&surface, &equation)?;
        }
    }
    let execution_pure_facts = transition.execution_facts;
    append_execution_effect_facts(&mut replay.effect_facts, &execution_pure_facts);
    let transition_obligations = transition.obligations;
    let successor_pure_facts = transition.pure_facts;
    let outcome = transition.outcome;
    if let Some(statement_exit_state) = match &outcome {
        CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
            Some(state.clone())
        }
        CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => None,
        CStatementOutcome::VerificationDiverges => None,
    } {
        record_statement_program_point_state(
            replay,
            function_block,
            statement_index,
            ProgramPointKind::Exit,
            statement_exit_state,
        );
        if let Some(loop_index) = loop_index {
            record_loop_program_point_state(
                replay,
                function_block,
                loop_index,
                ProgramPointKind::Exit,
                match &outcome {
                    CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
                        state.clone()
                    }
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)
                    | CStatementOutcome::VerificationDiverges => unreachable!(),
                },
            );
        }
    }

    match outcome {
        CStatementOutcome::Normal(next_state) => {
            let remaining = if let Some(remaining) = remaining {
                replay.frontier.next_statement_index = source_region.continuation_node;
                remaining
            } else if let Some(remaining) =
                resume_after_completed_region(replay, function_block, &next_state)
            {
                remaining
            } else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` reached the end of the function without a return"
                )));
            };
            *available_pure_facts = successor_pure_facts;
            replay.frontier.execution_start_state = Some(execution_start_state);
            replay.frontier.point = ProofExecutionPoint::StatementEntry { remaining };
            *state = next_state.clone();
            record_statement_program_point_state(
                replay,
                function_block,
                replay.frontier.next_statement_index,
                ProgramPointKind::Entry,
                next_state,
            );
        }
        CStatementOutcome::Return { .. } => {
            if let CStatementOutcome::Return {
                state: return_state,
                ..
            } = &outcome
            {
                record_completed_continuation_exits(replay, function_block, return_state);
            }
            let return_assumptions = assumptions_from_propositions(&successor_pure_facts);
            let (outcome, obligations) = c_function_outcome_from_statement_outcome(
                &execution_start_state,
                function,
                outcome,
                transition_obligations,
                &return_assumptions,
            );
            let mut completed_execution_facts = execution_pure_facts;
            append_execution_effect_facts(&mut completed_execution_facts, &replay.effect_facts);
            let completed = c_function_execution_candidates_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                vec![(outcome, completed_execution_facts, obligations)],
            );
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            replay.frontier.next_statement_index = source_region.continuation_node;
            *state = replay_state;
        }
        CStatementOutcome::VerificationDiverges => {
            let mut completed_execution_facts = execution_pure_facts;
            append_execution_effect_facts(&mut completed_execution_facts, &replay.effect_facts);
            let completed = c_function_execution_candidates_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                vec![(
                    CFunctionOutcome::VerificationDiverges,
                    completed_execution_facts,
                    transition_obligations,
                )],
            );
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                claim_label,
                tactic_index,
                tactic_name,
                execution_start_state,
                completed,
            )?;
            replay.frontier.next_statement_index = source_region.continuation_node;
            *state = replay_state;
        }
        CStatementOutcome::UndefinedBehavior(kind) => {
            let outcome = CFunctionOutcome::UndefinedBehavior(kind);
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced {}\n{}",
                describe_function_outcome(&outcome, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
        CStatementOutcome::RuntimeError(error) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` produced runtime error: {}\n{}",
                describe_runtime_error(&error, parameters, arguments),
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
    }
    Ok(())
}

fn resume_after_completed_region(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    state: &CState,
) -> Option<CStatement> {
    while let Some(continuation) = replay.frontier.continuations.pop() {
        if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
            replay.completed_branch_regions.push(statement_index);
            record_statement_program_point_state(
                replay,
                function_block,
                statement_index,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
        replay.frontier.next_statement_index = continuation.next_statement_index;
        if let Some(remaining) = continuation.remaining {
            return Some(remaining);
        }
    }
    None
}

fn record_completed_continuation_exits(
    replay: &mut TacticReplayState,
    function_block: &FunctionBlock,
    state: &CState,
) {
    while let Some(continuation) = replay.frontier.continuations.pop() {
        if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
            replay.completed_branch_regions.push(statement_index);
            record_statement_program_point_state(
                replay,
                function_block,
                statement_index,
                ProgramPointKind::Exit,
                state.clone(),
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn record_current_statement_entry(
    replay: &mut TacticReplayState,
    state: &CState,
    function_block: &FunctionBlock,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    let current_state = match &replay.frontier.point {
        ProofExecutionPoint::FunctionEntry => c_function_entry_state(state, function, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{tactic_name}` could not bind function arguments"
                ))
            })?,
        ProofExecutionPoint::StatementEntry { .. } => state.clone(),
        ProofExecutionPoint::FunctionExit { .. } => return Ok(()),
    };
    record_statement_program_point_state(
        replay,
        function_block,
        replay.frontier.next_statement_index,
        ProgramPointKind::Entry,
        current_state,
    );
    Ok(())
}

const BOUNDED_EXECUTE_STEP_LIMIT: usize = 10_000;

#[derive(Clone)]
struct BoundedProofFrontier {
    replay: TacticReplayState,
    state: CState,
    pure_facts: Vec<Proposition>,
}

#[allow(clippy::too_many_arguments)]
fn bounded_execute_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    prerequisite_policy: StatementPrerequisitePolicy,
) -> Result<(), ClickError> {
    let mut pending = vec![BoundedProofFrontier {
        replay: replay.clone(),
        state: state.clone(),
        pure_facts: available_pure_facts.clone(),
    }];
    let mut completed = Vec::new();
    let mut executed_steps = 0;

    while let Some(mut frontier) = pending.pop() {
        if frontier.replay.is_at_function_exit() {
            completed.push(frontier);
            continue;
        }
        if executed_steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget at statement({})",
                frontier.replay.frontier.next_statement_index
            )));
        }
        executed_steps += 1;

        let source_region = frontier
            .replay
            .source_layout
            .statement(frontier.replay.frontier.next_statement_index)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `execute` could not resolve source statement({})",
                    frontier.replay.frontier.next_statement_index
                ))
            })?;
        if matches!(source_region.kind, SourceStatementKind::If { .. }) {
            for take_then in [false, true] {
                let mut branch = frontier.clone();
                let entered = execute_branch_step_from_execution_point(
                    &mut branch.replay,
                    &mut branch.state,
                    &mut branch.pure_facts,
                    function_block,
                    function,
                    parameters,
                    arguments,
                    claim_label,
                    tactic_index,
                    "execute",
                    Some(take_then),
                    &[],
                    prerequisite_policy,
                    BranchStepPolicy::Explore,
                    false,
                )?;
                if entered {
                    pending.push(branch);
                }
            }
            continue;
        }

        let assumptions = assumptions_from_propositions(&frontier.pure_facts);
        execute_step_from_execution_point(
            &mut frontier.replay,
            &mut frontier.state,
            &mut frontier.pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute",
            &[],
            None,
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::EnterBody,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` failed after {executed_steps} small execution steps: {}",
                error.message()
            ))
        })?;
        pending.push(frontier);
    }

    let alternatives = if matches!(prerequisite_policy, StatementPrerequisitePolicy::Planning) {
        Some(
            completed
                .iter()
                .map(|frontier| {
                    ProofReplayPlan::from_planned_tactics(&frontier.replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute` path planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?,
        )
    } else {
        None
    };
    merge_bounded_execution_frontiers(
        replay,
        state,
        available_pure_facts,
        function,
        arguments,
        completed,
        claim_label,
        tactic_index,
    )?;
    if let Some(alternatives) = alternatives {
        replay.planned_tactics = vec![ProofTactic::CertifiedAlternatives(alternatives)];
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn merge_bounded_execution_frontiers(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function: &CFunction,
    arguments: &[CExpression],
    mut completed: Vec<BoundedProofFrontier>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    if completed.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute` produced no complete execution paths"
        )));
    }

    let execution_start_state = completed[0]
        .replay
        .frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute` has no execution start state"
            ))
        })?;
    let mut common_pure_facts = completed[0].pure_facts.clone();
    common_pure_facts.retain(|fact| {
        completed
            .iter()
            .skip(1)
            .all(|frontier| frontier.pure_facts.contains(fact))
    });
    let mut common_program_points = completed[0].replay.program_point_states.clone();
    common_program_points.retain(|point, point_state| {
        completed
            .iter()
            .skip(1)
            .all(|frontier| frontier.replay.program_point_states.get(point) == Some(point_state))
    });

    let mut paths = Vec::new();
    for frontier in &completed {
        let execution = frontier
            .replay
            .execution()
            .expect("completed bounded frontier should have an execution");
        for path in execution.paths() {
            let mut facts = path.execution_facts();
            for fact in &frontier.pure_facts {
                let fact = ExecutionPureFact::new(fact.clone());
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
            paths.push((path.outcome().clone(), facts, path.obligations().to_vec()));
        }
    }
    let execution = c_function_execution_candidates_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        paths,
    );

    let mut merged = completed.remove(0);
    merged.replay.program_point_states = common_program_points;
    merged.replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    merged.state = execution_start_state;
    merged.pure_facts = common_pure_facts;
    *replay = merged.replay;
    *state = merged.state;
    *available_pure_facts = merged.pure_facts;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_rest_from_execution_point(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    loop {
        let can_execute_one_step = match &replay.frontier.point {
            ProofExecutionPoint::FunctionEntry => {
                split_next_execution_step(function.body()).is_ok()
            }
            ProofExecutionPoint::StatementEntry { remaining } => {
                split_next_execution_step(remaining).is_ok()
            }
            ProofExecutionPoint::FunctionExit { .. } => return Ok(()),
        };
        if !can_execute_one_step {
            break;
        }

        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute",
            &[],
            None,
            StatementPrerequisitePolicy::Planning,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
        )?;
    }

    if !replay.is_at_function_exit() {
        bounded_execute_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            function_environment,
            claim_label,
            tactic_index,
            StatementPrerequisitePolicy::Planning,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_until_statement(
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    statement_index: usize,
    claim_label: &str,
    tactic_index: usize,
    prerequisite_policy: StatementPrerequisitePolicy,
) -> Result<(), ClickError> {
    if replay.source_layout.statement(statement_index).is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: function has no source statement({statement_index}); it contains {} statement regions",
            replay.source_layout.statement_count()
        )));
    }

    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot run after execution already reached function exit"
        )));
    }
    if statement_index < replay.frontier.next_statement_index {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` cannot move backward from statement({})",
            replay.frontier.next_statement_index
        )));
    }

    while replay.frontier.next_statement_index != statement_index {
        let region_start = replay.frontier.next_statement_index;
        let assumptions = assumptions_from_propositions(available_pure_facts);
        execute_step_from_execution_point(
            replay,
            state,
            available_pure_facts,
            function_block,
            function,
            parameters,
            arguments,
            &assumptions,
            function_environment,
            claim_label,
            tactic_index,
            "execute_until",
            &[],
            None,
            prerequisite_policy,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::ApplyVerifiedRule,
        )?;
        if replay.is_at_function_exit() {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` reached function exit before its target"
            )));
        }
        if replay.frontier.next_statement_index > statement_index {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until(statement({statement_index}))` target is not reachable from the current execution path; advancing statement({region_start}) moved the frontier to statement({})",
                replay.frontier.next_statement_index
            )));
        }
    }
    Ok(())
}

fn split_next_execution_step(
    statement: &CStatement,
) -> Result<(CStatement, Option<CStatement>), String> {
    let (source_statement, remaining) = split_next_source_operation(statement)?;
    if matches!(source_statement, CStatement::If { .. }) {
        return Err("next statement is an `if`; use `step()` or `step()`".to_string());
    }
    Ok((source_statement, remaining))
}

fn split_next_source_operation(
    statement: &CStatement,
) -> Result<(CStatement, Option<CStatement>), String> {
    let mut statements = Vec::new();
    flatten_top_level_sequence(statement, &mut statements).map_err(|message| {
        format!("could not flatten the lowered statement sequence: {message}")
    })?;
    let Some(source_statement) = statements.first() else {
        return Err("lowered statement is missing its source operation".to_string());
    };
    let remaining = sequence_from_statements(&statements[1..]);
    Ok((source_statement.clone(), remaining))
}

fn flatten_top_level_sequence(
    statement: &CStatement,
    statements: &mut Vec<CStatement>,
) -> Result<(), String> {
    match statement {
        CStatement::Seq(first, second) => {
            flatten_top_level_sequence(first, statements)?;
            flatten_top_level_sequence(second, statements)
        }
        statement => {
            statements.push(statement.clone());
            Ok(())
        }
    }
}

fn sequence_from_statements(statements: &[CStatement]) -> Option<CStatement> {
    let (first, rest) = statements.split_first()?;
    Some(rest.iter().cloned().fold(first.clone(), c_seq))
}

fn set_replay_execution(
    replay: &mut TacticReplayState,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
    execution_start_state: CState,
    execution: CFunctionExecutionCandidates,
) -> Result<(), ClickError> {
    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` cannot run after execution already reached function exit"
        )));
    }
    replay.frontier.execution_start_state = Some(execution_start_state);
    replay.frontier.point = ProofExecutionPoint::FunctionExit { execution };
    Ok(())
}

fn require_function_exit(
    replay: &TacticReplayState,
    claim_label: &str,
    tactic_index: usize,
    tactic_name: &str,
) -> Result<(), ClickError> {
    if !replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires execution to reach function exit first"
        )));
    }
    Ok(())
}
