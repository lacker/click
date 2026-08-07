use super::diagnostics::*;
use super::validation::tactic_name;
use super::*;

mod claim_proofs;
mod execution_planning;
mod fact_reasoning;
mod point_proofs;
mod pure_theorems;
mod replay_state;
mod resources;
mod structural;
mod surface_certificates;
mod surface_synthesis;
mod theorem_application;
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
use replay_state::*;
pub(super) use replay_state::{
    active_c0_tactic_expansion_request, capture_c0_proof_site_expansion,
    capture_c0_tactic_expansion,
};
pub(super) use resources::instantiate_composite_resource_body_resources;
use resources::*;
use structural::*;
use surface_certificates::*;
pub(super) use surface_synthesis::synthesize_surface_proposition;
#[cfg(test)]
use surface_synthesis::{SURFACE_SYNTHESIS_DEPTH_LIMIT, bitvector_term_is_load_free};
use surface_synthesis::{surface_synthesis_exhaustion_description, surface_synthesis_failure};
use theorem_application::*;

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

#[allow(clippy::too_many_arguments)]
fn checked_surface_fact_at_point(
    replay: &TacticReplayState,
    kernel: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let check = |surface: &ClickProposition| {
        lower_point_proposition(
            surface,
            available,
            parameters,
            arguments,
            replay.old_reference_state(state),
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(ClickError::new)
    };
    if let Ok(surface) = replay.surface_propositions.checked_surface(kernel, check) {
        return Ok(surface);
    }
    if let Ok(ClickProposition::Loadable { segment }) = replay.surface_propositions.surface(kernel)
    {
        let mut old_segment = segment.clone();
        old_segment.state = ContractSegmentState::Old;
        let old_candidate = ClickProposition::Loadable {
            segment: old_segment,
        };
        if check(&old_candidate).ok().as_ref() == Some(kernel) {
            return Ok(old_candidate);
        }
    }
    if let Proposition::Predicate {
        name,
        arguments: target_arguments,
    } = kernel
    {
        let same_non_memory_arguments = |arguments: &[Term]| {
            arguments.len() == target_arguments.len()
                && arguments.iter().zip(target_arguments).all(|(left, right)| {
                    matches!((left, right), (Term::CMemory(_), Term::CMemory(_))) || left == right
                })
        };
        for recorded in replay.surface_propositions.kernel_facts() {
            let Proposition::Predicate {
                name: recorded_name,
                arguments,
            } = recorded
            else {
                continue;
            };
            if recorded_name != name || !same_non_memory_arguments(arguments) {
                continue;
            }
            let Ok(ClickProposition::PredicateCall {
                name: surface_name,
                arguments: surface_arguments,
            }) = replay.surface_propositions.surface(recorded)
            else {
                continue;
            };
            for point in replay.program_point_states.keys().rev() {
                let candidate = ClickProposition::PredicateCall {
                    name: surface_name.clone(),
                    arguments: surface_arguments
                        .iter()
                        .map(|argument| ContractExpression::At {
                            selector: VisitSelector::ProgramPoint(point.clone()),
                            expression: Box::new(argument.clone()),
                        })
                        .collect(),
                };
                if check(&candidate).ok().as_ref() == Some(kernel) {
                    return Ok(candidate);
                }
            }
        }
    }
    let kernel_memories = c_condition_fact_memories(kernel);
    if !kernel_memories.is_empty()
        && kernel_memories
            .iter()
            .any(|memory| !memory.has_same_snapshot_markers(state.memory()))
    {
        return Err(ClickError::new(format!(
            "kernel fact belongs to a different recorded memory snapshot: {kernel:?}"
        )));
    }
    let candidate = synthesize_surface_proposition(kernel, parameters, arguments, state)
        .ok_or_else(|| {
            ClickError::new(surface_synthesis_failure(
                "kernel fact has no recorded or structurally synthesized Click spelling",
                kernel,
            ))
        })?;
    let lowered = check(&candidate);
    if lowered.as_ref().is_ok_and(|lowered| lowered == kernel) {
        return Ok(candidate);
    }
    if let ClickProposition::Loadable { segment } = &candidate {
        let mut old_segment = segment.clone();
        old_segment.state = ContractSegmentState::Old;
        let old_candidate = ClickProposition::Loadable {
            segment: old_segment,
        };
        if check(&old_candidate).ok().as_ref() == Some(kernel) {
            return Ok(old_candidate);
        }
    }
    match lowered {
        Ok(lowered) => Err(ClickError::new(format!(
            "synthesized Click fact does not lower to the kernel fact at this proof point\n  Click: {candidate:?}\n  lowered: {lowered:?}\n  kernel: {kernel:?}"
        ))),
        Err(error) => Err(ClickError::new(format!(
            "synthesized Click fact could not be lowered at this proof point\n  Click: {candidate:?}\n  error: {}\n  kernel: {kernel:?}",
            error.message()
        ))),
    }
}

fn proposition_snapshot_memories(proposition: &Proposition) -> Vec<CMemory> {
    if !matches!(
        proposition,
        Proposition::And(_, _)
            | Proposition::Or(_, _)
            | Proposition::Not(_)
            | Proposition::Implies(_, _)
            | Proposition::ForAll { .. }
            | Proposition::Exists { .. }
            | Proposition::Predicate { .. }
            | Proposition::Equal(_, _)
    ) {
        return c_condition_fact_memories(proposition);
    }
    let mut memories = Vec::new();
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            Proposition::ConditionIs(_, _) => {
                for memory in c_condition_fact_memories(proposition) {
                    if !memories.contains(&memory) {
                        memories.push(memory);
                    }
                }
            }
            Proposition::Equal(left, right) => {
                for term in [left, right] {
                    if let Term::CMemory(memory) = term
                        && !memories.contains(memory)
                    {
                        memories.push(memory.clone());
                    }
                }
            }
            Proposition::Predicate { arguments, .. } => {
                for argument in arguments {
                    if let Term::CMemory(memory) = argument
                        && !memories.contains(memory)
                    {
                        memories.push(memory.clone());
                    }
                }
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Proposition::Not(body)
            | Proposition::ForAll { body, .. }
            | Proposition::Exists { body, .. } => pending.push(body),
            _ => {}
        }
    }
    memories
}

type ProgramPointStateMatches<'a> = Vec<(&'a ProgramPointRef, &'a CState)>;

fn snapshot_indexed_program_points<'a>(
    kernel: &Proposition,
    program_point_states: &'a ProgramPointStates,
) -> (ProgramPointStateMatches<'a>, ProgramPointStateMatches<'a>) {
    let memories = proposition_snapshot_memories(kernel);
    let mut exact = Vec::new();
    let mut compatible = Vec::new();
    for (point, state) in program_point_states.iter().rev() {
        if memories.iter().any(|memory| memory == state.memory()) {
            exact.push((point, state));
        } else if memories
            .iter()
            .any(|memory| memory.has_same_snapshot_markers(state.memory()))
        {
            compatible.push((point, state));
        }
    }
    (exact, compatible)
}

#[derive(Clone, Copy)]
enum SurfaceFactMatch {
    CanonicalExact,
    ReplayEquivalent,
}

#[allow(clippy::too_many_arguments)]
fn checked_surface_comparison_fact_at_point(
    replay: &TacticReplayState,
    kernel: &Proposition,
    match_kind: SurfaceFactMatch,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let matches_kernel = |lowered: &Proposition| {
        if matches!(match_kind, SurfaceFactMatch::CanonicalExact) {
            return normalize_direct_atomic_memory_loads(lowered)
                == normalize_direct_atomic_memory_loads(kernel);
        }
        let lowered = normalize_direct_atomic_memory_loads(lowered);
        let kernel = normalize_direct_atomic_memory_loads(kernel);
        condition_polarity_equivalent(&lowered, &kernel)
            || lowered == kernel
            || materialization_equivalent_available_fact(&kernel, std::slice::from_ref(&lowered))
                .is_some()
            || quantified_binder_equivalent(&lowered, &kernel)
    };
    // Candidates below are matched through the permissive candidate lowering
    // (symbolic contract loads allowed), but the emitted certificate is
    // replayed by the ordinary executor, whose strict lowering carries
    // loadability obligations. A spelling that only lowers permissively —
    // for example a snapshot fact whose `at(...)` anchor was dropped so its
    // current-state loads are not provably loadable — must not be emitted.
    let strictly_replayable = |surface: &ClickProposition| {
        replay
            .surface_propositions
            .available_kernel(surface, available)
            .is_some()
            || lower_point_proposition(
                surface,
                available,
                parameters,
                arguments,
                replay.old_reference_state(state),
                state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .is_ok_and(|premise| {
                exact_fact_is_available(&premise, available)
                    || materialization_equivalent_available_fact(&premise, available).is_some()
            })
    };
    // An explicitly snapshot-indexed spelling already paired with this exact
    // available kernel fact is itself a checked replay certificate. Re-lowering
    // every such spelling at the end of a long execution is both redundant and
    // potentially quadratic in the accumulated snapshots; `StepUsing` consults
    // this same map before lowering its premises. Current-state spellings are
    // not stable across statements, so they must still be lowered below.
    let recorded_surfaces = replay
        .surface_propositions
        .surfaces(kernel)
        .collect::<Vec<_>>();
    for surface in recorded_surfaces.into_iter().rev() {
        if proposition_contains_at_expression(surface)
            && replay
                .surface_propositions
                .available_kernel(surface, available)
                .is_some_and(&matches_kernel)
        {
            return Ok(surface.clone());
        }
    }
    if let Ok(surface) = checked_surface_fact_at_point(
        replay,
        kernel,
        available,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    ) && strictly_replayable(&surface)
    {
        return Ok(surface);
    }

    let mut bases = Vec::new();
    for surface in replay.surface_propositions.surfaces(kernel) {
        if !bases.contains(surface) {
            bases.push(surface.clone());
        }
    }
    let (exact_points, compatible_points) =
        snapshot_indexed_program_points(kernel, &replay.program_point_states);
    if let Some(surface) = synthesize_surface_proposition(kernel, parameters, arguments, state)
        && !bases.contains(&surface)
    {
        bases.push(surface);
    }
    for (_, point_state) in exact_points.iter().chain(&compatible_points) {
        if let Some(surface) =
            synthesize_surface_proposition(kernel, parameters, arguments, point_state)
            && !bases.contains(&surface)
        {
            bases.push(surface);
        }
    }
    for base in &bases {
        if let Ok(lowered) = lower_surface_candidate_at_point(
            replay,
            base,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        ) && (matches_kernel(&lowered)
            || proposition_contains_at_expression(base)
                && quantified_replay_equivalent_available_fact(
                    kernel,
                    std::slice::from_ref(&lowered),
                )
                .is_some())
            && strictly_replayable(base)
        {
            return Ok(base.clone());
        }
    }
    for (point, _) in exact_points.iter().chain(&compatible_points) {
        for base in &bases {
            let ClickProposition::Comparison {
                left,
                operator,
                right,
            } = base
            else {
                continue;
            };
            let at_point = |expression: &ContractExpression| ContractExpression::At {
                selector: VisitSelector::ProgramPoint((*point).clone()),
                expression: Box::new(expression.clone()),
            };
            let candidates = [
                ClickProposition::Comparison {
                    left: at_point(left),
                    operator: *operator,
                    right: at_point(right),
                },
                ClickProposition::Comparison {
                    left: at_point(left),
                    operator: *operator,
                    right: right.clone(),
                },
                ClickProposition::Comparison {
                    left: left.clone(),
                    operator: *operator,
                    right: at_point(right),
                },
            ];
            for candidate in candidates {
                let lowered = lower_surface_candidate_at_point(
                    replay,
                    &candidate,
                    available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                );
                if lowered.is_ok_and(|lowered| matches_kernel(&lowered))
                    && strictly_replayable(&candidate)
                {
                    return Ok(candidate);
                }
            }
        }
    }
    for indexed_points in [&exact_points, &compatible_points] {
        let points = indexed_points
            .iter()
            .map(|(point, _)| (*point).clone())
            .collect::<Vec<_>>();
        for base in &bases {
            let Some(variants) = comparison_program_point_variants(base, &points) else {
                continue;
            };
            for candidate in variants {
                check_verification_deadline()?;
                if lower_surface_candidate_at_point(
                    replay,
                    &candidate,
                    available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                )
                .is_ok_and(|lowered| matches_kernel(&lowered))
                    && strictly_replayable(&candidate)
                {
                    return Ok(candidate);
                }
            }
        }
    }
    if let Some(exhaustion) = surface_synthesis_exhaustion_description() {
        return Err(ClickError::new(format!(
            "comparison fact has no checked Click spelling at this proof point: {exhaustion}"
        )));
    }
    Err(ClickError::new(format!(
        "comparison fact has no replayable Surface Click spelling at this proof point ({} exact and {} compatible recorded snapshots, {} structural bases)",
        exact_points.len(),
        compatible_points.len(),
        bases.len(),
    )))
}

#[allow(clippy::too_many_arguments)]
fn record_surface_replay_tactic(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    tactic: &ProofTactic,
    _statement_uses_memory_context: Option<bool>,
) {
    if replay.surface_replay.blocker.is_some() {
        return;
    }
    if let Err(error) = check_verification_deadline() {
        replay.surface_replay.block(error.message());
        return;
    }
    match tactic {
        ProofTactic::CertifiedStatementReplay(evidence) => {
            let mut exact_premises = if evidence.transition.consults_conditions {
                ambient_condition_facts(available)
            } else {
                Vec::new()
            };
            for obligation in &evidence.transition.obligations {
                if exact_fact_is_available(obligation.proposition(), available)
                    && !exact_premises.contains(obligation.proposition())
                {
                    exact_premises.push(obligation.proposition().clone());
                }
            }
            record_surface_replay_tactic(
                replay,
                state,
                available,
                function_block,
                parameters,
                arguments,
                predicate_environment,
                click_function_environment,
                &ProofTactic::CertifiedStatementStep {
                    prerequisite_derivations: evidence.transition.prerequisite_derivations.clone(),
                    // Planning reasons from the whole ambient context, so a
                    // condition it consulted leaves no trace in the transition
                    // and cannot be recovered from it afterwards. A statement
                    // whose execution can consult conditions therefore carries
                    // them all; one that only moves a variable or a constant,
                    // in a context that cannot turn a condition into a memory
                    // conclusion, carries none.
                    exact_premises,
                },
                None,
            );
            let post_state = match &evidence.transition.outcome {
                CStatementOutcome::Normal(state) | CStatementOutcome::Return { state, .. } => {
                    Some(state)
                }
                CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => {
                    None
                }
                CStatementOutcome::VerificationDiverges => None,
            };
            for transport in &evidence.transition.fact_transports {
                if !transport.statement_local
                    || !is_internal_snapshot_frame_witness(&transport.source)
                {
                    continue;
                }
                let surface = replay
                    .surface_propositions
                    .surface(&transport.target)
                    .ok()
                    .cloned()
                    .or_else(|| {
                        post_state.and_then(|state| {
                            synthesize_surface_proposition(
                                &transport.target,
                                parameters,
                                arguments,
                                state,
                            )
                        })
                    });
                let Some(surface) = surface else {
                    replay.surface_replay.block(format!(
                        "statement-local frame witness has no checked Click spelling: {:?}",
                        transport.target
                    ));
                    continue;
                };
                replay.surface_replay.push(ProofTactic::Have(ProofHave {
                    proposition: surface,
                    proof: Proof::Script(vec![ProofTactic::Normalize]),
                }));
            }
            // A verified call's postconditions are public, but CallAssign's
            // result identity is only useful to Surface Click after the value
            // has been stored in its C local. Publish exactly those
            // postconditions that synthesize through `c(local)`. Internal
            // havoc identities and intermediate-memory facts remain hidden.
            if let Some(post_state) = post_state {
                let mut emitted = Vec::new();
                for fact in evidence
                    .transition
                    .execution_facts
                    .iter()
                    .rev()
                    .filter(|fact| fact.is_public() && fact.is_certified())
                {
                    let Some(surface) = synthesize_surface_proposition(
                        fact.proposition(),
                        parameters,
                        arguments,
                        post_state,
                    ) else {
                        continue;
                    };
                    if !public_local_result_surface(&surface, parameters)
                        || emitted.contains(&surface)
                    {
                        continue;
                    }
                    let Ok(lowered) = lower_surface_candidate_at_point(
                        replay,
                        &surface,
                        &evidence.transition.pure_facts,
                        parameters,
                        arguments,
                        post_state,
                        predicate_environment,
                        click_function_environment,
                    ) else {
                        continue;
                    };
                    if !exact_fact_is_available(&lowered, &evidence.transition.pure_facts) {
                        continue;
                    }
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface, &lowered)
                    {
                        replay.surface_replay.block(format!(
                            "public opaque-call result fact has no stable Surface Click spelling: {}",
                            error.message()
                        ));
                        continue;
                    }
                    emitted.push(surface.clone());
                    replay.surface_replay.push(ProofTactic::Have(ProofHave {
                        proposition: surface,
                        proof: Proof::Script(vec![ProofTactic::Assumption]),
                    }));
                }
            }
        }
        ProofTactic::CertifiedLoopSummaryReplay(evidence) => {
            let exact_premises = theorem_implication_premises(&evidence.transition.theorem)
                .into_iter()
                .filter(|premise| {
                    !evidence
                        .transition
                        .execution_facts
                        .iter()
                        .any(|fact| fact.is_certified() && fact.proposition() == premise)
                })
                .collect();
            record_surface_replay_tactic(
                replay,
                state,
                available,
                function_block,
                parameters,
                arguments,
                predicate_environment,
                click_function_environment,
                &ProofTactic::CertifiedLoopSummaryStep {
                    prerequisite_derivations: evidence.transition.prerequisite_derivations.clone(),
                    exact_premises,
                },
                _statement_uses_memory_context,
            );
        }
        ProofTactic::CertifiedStatementStep {
            prerequisite_derivations: derivations,
            exact_premises,
        } => {
            replay.surface_replay.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            });
            let premises = Ok::<_, ClickError>({
                let mut premises = Vec::new();
                let derivation_context = derivations
                    .iter()
                    .flat_map(PropositionDerivation::context_premises)
                    .collect::<BTreeSet<_>>();
                let explicit_dependency_facts = derivation_context
                    .iter()
                    .map(|fact| (*fact).clone())
                    .chain(exact_premises.iter().cloned())
                    .collect::<Vec<_>>();
                let projected_resource_facts = state.resources().observable_facts_assuming_valid(
                    &assumptions_from_propositions(&explicit_dependency_facts),
                );
                // Preserve exactly the facts selected by prerequisite
                // derivations or explicitly tracked by the transition.
                // Resource/loadability facts are projected deterministically
                // from the current resource state after these premises are
                // installed.
                //
                // Do not copy every implication premise from the execution
                // theorem: it contains the transitive ambient context,
                // including internal call identities and verifier variables.
                // Ordinary replay below remains the authority on whether this
                // explicit, source-expressible subset is sufficient.
                let mut available_conjuncts = Vec::new();
                for fact in available {
                    atomic_conjuncts(fact, &mut available_conjuncts);
                }
                // Source-spelled memory-range separation facts (for example
                // a resource body's canonical
                // `separate(memory(object(owner)), ...)` aggregate) that can
                // re-fold a decomposed per-field separation back to its
                // declared spelling below. Entailment assumptions are built
                // lazily, at most once per candidate.
                let memory_separation_bases = |fact: &Proposition| {
                    let Proposition::CResourceSeparate { left, right } = fact else {
                        return None;
                    };
                    let (CResource::Memory(left), CResource::Memory(right)) = (left, right) else {
                        return None;
                    };
                    Some((left.base().clone(), right.base().clone()))
                };
                let mut spelled_separations = available_conjuncts
                    .iter()
                    .copied()
                    .filter_map(|candidate| {
                        let bases = memory_separation_bases(candidate)?;
                        replay
                            .surface_propositions
                            .surfaces(candidate)
                            .next()
                            .is_some()
                            .then_some((candidate, bases, None::<Assumptions>))
                    })
                    .collect::<Vec<_>>();
                for fact in &available_conjuncts {
                    let fact = *fact;
                    let selected_by_derivation = derivation_context.iter().any(|required| {
                        (*required).eq(fact)
                            || normalize_direct_atomic_memory_loads(required)
                                == normalize_direct_atomic_memory_loads(fact)
                    }) || exact_premises.iter().any(|required| {
                        required == fact
                            || normalize_direct_atomic_memory_loads(required)
                                == normalize_direct_atomic_memory_loads(fact)
                    });
                    // A permission the resource projection reproduces is
                    // reconstructed by the replay for itself. One it does not
                    // reproduce is only available because the ambient context
                    // carried it, so the certificate has to spell it.
                    let non_reconstructible_permission =
                        statement_step_permission_needs_surface_premise(
                            fact,
                            &projected_resource_facts,
                        );
                    if !selected_by_derivation && !non_reconstructible_permission {
                        continue;
                    }
                    // A separation carried only as an ambient permission may
                    // be one piece of a source-spelled aggregate (`unfold`
                    // decomposes `separate(memory(object(owner)), ...)` into
                    // per-field separations). Re-fold it: emit the strictly
                    // stronger declared fact, whose canonical spelling the
                    // replay derives the per-field pieces from, instead of
                    // the decomposed piece.
                    let fact = 'fold: {
                        let fact_bases = if selected_by_derivation {
                            None
                        } else {
                            memory_separation_bases(fact)
                        };
                        let Some((fact_left, fact_right)) = fact_bases else {
                            break 'fold fact;
                        };
                        let mut fact_is_foldable = None;
                        for (candidate, (left, right), cached) in &mut spelled_separations {
                            if *candidate == fact
                                || !(*left == fact_left && *right == fact_right
                                    || *left == fact_right && *right == fact_left)
                            {
                                continue;
                            }
                            // An arithmetically true separation (same base,
                            // disjoint constant ranges) is derivable from
                            // any premise set, so entailment cannot pick a
                            // fold target for it; keep its own spelling.
                            let foldable = *fact_is_foldable.get_or_insert_with(|| {
                                assumptions_from_propositions(&[])
                                    .derive_atomic_proposition(fact)
                                    .is_none()
                            });
                            if !foldable {
                                break;
                            }
                            let assumptions = cached.get_or_insert_with(|| {
                                assumptions_from_propositions(std::slice::from_ref(*candidate))
                            });
                            if assumptions.derive_atomic_proposition(fact).is_some()
                                && assumptions_from_propositions(std::slice::from_ref(fact))
                                    .derive_atomic_proposition(candidate)
                                    .is_none()
                            {
                                break 'fold *candidate;
                            }
                        }
                        fact
                    };
                    // A certified statement prerequisite may be represented by
                    // a source fact whose lowering differs only by canonical
                    // load materialization. Keep that checked equivalence here:
                    // the generated `step() using` certificate is subsequently
                    // replayed by the ordinary executor, which remains the
                    // authority on whether the selected premise is sufficient.
                    let Ok(surface) = checked_surface_comparison_fact_at_point(
                        replay,
                        fact,
                        SurfaceFactMatch::ReplayEquivalent,
                        available,
                        parameters,
                        arguments,
                        state,
                        predicate_environment,
                        click_function_environment,
                    ) else {
                        continue;
                    };
                    if !premises.contains(&surface) {
                        premises.push(surface);
                    }
                }
                premises
            });
            match premises {
                Ok(premises) if premises.is_empty() => replay
                    .surface_replay
                    .push(ProofTactic::StepUsing(Vec::new())),
                Ok(premises) => replay.surface_replay.push(ProofTactic::StepUsing(premises)),
                Err(error) => replay.surface_replay.block(format!(
                    "could not express a statement-step premise at the current proof point: {}",
                    error.message()
                )),
            }
        }
        ProofTactic::CertifiedLoopSummaryStep {
            prerequisite_derivations: derivations,
            exact_premises,
        } => {
            let loop_index = replay
                .source_layout
                .statement(replay.frontier.next_statement_index)
                .and_then(|region| match region.kind {
                    SourceStatementKind::Loop { loop_index } => Some(loop_index),
                    SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
                });
            let Some(loop_index) = loop_index else {
                replay
                    .surface_replay
                    .block("certified loop-summary replay is not at a source loop entry");
                return;
            };
            replay.surface_replay.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            });
            let mut surface_available = available.to_vec();
            let mut loop_summary_premises: Vec<(Proposition, ClickProposition)> = Vec::new();
            if let Some(loop_clause) = function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            {
                let mut unfold_names = Vec::new();
                for proof in [loop_clause.initialize_proof(), loop_clause.preserve_proof()]
                    .into_iter()
                    .flatten()
                {
                    for tactic in proof.tactics().unwrap_or_default() {
                        if let ProofTactic::UnfoldPredicate(name) = tactic
                            && !unfold_names.contains(name)
                        {
                            unfold_names.push(name.clone());
                        }
                    }
                }
                for name in unfold_names {
                    let assumptions = assumptions_from_propositions(&surface_available);
                    let surface_unfoldings = surface_available
                        .iter()
                        .flat_map(|kernel| {
                            let Proposition::Predicate {
                                name: kernel_name, ..
                            } = kernel
                            else {
                                return Vec::new();
                            };
                            if kernel_name != &name {
                                return Vec::new();
                            }
                            let Some(unfolded) = unfold_predicates_in_proposition(
                                predicate_environment,
                                click_function_environment,
                                std::slice::from_ref(&name),
                                kernel,
                                &assumptions,
                            )
                            .ok() else {
                                return Vec::new();
                            };
                            replay
                                .surface_propositions
                                .surfaces(kernel)
                                .filter_map(|surface| {
                                    let ClickProposition::PredicateCall {
                                        name: surface_name,
                                        arguments: surface_arguments,
                                    } = surface
                                    else {
                                        return None;
                                    };
                                    let source_point = predicate_call_source_site(surface);
                                    let definition = predicate_environment.get(surface_name)?;
                                    let mut surface = instantiate_click_predicate_definition(
                                        definition,
                                        surface_arguments,
                                    )
                                    .ok()?;
                                    if let Some(point) = source_point {
                                        surface =
                                            surface_with_source_site(&surface, &point).ok()?;
                                    }
                                    Some((surface, unfolded.clone()))
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    match unfold_available_predicate_facts(
                        predicate_environment,
                        click_function_environment,
                        std::slice::from_ref(&name),
                        &surface_available,
                    ) {
                        Ok(unfolded) => surface_available = unfolded,
                        Err(_) => continue,
                    }
                    for (surface, kernel) in surface_unfoldings {
                        if replay
                            .surface_propositions
                            .record_lowering(&surface, &kernel)
                            .is_err()
                        {
                            continue;
                        }
                    }
                    replay
                        .surface_replay
                        .push(ProofTactic::UnfoldPredicate(name));
                }
                let current_loadable_haves = surface_available
                    .iter()
                    .filter_map(|kernel| {
                        if !matches!(kernel, Proposition::CMemoryLoadable { .. }) {
                            return None;
                        }
                        let ClickProposition::Loadable { segment } =
                            replay.surface_propositions.surface(kernel).ok()?
                        else {
                            return None;
                        };
                        let mut current_segment = segment.clone();
                        current_segment.state = ContractSegmentState::Current;
                        Some(ProofHave {
                            proposition: ClickProposition::Loadable {
                                segment: current_segment,
                            },
                            proof: Proof::Tactic(SmartTactic::Simp),
                        })
                    })
                    .collect::<Vec<_>>();
                for have in current_loadable_haves {
                    let Ok((fact, plan)) = plan_smart_have_at_current_point(
                        &have,
                        "surface loop-summary certificate",
                        0,
                        &surface_available,
                        parameters,
                        arguments,
                        replay.old_reference_state(state),
                        state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        &[],
                        None,
                    ) else {
                        continue;
                    };
                    if replay
                        .surface_propositions
                        .record_lowering(&have.proposition, &fact)
                        .is_err()
                    {
                        continue;
                    }
                    if !loop_summary_premises
                        .iter()
                        .any(|(kernel, _)| kernel == &fact)
                    {
                        loop_summary_premises.push((fact.clone(), have.proposition.clone()));
                    }
                    if surface_available.contains(&fact) {
                        continue;
                    }
                    match surface_smart_have_certificate(
                        replay,
                        state,
                        &surface_available,
                        parameters,
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        &have,
                        &plan,
                        &[],
                    ) {
                        Ok(certificate) => replay
                            .surface_replay
                            .tactics
                            .extend_from_slice(certificate.tactics()),
                        Err(error) => replay.surface_replay.block(error.message()),
                    }
                    surface_available.push(fact);
                }
                fn append_surface_conjuncts(
                    proposition: &ClickProposition,
                    conjuncts: &mut Vec<ClickProposition>,
                ) {
                    if let ClickProposition::And(left, right) = proposition {
                        append_surface_conjuncts(left, conjuncts);
                        append_surface_conjuncts(right, conjuncts);
                    } else {
                        conjuncts.push(proposition.clone());
                    }
                }
                let mut invariants = Vec::new();
                for invariant in loop_clause
                    .items()
                    .iter()
                    .filter(|item| item.kind() == StructuralItemKind::Invariant)
                    .filter_map(StructuralItem::proposition)
                {
                    append_surface_conjuncts(invariant, &mut invariants);
                }
                for invariant in invariants {
                    let have = ProofHave {
                        proposition: invariant,
                        proof: Proof::Tactic(SmartTactic::Simp),
                    };
                    let planned = plan_smart_have_at_current_point(
                        &have,
                        "surface loop-summary certificate",
                        0,
                        &surface_available,
                        parameters,
                        arguments,
                        replay.old_reference_state(state),
                        state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        &[],
                        None,
                    );
                    let (fact, plan) = match planned {
                        Ok(planned) => planned,
                        Err(_) => continue,
                    };
                    if !loop_summary_premises
                        .iter()
                        .any(|(kernel, _)| kernel == &fact)
                    {
                        loop_summary_premises.push((fact.clone(), have.proposition.clone()));
                    }
                    if !surface_available.contains(&fact) {
                        if let Err(error) = replay
                            .surface_propositions
                            .record_lowering(&have.proposition, &fact)
                        {
                            replay.surface_replay.block(format!(
                                "could not record a loop invariant for its surface certificate: {}",
                                error.message()
                            ));
                            return;
                        }
                        match surface_smart_have_certificate(
                            replay,
                            state,
                            &surface_available,
                            parameters,
                            arguments,
                            predicate_environment,
                            click_function_environment,
                            &have,
                            &plan,
                            &[],
                        ) {
                            Ok(certificate) => replay
                                .surface_replay
                                .tactics
                                .extend_from_slice(certificate.tactics()),
                            Err(error) => replay.surface_replay.block(error.message()),
                        }
                        surface_available.push(fact);
                    }
                }
            }
            for derivation in derivations {
                if surface_available.contains(derivation.conclusion()) {
                    continue;
                }
                if let Ok((conclusion, proof)) = lower_surface_atomic_derivation(
                    replay,
                    derivation,
                    None,
                    &surface_available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                ) {
                    replay.surface_replay.push(ProofTactic::Have(ProofHave {
                        proposition: conclusion,
                        proof,
                    }));
                    surface_available.push(derivation.conclusion().clone());
                }
            }
            let needed = exact_premises
                .iter()
                .cloned()
                .chain(
                    loop_summary_premises
                        .iter()
                        .map(|(kernel, _)| kernel.clone()),
                )
                .chain(
                    derivations
                        .iter()
                        .flat_map(PropositionDerivation::context_premises),
                )
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>();
            let contextual_step = |replay: &TacticReplayState, needed: &[Proposition]| {
                let normalized_needed = needed
                    .iter()
                    .map(|fact| {
                        (
                            fact,
                            normalize_proposition(fact),
                            normalize_direct_atomic_memory_loads(fact),
                        )
                    })
                    .collect::<Vec<_>>();
                let mut premises = Vec::new();
                for (fact, normalized, materialized) in normalized_needed {
                    let check_candidate = |available_fact: &Proposition| {
                        checked_surface_comparison_fact_at_point(
                            replay,
                            available_fact,
                            SurfaceFactMatch::CanonicalExact,
                            &surface_available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        )
                        .ok()
                    };
                    // Exact and normalization-equivalent premises are the
                    // common case. Try that cheap path across the whole
                    // context before asking the general prover whether an
                    // unrelated ambient fact entails this dependency.
                    let surface = surface_available
                        .iter()
                        .filter(|available| {
                            *available == fact
                                || normalize_proposition(available) == normalized
                                || normalize_direct_atomic_memory_loads(available) == materialized
                        })
                        .find_map(&check_candidate)
                        .or_else(|| {
                            surface_available.iter().find_map(|available_fact| {
                                if assumptions_from_propositions(std::slice::from_ref(
                                    available_fact,
                                ))
                                .proves(fact)
                                {
                                    check_candidate(available_fact)
                                } else {
                                    None
                                }
                            })
                        });
                    if let Some(surface) = surface
                        && !premises.contains(&surface)
                    {
                        premises.push(surface);
                    }
                }
                Ok::<_, ClickError>(premises)
            };
            let premises = contextual_step(replay, &needed).map(|mut premises| {
                for (_, surface) in &loop_summary_premises {
                    if !premises.contains(surface) {
                        premises.push(surface.clone());
                    }
                }
                premises
            });
            replay.surface_replay.block(match premises {
                Ok(_) => "a detached loop-summary certificate has no surface spelling; use a frontier-local `loop { ... }` tactic".to_string(),
                Err(error) => format!(
                    "could not express a loop-summary premise at the current proof point: {}",
                    error.message()
                ),
            });
        }
        ProofTactic::CertifiedFactTransport { source, target, .. } => {
            let Some(step_entry) = replay.surface_replay.last_step_entry.clone() else {
                replay
                    .surface_replay
                    .block("fact transport has no preceding statement-entry snapshot");
                return;
            };
            let transport_assumptions = assumptions_from_propositions(available);
            let mut base_surfaces = Vec::new();
            for proposition in [source, target] {
                for surface in replay.surface_propositions.surfaces(proposition) {
                    if !base_surfaces.contains(surface) {
                        base_surfaces.push(surface.clone());
                    }
                }
                if let Some(surface) =
                    synthesize_surface_proposition(proposition, parameters, arguments, state)
                    && !base_surfaces.contains(&surface)
                {
                    base_surfaces.push(surface);
                }
                let normalized = normalize_direct_atomic_memory_loads(proposition);
                for recorded in replay.surface_propositions.kernel_facts() {
                    let matches = normalize_direct_atomic_memory_loads(recorded) == normalized
                        || (memory_erased_comparison(recorded).is_some()
                            && memory_erased_comparison(recorded)
                                == memory_erased_comparison(proposition)
                            && proposition_outer_load_memory(proposition).is_some_and(|after| {
                                certified_fact_transport_reaches_through(
                                    recorded,
                                    proposition,
                                    after,
                                    &transport_assumptions,
                                    &replay.effect_facts,
                                )
                            }));
                    if !matches {
                        continue;
                    }
                    for surface in replay.surface_propositions.surfaces(recorded) {
                        if !base_surfaces.contains(surface) {
                            base_surfaces.push(surface.clone());
                        }
                    }
                }
            }
            if base_surfaces.is_empty() {
                replay.surface_replay.block(format!(
                    "fact transport has no recorded or synthesized Click comparison spelling\n  source: {source:?}\n  target: {target:?}"
                ));
                return;
            }
            let mut points = replay
                .program_point_states
                .keys()
                .cloned()
                .collect::<Vec<_>>();
            if !points.contains(&step_entry) {
                points.push(step_entry);
            }
            let mut candidates = Vec::new();
            for base_surface in base_surfaces {
                let Some(variants) = comparison_program_point_variants(&base_surface, &points)
                else {
                    replay.surface_replay.block(
                        "fact transport surface lowering currently supports comparisons only",
                    );
                    return;
                };
                for candidate in variants {
                    if !candidates.contains(&candidate) {
                        candidates.push(candidate);
                    }
                }
            }
            let find_candidate = |expected: &Proposition| {
                if crate::instrumentation::deadline_exceeded() {
                    return None;
                }
                let normalized_expected = normalize_direct_atomic_memory_loads(expected);
                let lower = |candidate: &ClickProposition| {
                    lower_surface_candidate_at_point(
                        replay,
                        candidate,
                        available,
                        parameters,
                        arguments,
                        state,
                        predicate_environment,
                        click_function_environment,
                    )
                    .ok()
                };
                for candidate in &candidates {
                    if crate::instrumentation::deadline_exceeded() {
                        return None;
                    }
                    let actual = lower(candidate)?;
                    if normalize_direct_atomic_memory_loads(&actual) == normalized_expected {
                        return Some((candidate.clone(), actual));
                    }
                    // The certified pair may sit at a snapshot no recorded
                    // point reproduces syntactically; accept a candidate
                    // whose lowering provably transports to the certified
                    // spelling.
                    if memory_erased_comparison(&actual).is_some()
                        && memory_erased_comparison(&actual) == memory_erased_comparison(expected)
                        && let Some(after) = proposition_outer_load_memory(expected)
                        && certified_fact_transport_reaches_through(
                            &actual,
                            expected,
                            after,
                            &transport_assumptions,
                            &replay.effect_facts,
                        )
                    {
                        return Some((candidate.clone(), actual));
                    }
                }
                None
            };
            let selected_by_preceding_step = replay
                .surface_replay
                .tactics
                .iter()
                .rev()
                .find_map(|tactic| match tactic {
                    ProofTactic::StepUsing(premises) => Some(Some(premises)),
                    ProofTactic::Step => Some(None),
                    _ => None,
                })
                .flatten()
                .is_some_and(|premises| {
                    premises.iter().any(|premise| {
                        replay
                            .surface_propositions
                            .surfaces(source)
                            .any(|surface| surface == premise)
                    })
                });
            match (find_candidate(source), find_candidate(target)) {
                (
                    Some((_surface_source, _)),
                    Some((surface_target, lowered_surface_target)),
                ) if selected_by_preceding_step => {
                    // `step() using` replays with Selected fact transport, so a
                    // listed statement-entry source is already carried by the
                    // certified statement transition. Do not ask the
                    // post-state context to independently reconstruct the
                    // same frame proof.
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface_target, &lowered_surface_target)
                    {
                        replay.surface_replay.block(format!(
                            "could not retain the certified fact transport target spelling: {}",
                            error.message()
                        ));
                    }
                }
                (
                    Some((surface_source, _)),
                    Some((surface_target, lowered_surface_target)),
                )
                    if surface_source == surface_target =>
                {
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface_target, &lowered_surface_target)
                    {
                        replay.surface_replay.block(format!(
                            "could not retain the certified fact transport target spelling: {}",
                            error.message()
                        ));
                    }
                }
                (
                    Some((surface_source, lowered_surface_source)),
                    Some((surface_target, lowered_surface_target)),
                ) => {
                    let transition_facts =
                        fact_transport_transition_facts(&replay.effect_facts, &lowered_surface_source);
                    match plan_explicit_fact_transport(
                        &surface_source,
                        &lowered_surface_source,
                        &lowered_surface_target,
                        available,
                        &transition_facts,
                        parameters,
                        arguments,
                        replay,
                        state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            replay.surface_replay.push(ProofTactic::TransportUsing {
                                source: surface_source,
                                target: surface_target.clone(),
                                premises,
                            });
                            if let Err(error) = replay
                                .surface_propositions
                                .record_lowering(&surface_target, &lowered_surface_target)
                            {
                                replay.surface_replay.block(format!(
                                    "could not retain the certified fact transport target spelling: {}",
                                    error.message()
                                ));
                            }
                        }
                        Err(error) => {
                            // A pre-state fact may be impossible to derive
                            // from the post-state context of an opaque call.
                            // In that case make the exact statement-entry
                            // source a dependency of the preceding step, so
                            // Selected transport replays it as part of the
                            // statement certificate itself.
                            let attached = replay
                                .surface_replay
                                .tactics
                                .iter_mut()
                                .rev()
                                .find_map(|tactic| match tactic {
                                    ProofTactic::StepUsing(premises) => {
                                        if !premises.contains(&surface_source) {
                                            premises.push(surface_source.clone());
                                        }
                                        Some(true)
                                    }
                                    ProofTactic::Step => Some(false),
                                    _ => None,
                                })
                                .unwrap_or(false);
                            if attached {
                                if let Err(record_error) = replay
                                    .surface_propositions
                                    .record_lowering(&surface_source, &lowered_surface_source)
                                    .and_then(|()| {
                                        replay.surface_propositions.record_lowering(
                                            &surface_target,
                                            &lowered_surface_target,
                                        )
                                    })
                                {
                                    replay.surface_replay.block(format!(
                                        "could not retain the statement-attached fact transport spelling: {}",
                                        record_error.message()
                                    ));
                                }
                            } else {
                                replay.surface_replay.block(fact_transport_planning_failure(
                                    &surface_source,
                                    &surface_target,
                                    &replay.unfolded_predicates,
                                    &error,
                                ));
                            }
                        }
                    }
                }
                _ => replay.surface_replay.block(format!(
                    "no placement of the comparison operands at the {} recorded program points lowered to the certified fact transport\n  certified source: {source:?}\n  certified target: {target:?}",
                    points.len()
                )),
            }
        }
        ProofTactic::FinishCertifiedFactTransports(_) => {}
        ProofTactic::CertifiedPathAssumption {
            occurrence,
            condition,
            value,
            facts,
            ..
        } => {
            // Planning records the exact statement-entry point where the
            // branch decision was made. Keep that spelling here: alternatives
            // can replay without their common statement-step prefix, so a
            // transient "last step" pointer is not a reliable anchor.
            let condition = condition.clone();
            let surface_fact = if *value {
                condition.clone()
            } else {
                negate_click_proposition(&condition)
            };
            let lowered = lower_surface_candidate_at_point(
                replay,
                &surface_fact,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            );
            match lowered {
                Ok(kernel_fact)
                    if facts
                        .iter()
                        .any(|fact| path_condition_equivalent(fact, &kernel_fact)) =>
                {
                    let certified_fact = facts
                        .iter()
                        .find(|fact| path_condition_equivalent(fact, &kernel_fact))
                        .expect("the matching certified path fact was checked above");
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface_fact, certified_fact)
                    {
                        replay.surface_replay.block(format!(
                            "could not retain the certified path-condition spelling: {}",
                            error.message()
                        ));
                        return;
                    }
                }
                Ok(kernel_fact) => {
                    replay.surface_replay.block(format!(
                        "surface branch condition did not lower to a certified path fact\n  lowered: {kernel_fact:?}\n  certified facts: {facts:?}"
                    ));
                    return;
                }
                Err(error) => {
                    replay.surface_replay.block(format!(
                        "could not lower the certified path condition: {}",
                        error.message()
                    ));
                    return;
                }
            }
            replay.surface_replay.path_choices.push(SurfacePathChoice {
                occurrence: *occurrence,
                condition,
                value: *value,
                tactic_offset: replay.surface_replay.tactics.len(),
            });
        }
        ProofTactic::CertifiedAlternatives(_) => {}
        ProofTactic::Have(have) => {
            match TacticCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                Ok(_) => replay.surface_replay.push(tactic.clone()),
                Err(_)
                    if smart_simp_unfold_prefix(&have.proof).is_some()
                        || have_proof_contains_smart_apply(&have.proof) =>
                {
                    // The successful smart proof is lowered after it has
                    // produced its checked kernel fact.
                }
                Err(error) => replay
                    .surface_replay
                    .block(format!("could not lower control-flow tactic: {error:?}")),
            }
        }
        ProofTactic::ExactPropositionDerivation(derivation) => {
            match lower_surface_atomic_derivation(
                replay,
                derivation,
                None,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            ) {
                Ok((mut conclusion, mut proof)) => {
                    // Exact facts emitted immediately after a certified step
                    // describe that step's entry snapshot. An unqualified
                    // field spelling is evaluated again in the post-step
                    // state and can silently become a different proposition
                    // (for example `len < len + 1` after `len` changes).
                    // Preserve the snapshot in both the generated goal and
                    // every listed premise.
                    if let Some(point) = replay.surface_replay.last_step_entry.clone() {
                        let Ok(anchored) = surface_with_source_site(&conclusion, &point) else {
                            replay.surface_replay.block(
                                "could not anchor an exact derivation conclusion at its statement-entry snapshot",
                            );
                            return;
                        };
                        conclusion = anchored;
                        if let Proof::Script(tactics) = &mut proof {
                            for tactic in tactics {
                                if let ProofTactic::Derive(derive) = tactic {
                                    for premise in &mut derive.premises {
                                        let Ok(anchored) =
                                            surface_with_source_site(premise, &point)
                                        else {
                                            replay.surface_replay.block(
                                                "could not anchor an exact derivation premise at its statement-entry snapshot",
                                            );
                                            return;
                                        };
                                        *premise = anchored;
                                    }
                                }
                            }
                        }
                    }
                    replay.surface_replay.push(ProofTactic::Have(ProofHave {
                        proposition: conclusion,
                        proof,
                    }));
                }
                Err(error) => replay.surface_replay.block(format!(
                    "could not lower exact proposition derivation: {}",
                    error.message()
                )),
            }
        }
        ProofTactic::CertifiedFrame(path_derivations) => {
            let lowered = path_derivations
                .iter()
                .map(|derivations| {
                    check_verification_deadline()?;
                    let mut tactics = Vec::new();
                    let mut premises = Vec::new();
                    // A certified frame's derivation contexts are its exact
                    // dependency boundary. Surface-lowering every ambient
                    // snapshot here made expansion grow with unrelated proof
                    // history even though exact replay never consulted it.
                    for fact in derivations
                        .iter()
                        .flat_map(PropositionDerivation::context_premises)
                    {
                        check_verification_deadline()?;
                        if let Ok(surface) = checked_surface_fact_at_point(
                            replay,
                            &fact,
                            available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        ) && !premises.contains(&surface)
                        {
                            premises.push(surface);
                        }
                    }
                    for derivation in derivations {
                        check_verification_deadline()?;
                        let (mut conclusion, proof) = lower_surface_atomic_derivation(
                            replay,
                            derivation,
                            None,
                            available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        )?;
                        let memories = c_condition_fact_memories(derivation.conclusion());
                        // Prefer the stable function-entry selector when it
                        // names the certified snapshot. Statement-entry
                        // states are replay artifacts and a generated
                        // certificate must not depend on an ephemeral
                        // lowering map to reconstruct one of them.
                        let mut candidate_points = Vec::new();
                        if let Some(entry_state) = &replay.function_entry_state {
                            candidate_points.push((
                                ProgramPointRef {
                                    region: CodeRegionRef::Function,
                                    kind: ProgramPointKind::Entry,
                                },
                                entry_state.clone(),
                            ));
                        }
                        candidate_points.extend(
                            replay
                                .program_point_states
                                .iter()
                                .rev()
                                .map(|(point, state)| (point.clone(), state.clone())),
                        );
                        for (point, point_state) in candidate_points {
                            if memories.is_empty()
                                || !memories.iter().any(|memory| {
                                    memory.has_same_snapshot_markers(point_state.memory())
                                })
                            {
                                continue;
                            }
                            let Ok(candidate) = surface_with_source_site(&conclusion, &point)
                            else {
                                continue;
                            };
                            let lowered = lower_point_proposition(
                                &candidate,
                                available,
                                parameters,
                                arguments,
                                replay.old_reference_state(state),
                                state,
                                None,
                                &replay.program_point_states,
                                predicate_environment,
                                click_function_environment,
                            );
                            if lowered.as_ref().is_ok_and(|lowered| {
                                normalize_direct_atomic_memory_loads(lowered)
                                    == normalize_direct_atomic_memory_loads(derivation.conclusion())
                            }) {
                                conclusion = candidate;
                                break;
                            }
                        }
                        if !premises.contains(&conclusion) {
                            premises.push(conclusion.clone());
                            tactics.push(ProofTactic::Have(ProofHave {
                                proposition: conclusion,
                                proof,
                            }));
                        }
                    }
                    tactics.push(ProofTactic::FrameUsing {
                        region: None,
                        premises,
                    });
                    Ok::<_, ClickError>(tactics)
                })
                .collect::<Result<Vec<_>, _>>();
            match lowered {
                Ok(path_tactics) => {
                    if let Err(message) = append_surface_tactics_by_leaf(
                        &mut replay.surface_replay.tactics,
                        &path_tactics,
                    ) {
                        replay.surface_replay.block(message);
                    }
                }
                Err(error) => replay.surface_replay.block(format!(
                    "could not lower contextual frame certificate: {}",
                    error.message()
                )),
            }
        }
        // A frontier-local loop is lowered after its initialization,
        // preservation, and effect certificates have been checked. Recording
        // the source block here would either retain smart defaults or mark
        // the replay blocked before those certificates exist.
        ProofTactic::Loop(_) => {}
        _ => match tactic.class() {
            TacticClass::Simple(simple) if simple.is_surface_expressible() => {
                replay.surface_replay.push(tactic.clone())
            }
            TacticClass::ControlFlow(_) => {
                match TacticCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                    Ok(_) => replay.surface_replay.push(tactic.clone()),
                    Err(error) => replay
                        .surface_replay
                        .block(format!("could not lower control-flow tactic: {error:?}")),
                }
            }
            TacticClass::Smart(_) | TacticClass::Simple(_) => {}
        },
    }
}

fn statement_step_permission_needs_surface_premise(
    fact: &Proposition,
    projected_resource_facts: &[Proposition],
) -> bool {
    let separation_follows_from_fresh_heap_provenance = matches!(
        fact,
        Proposition::CResourceSeparate {
            left: CResource::Memory(left),
            right: CResource::Memory(right),
        } if left.base().block != right.base().block
            && (matches!(left.base().block, PointerBlock::Heap(_))
                || matches!(right.base().block, PointerBlock::Heap(_)))
    );
    matches!(
        fact,
        Proposition::CMemoryDisjoint { .. }
            | Proposition::CResourceSeparate { .. }
            | Proposition::CMemoryLoadable { .. }
    ) && !separation_follows_from_fresh_heap_provenance
        && !exact_fact_is_available(fact, projected_resource_facts)
}

fn have_proof_is_smart_simp(proof: &Proof) -> bool {
    match proof {
        Proof::Default | Proof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => true,
        Proof::Script(tactics) => matches!(tactics.as_slice(), [ProofTactic::Simp]),
        Proof::Tactic(SmartTactic::Frame) => false,
    }
}

fn smart_simp_unfold_prefix(proof: &Proof) -> Option<Vec<String>> {
    if have_proof_is_smart_simp(proof) {
        return Some(Vec::new());
    }
    let Proof::Script(tactics) = proof else {
        return None;
    };
    let (last, prefix) = tactics.split_last()?;
    if !matches!(last, ProofTactic::Simp) {
        return None;
    }
    prefix
        .iter()
        .map(|tactic| match tactic {
            ProofTactic::UnfoldPredicate(name) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

/// Replace the trailing smart `simp` of a post-execution `have` script whose
/// prefix is already certificate-expressible with a simple closer.
///
/// This covers the shapes the `[unfold*, simp]` lowering misses — notably a
/// `witness`/`choose` prefix, which is how an existential `have` is written.
/// The candidate script is accepted only when `prove_have_at_point` (the
/// replay judgment) proves it AND yields exactly the fact the smart script
/// established, so this emits only what replay accepts.
#[allow(clippy::too_many_arguments)]
fn lower_smart_simp_suffix_have(
    have: &ProofHave,
    fact: &Proposition,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_requires: &[Requirement],
    path_index: usize,
) -> Option<ProofHave> {
    let Proof::Script(tactics) = &have.proof else {
        return None;
    };
    let (last, prefix) = tactics.split_last()?;
    if !matches!(last, ProofTactic::Simp) {
        return None;
    }
    for closer in [ProofTactic::Assumption, ProofTactic::Normalize] {
        let mut candidate_tactics = prefix.to_vec();
        candidate_tactics.push(closer);
        let candidate = ProofHave {
            proposition: have.proposition.clone(),
            proof: Proof::Script(candidate_tactics),
        };
        if TacticCertificate::from_proof_tactics(std::slice::from_ref(&ProofTactic::Have(
            candidate.clone(),
        )))
        .is_err()
        {
            continue;
        }
        let replayed = prove_have_at_point(
            &candidate,
            theorem_environment,
            claim_label,
            tactic_index,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            Some(result),
            program_point_states,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            function_requires,
            Some(path_index),
        );
        if replayed.is_ok_and(|replayed| replayed == *fact) {
            return Some(candidate);
        }
    }
    None
}

fn have_proof_contains_smart_apply(proof: &Proof) -> bool {
    let Proof::Script(tactics) = proof else {
        return false;
    };
    tactics
        .iter()
        .any(|tactic| matches!(tactic, ProofTactic::ApplyTheorem(_)))
}

#[allow(clippy::too_many_arguments)]
fn surface_simp_plan_proof(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    surface_goal: &ClickProposition,
    plan: &ProofReplayPlan,
    unfolded_predicates: &[String],
) -> Result<Proof, ClickError> {
    let active_surface_goal = if unfolded_predicates.is_empty() {
        surface_goal.clone()
    } else {
        unfold_structural_invariant_proposition(
            predicate_environment,
            surface_goal,
            unfolded_predicates,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "could not express the smart proof goal after predicate unfolding: {message}"
            ))
        })?
    };
    let proof = match plan.tactics() {
        [ProofTactic::Assumption] => Proof::Script(vec![ProofTactic::Assumption]),
        [ProofTactic::Normalize] => Proof::Script(vec![ProofTactic::Normalize]),
        [ProofTactic::ExactPropositionDerivation(derivation)] => {
            let (_, proof) = lower_surface_atomic_derivation(
                replay,
                derivation,
                Some(&active_surface_goal),
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "could not lower the planned smart proof certificate: {}",
                    error.message()
                ))
            })?;
            proof
        }
        _ => {
            return Err(ClickError::new(
                "smart proof planned an unexpected simp certificate",
            ));
        }
    };
    if unfolded_predicates.is_empty() {
        return Ok(proof);
    }
    let mut tactics = unfolded_predicates
        .iter()
        .cloned()
        .map(ProofTactic::UnfoldPredicate)
        .collect::<Vec<_>>();
    let Proof::Script(suffix) = proof else {
        return Err(ClickError::new(
            "planned smart proof certificate was not a tactic script",
        ));
    };
    tactics.extend(suffix);
    Ok(Proof::Script(tactics))
}

#[allow(clippy::too_many_arguments)]
fn surface_smart_have_certificate(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    have: &ProofHave,
    plan: &ProofReplayPlan,
    unfolded_predicates: &[String],
) -> Result<TacticCertificate, ClickError> {
    let proof = surface_simp_plan_proof(
        replay,
        state,
        available,
        parameters,
        arguments,
        predicate_environment,
        click_function_environment,
        &have.proposition,
        plan,
        unfolded_predicates,
    )?;
    let tactic = ProofTactic::Have(ProofHave {
        proposition: have.proposition.clone(),
        proof,
    });
    TacticCertificate::from_proof_tactics(&[tactic]).map_err(|error| {
        ClickError::new(format!(
            "smart `have` produced an invalid certificate: {error:?}"
        ))
    })
}

#[allow(clippy::too_many_arguments)]
fn surface_smart_have_derivation_certificate(
    replay: &TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    have: &ProofHave,
) -> Option<TacticCertificate> {
    let mut premises = Vec::new();
    for fact in available {
        let relevant = matches!(fact, Proposition::CMemoryLoadable { .. })
            || matches!(
                fact,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(_, _)
                        | ConditionTerm::Bitvector32SignedLessEqual(_, _)
                        | ConditionTerm::Bitvector32SignedGreaterThan(_, _)
                        | ConditionTerm::Bitvector32SignedGreaterEqual(_, _),
                    _,
                )
            );
        if !relevant {
            continue;
        }
        let Ok(surface) = checked_surface_fact_at_point(
            replay,
            fact,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        ) else {
            continue;
        };
        if !premises.contains(&surface) {
            premises.push(surface);
        }
    }
    if premises.is_empty() {
        return None;
    }
    TacticCertificate::from_proof_tactics(&[ProofTactic::Have(ProofHave {
        proposition: have.proposition.clone(),
        proof: Proof::Script(vec![ProofTactic::Derive(ProofDerive { premises })]),
    })])
    .ok()
}

#[allow(clippy::too_many_arguments)]
fn surface_outcome_smart_have_derivation(
    replay: &TacticReplayState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    have: &ProofHave,
    unfolded_predicates: &[String],
) -> Option<ProofHave> {
    let mut atomic_available = Vec::new();
    for fact in available {
        atomic_conjuncts(fact, &mut atomic_available);
    }
    let mut premises = Vec::new();
    for fact in atomic_available {
        let relevant = matches!(fact, Proposition::CMemoryLoadable { .. })
            || match fact {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(left, right)
                    | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                    | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                    | ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
                    _,
                ) => [left.as_const(), right.as_const()]
                    .into_iter()
                    .flatten()
                    .all(|constant| constant == 0),
                _ => false,
            };
        if !relevant {
            continue;
        }
        let Ok(surface) = checked_surface_fact_at_outcome(
            replay,
            fact,
            SurfaceFactMatch::CanonicalExact,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        ) else {
            continue;
        };
        if !premises.contains(&surface) {
            premises.push(surface);
        }
    }
    (!premises.is_empty()).then(|| {
        let mut tactics = unfolded_predicates
            .iter()
            .cloned()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.push(ProofTactic::Derive(ProofDerive { premises }));
        ProofHave {
            proposition: have.proposition.clone(),
            proof: Proof::Script(tactics),
        }
    })
}

#[allow(clippy::too_many_arguments)]
fn surface_smart_apply_have_certificate(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    tactic_index: usize,
    have: &ProofHave,
    goal: &Proposition,
) -> Result<Option<TacticCertificate>, ClickError> {
    if !have_proof_contains_smart_apply(&have.proof) {
        return Ok(None);
    }
    let Proof::Script(tactics) = &have.proof else {
        unreachable!("smart apply is represented by a proof script")
    };
    let mut planning_replay = replay.clone();
    let mut planning_available = available.to_vec();
    let mut surface_tactics = Vec::with_capacity(tactics.len());
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(name) => {
                planning_available = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &planning_available,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not plan smart `apply` after `unfold`: {message}"
                    ))
                })?;
                if !planning_replay.unfolded_predicates.contains(name) {
                    planning_replay.unfolded_predicates.push(name.clone());
                }
                surface_tactics.push(tactic.clone());
            }
            ProofTactic::ApplyTheorem(application) => {
                let premises = plan_explicit_theorem_application(
                    theorem_environment,
                    application,
                    claim_label,
                    tactic_index,
                    &planning_available,
                    parameters,
                    arguments,
                    &planning_replay,
                    state,
                    predicate_environment,
                    click_function_environment,
                )?;
                planning_available = apply_theorem_at_current_point(
                    theorem_environment,
                    application,
                    claim_label,
                    tactic_index,
                    planning_available,
                    parameters,
                    arguments,
                    planning_replay.old_reference_state(state),
                    state,
                    &planning_replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                    &planning_replay.unfolded_predicates,
                    None,
                )?;
                surface_tactics.push(ProofTactic::ApplyTheoremUsing {
                    application: application.clone(),
                    premises,
                });
            }
            ProofTactic::Simp => {
                let assumptions = assumptions_from_propositions(&planning_available);
                let plan = plan_simp_certificate(goal, &assumptions).ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not plan the `simp` suffix after smart `apply`"
                    ))
                })?;
                let Proof::Script(lowered) = surface_simp_plan_proof(
                    &mut planning_replay,
                    state,
                    &planning_available,
                    parameters,
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    &have.proposition,
                    &plan,
                    &[],
                )?
                else {
                    unreachable!("surface simp lowering always returns a script")
                };
                surface_tactics.extend(lowered);
            }
            _ => surface_tactics.push(tactic.clone()),
        }
    }
    let tactic = ProofTactic::Have(ProofHave {
        proposition: have.proposition.clone(),
        proof: Proof::Script(surface_tactics),
    });
    let certificate = TacticCertificate::from_proof_tactics(&[tactic]).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart `apply` inside `have` produced an invalid certificate: {error:?}"
        ))
    })?;
    Ok(Some(certificate))
}

/// Track, in the certificate-generation fact set, the facts a recorded
/// post-execution surface tactic just added to the drain's requirements.
///
/// `surface_certificate_facts` is snapshotted before the drain runs, but
/// the certificate a claim ends up with is `[recorded post tactics ...,
/// closer tactics ...]`. Facts produced by replaying a recorded tactic are
/// therefore in scope when the closer replays; withholding them from
/// generation only makes generation plan against strictly less than the
/// replay judgment accepts.
fn record_certificate_facts_from_replay(
    before: &[Proposition],
    after: &[Proposition],
    surface_certificate_facts: &mut Vec<Proposition>,
) {
    for fact in after {
        if !before.contains(fact) && !surface_certificate_facts.contains(fact) {
            surface_certificate_facts.push(fact.clone());
        }
    }
}

fn tactic_is_deferred_post_execution(tactic: &ProofTactic) -> bool {
    matches!(
        tactic,
        ProofTactic::FoldResource(_)
            | ProofTactic::UnfoldPredicate(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Have(_)
            | ProofTactic::Transport { .. }
            | ProofTactic::TransportUsing { .. }
            | ProofTactic::Witness(_)
            | ProofTactic::Choose(_)
            | ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Rewrite(_)
            | ProofTactic::Simp
            | ProofTactic::FrameUsing {
                region: None | Some(CodeRegionRef::Function),
                ..
            }
    )
}

struct TacticTiming {
    claim_label: String,
    tactic_index: usize,
    source_index: usize,
    tactic_name: String,
    tactic_class: &'static str,
    statement_index: usize,
    start: std::time::Instant,
    context: TimingTacticContext,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceTacticClass {
    Simple,
    Smart,
    Control,
}

impl SourceTacticClass {
    fn label(self) -> &'static str {
        match self {
            Self::Simple => "simple",
            Self::Smart => "smart",
            Self::Control => "control",
        }
    }
}

pub(super) fn source_tactic_class(tactic: &ProofTactic) -> SourceTacticClass {
    if let ProofTactic::Have(have) = tactic {
        if smart_simp_unfold_prefix(&have.proof).is_some() {
            return SourceTacticClass::Smart;
        }
        if let Proof::Script(tactics) = &have.proof
            && !tactics.is_empty()
            && tactics
                .iter()
                .all(|tactic| matches!(tactic.class(), TacticClass::Simple(_)))
        {
            return SourceTacticClass::Simple;
        }
    }
    if let ProofTactic::Loop(loop_clause) = tactic
        && (loop_clause.initialize_proof().is_none()
            || loop_clause.preserve_proof().is_none()
            || loop_clause
                .items()
                .iter()
                .any(|item| item.is_effect_kind() && matches!(item.proof(), Proof::Default)))
    {
        // The loop keyword is the shared source anchor for every omitted
        // phase/effect proof in this block. Expanding it materializes all of
        // those defaults together.
        return SourceTacticClass::Smart;
    }
    match tactic.class() {
        TacticClass::Simple(_) => SourceTacticClass::Simple,
        TacticClass::Smart(_) => SourceTacticClass::Smart,
        TacticClass::ControlFlow(_) => SourceTacticClass::Control,
    }
}

fn has_independent_source_timing(tactic: &ProofTactic) -> bool {
    // `CertifiedAlternatives` is the internal branching plan produced by a
    // smart `execute`. It has no surface spelling or source site of its own:
    // replaying and lowering it is part of the owning smart tactic. Starting
    // a nested control timer here would hide the expensive part of `execute`
    // from `click profile` and subject `click expand` to the control budget.
    !matches!(tactic, ProofTactic::CertifiedAlternatives(_))
}

impl TacticTiming {
    fn new(
        claim_label: &str,
        tactic_index: usize,
        source_index: usize,
        tactic: &ProofTactic,
        statement_index: usize,
    ) -> Option<Self> {
        Self::named_for_tactic(
            claim_label,
            tactic_name(tactic),
            tactic,
            tactic_index,
            source_index,
            statement_index,
        )
    }

    /// Times work that is not itself a surface tactic replay — a planner
    /// searching for a certificate, or a kernel re-derivation that a replayed
    /// tactic defers to its caller — under an explicit `name`, taking the
    /// class from the tactic the work belongs to rather than inventing one.
    fn named_for_tactic(
        claim_label: &str,
        name: &str,
        tactic: &ProofTactic,
        tactic_index: usize,
        source_index: usize,
        statement_index: usize,
    ) -> Option<Self> {
        if source_index == usize::MAX {
            return None;
        }
        crate::instrumentation::enabled().then(|| {
            let tactic_class = source_tactic_class(tactic).label();
            if crate::instrumentation::starts_enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(
                        crate::instrumentation::TacticEvent {
                            claim: claim_label.to_string(),
                            tactic_index,
                            tactic_name: name.to_string(),
                            class: tactic_class.to_string(),
                            statement_index,
                            source_index,
                        },
                    ),
                );
            }
            let context = TimingTacticContext {
                claim_label: claim_label.to_string(),
                tactic_index,
                tactic_name: name.to_string(),
                tactic_class: tactic_class.to_string(),
                statement_index,
                source_index,
            };
            push_timing_tactic(context.clone());
            Self {
                claim_label: claim_label.to_string(),
                tactic_index,
                source_index,
                tactic_name: name.to_string(),
                tactic_class,
                statement_index,
                start: std::time::Instant::now(),
                context,
            }
        })
    }
}

impl Drop for TacticTiming {
    fn drop(&mut self) {
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFinished {
            tactic: crate::instrumentation::TacticEvent {
                claim: self.claim_label.clone(),
                tactic_index: self.tactic_index,
                tactic_name: self.tactic_name.clone(),
                class: self.tactic_class.to_string(),
                statement_index: self.statement_index,
                source_index: self.source_index,
            },
            elapsed: self.start.elapsed(),
        });
        pop_timing_tactic(&self.context);
    }
}

#[allow(clippy::too_many_arguments)]
fn execute_frontier_local_loop(
    loop_template: &StructuralClause,
    replay: &mut TacticReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    source_index: usize,
) -> Result<(), ClickError> {
    if replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop, but execution has reached function exit"
        )));
    }
    let statement_index = replay.frontier.next_statement_index;
    let source_region = replay.source_layout.statement(statement_index).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` could not resolve source statement({statement_index})"
        ))
    })?;
    let SourceStatementKind::Loop { loop_index } = source_region.kind else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `loop` requires the execution frontier to be at a loop; current frontier is statement({statement_index})"
        )));
    };
    if replay
        .frontier_loop_clauses
        .iter()
        .any(|clause| clause.region() == &CodeRegion::Loop(loop_index))
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: loop({loop_index}) already has a frontier-local proof on this execution path"
        )));
    }
    let function_with_prior_loops =
        function_block.with_bound_frontier_loop_clauses(&replay.frontier_loop_clauses);
    let bound_function_block =
        function_with_prior_loops.with_frontier_loop_clause(loop_template, loop_index);
    validate_region_proof_clauses(&bound_function_block, parsed_function)?;

    let initial_state = replay.execution_start_state(state).clone();
    let annotated = annotated_function(
        &bound_function_block,
        parsed_function,
        &initial_state,
        arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        false,
    )?;
    if replay.is_at_function_entry() {
        let entry_state = c_function_entry_state(&initial_state, &annotated, arguments)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `loop` could not bind function arguments"
                ))
            })?;
        replay.frontier.execution_start_state = Some(initial_state.clone());
        replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: annotated.body().clone(),
        };
        *state = entry_state;
    }
    let mut found_loop_index = 0;
    let current_loop = kernel_loop_by_index(annotated.body(), loop_index, &mut found_loop_index)
        .cloned()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `loop` could not lower loop({loop_index}) at statement({statement_index})"
            ))
        })?;

    let source_layout = SourceExecutionLayout::new(parsed_function.body());
    let loop_certificates = std::cell::RefCell::new(LoopProofCertificates::default());
    let loop_source = FrontierLoopProofSource::new(
        loop_template,
        replay.proof_site.clone(),
        claim_label,
        source_index,
    );
    let proof_environment = ExecutionProofEnvironment {
        initial_state: &initial_state,
        function_block: &bound_function_block,
        parsed_function,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function: &annotated,
        arguments,
        surface_propositions: &replay.surface_propositions,
        source_layout: &source_layout,
        frontier_loop_certificates: Some(&loop_certificates),
        frontier_loop_source: Some(&loop_source),
    };
    let case_path = replay
        .case_assumptions
        .iter()
        .map(|choice| ProofCaseChoice {
            condition: choice.condition.clone(),
            value: choice.value,
        })
        .collect();
    let mut verified_loop_rules = Vec::new();
    let mut next_statement_index = statement_index;
    let mut next_loop_index = loop_index;
    // `unfold` retains the opaque predicate atom alongside its definition so
    // later surface tactics can still refer to either spelling.  A verified
    // loop rule must not turn that proof-context convenience into an ambient
    // kernel prerequisite: exact contract certification exposes the fully
    // unfolded definition.  Keep every other fact, including the expanded
    // proposition, and omit only predicate atoms whose names have explicitly
    // been unfolded on this path.
    let loop_pure_facts = available_pure_facts
        .iter()
        .filter(|fact| {
            !matches!(
                fact,
                Proposition::Predicate { name, .. }
                    if replay.unfolded_predicates.contains(name)
            )
        })
        .cloned()
        .collect();
    let _exit_contexts = verify_execution_proofs_forward(
        &current_loop,
        vec![ExecutionProofContext {
            state: state.clone(),
            pure_facts: loop_pure_facts,
            surface_propositions: replay.surface_propositions.clone(),
            program_point_states: replay.program_point_states.clone(),
            case_path,
            next_opaque_call: replay.next_opaque_call,
            next_verification_variable: replay.next_verification_variable,
        }],
        &mut next_statement_index,
        &mut next_loop_index,
        &proof_environment,
        &mut verified_loop_rules,
    )?;
    let loop_rule = verified_loop_rules
        .pop()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `loop` did not construct a verified rule for loop({loop_index})"
            ))
        })?
        .with_composite_resource_definitions(
            annotated.composite_resource_definitions().iter().cloned(),
        );
    let loop_exit_condition = match &current_loop {
        CStatement::While { condition, .. } => Some(ClickProposition::Not(Box::new(
            surface_c_condition(condition),
        ))),
        _ => None,
    };
    let certificates = loop_certificates.borrow().clone();
    let mut expanded_loop = loop_template.clone();
    expanded_loop.initialize_proof = Some(Proof::Script(
        certificates
            .initialize
            .as_ref()
            .map(|certificate| certificate.tactics().to_vec())
            .unwrap_or_else(|| vec![ProofTactic::Assumption]),
    ));
    expanded_loop.preserve_proof = Some(Proof::Script(
        certificates
            .preserve
            .as_ref()
            .map(|certificate| certificate.tactics().to_vec())
            .unwrap_or_else(|| vec![ProofTactic::Assumption]),
    ));
    for (item_index, item) in expanded_loop.items.iter_mut().enumerate() {
        if !item.is_effect_kind() {
            continue;
        }
        if let Some(certificate) = certificates.effects.get(&item_index) {
            item.proof = Proof::Script(certificate.tactics().to_vec());
        }
    }
    let local_function_environment = function_environment.clone().with_verified_loop_rules(
        replay
            .frontier_loop_rules
            .iter()
            .cloned()
            .chain(std::iter::once(loop_rule.clone())),
    );

    if let ProofExecutionPoint::StatementEntry { remaining } = &replay.frontier.point {
        let (_, tail) = split_next_source_operation(remaining).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `loop` could not isolate the current source loop: {message}"
                ))
            })?;
        let mut statements = Vec::new();
        statements.push(current_loop);
        if let Some(tail) = tail {
            flatten_top_level_sequence(&tail, &mut statements).map_err(ClickError::new)?;
        }
        replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: sequence_from_statements(&statements)
                .expect("the current loop always contributes one statement"),
        };
    }

    let assumptions = assumptions_from_propositions(available_pure_facts);
    execute_step_from_execution_point(
        replay,
        state,
        available_pure_facts,
        &bound_function_block,
        &annotated,
        parsed_function.parameters(),
        arguments,
        &assumptions,
        &local_function_environment,
        claim_label,
        tactic_index,
        "loop",
        &[],
        None,
        StatementPrerequisitePolicy::Exact,
        StatementFactTransportPolicy::Automatic,
        LoopStepPolicy::ApplyVerifiedRule,
    )?;
    if let Some(exit_condition) = loop_exit_condition {
        let exit_point = ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Exit,
        };
        let lowered_exit_condition = lower_point_proposition(
            &exit_condition,
            available_pure_facts,
            parsed_function.parameters(),
            arguments,
            &initial_state,
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower loop({loop_index}) exit condition provenance: {message}"
            ))
        })?;
        if available_pure_facts.contains(&lowered_exit_condition) {
            let exit_surface = surface_with_source_site(&exit_condition, &exit_point)?;
            replay
                .surface_propositions
                .record_lowering(&exit_surface, &lowered_exit_condition)?;
        }
    }
    replay
        .frontier_loop_clauses
        .push(loop_template.bound_to_loop(loop_index));
    replay.frontier_loop_rules.push(loop_rule);
    replay.surface_replay.push(ProofTactic::Loop(expanded_loop));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn replay_linear_tactics(
    mut context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactics: &[IndexedTactic],
) -> Result<ProofReplayContext, ClickError> {
    let mut chunk_start = 0;
    for (index, indexed_tactic) in tactics.iter().enumerate() {
        let ProofTactic::Loop(loop_clause) = &indexed_tactic.tactic else {
            continue;
        };
        context = replay_linear_tactics_without_frontier_loops(
            context,
            function_block,
            parsed_function,
            claims,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            function,
            arguments,
            &tactics[chunk_start..index],
        )?;
        context = replay_frontier_local_loop_tactic(
            context,
            loop_clause,
            indexed_tactic.index,
            indexed_tactic.source_index,
            function_block,
            parsed_function,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            arguments,
        )?;
        chunk_start = index + 1;
    }
    replay_linear_tactics_without_frontier_loops(
        context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        &tactics[chunk_start..],
    )
}

#[allow(clippy::too_many_arguments)]
fn replay_frontier_local_loop_tactic(
    context: ProofReplayContext,
    loop_clause: &StructuralClause,
    tactic_index: usize,
    source_index: usize,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    arguments: &[CExpression],
) -> Result<ProofReplayContext, ClickError> {
    if crate::instrumentation::deadline_exceeded() {
        return Err(ClickError::new(format!(
            "tactic time limit exceeded: {}",
            crate::instrumentation::deadline_context()
        )));
    }
    let ProofReplayContext {
        mut state,
        pure_facts: mut available_pure_facts,
        mut replay,
        branch_path,
    } = context;
    let capture_this_tactic = begin_tactic_expansion_capture(
        source_index,
        &ProofTactic::Loop(loop_clause.clone()),
        &mut replay,
    )
    .is_some();
    let _timing = TacticTiming::new(
        claim_label,
        tactic_index,
        source_index,
        &ProofTactic::Loop(loop_clause.clone()),
        replay.frontier.next_statement_index,
    );
    execute_frontier_local_loop(
        loop_clause,
        &mut replay,
        &mut state,
        &mut available_pure_facts,
        function_block,
        parsed_function,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        arguments,
        claim_label,
        tactic_index,
        source_index,
    )?;
    if capture_this_tactic {
        return Err(finish_tactic_expansion_capture(
            &replay.surface_replay,
            false,
        ));
    }
    Ok(ProofReplayContext {
        state,
        pure_facts: available_pure_facts,
        replay,
        branch_path,
    })
}

#[allow(clippy::too_many_arguments)]
fn replay_linear_tactics_without_frontier_loops(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactics: &[IndexedTactic],
) -> Result<ProofReplayContext, ClickError> {
    let ProofReplayContext {
        mut state,
        pure_facts: mut requirement_pure_facts,
        mut replay,
        mut branch_path,
    } = context;
    let mut assumptions = assumptions_from_propositions(&requirement_pure_facts);

    for indexed_tactic in tactics {
        if crate::instrumentation::deadline_exceeded() {
            return Err(ClickError::new(format!(
                "tactic time limit exceeded: {}",
                crate::instrumentation::deadline_context()
            )));
        }
        let tactic_index = indexed_tactic.index;
        let source_index = indexed_tactic.source_index;
        let tactic = &indexed_tactic.tactic;
        let deferred_post_execution = replay.ordered_finalization
            && replay.is_at_function_exit()
            && tactic_is_deferred_post_execution(tactic);
        let deferred_region_simp = replay.region_proof && matches!(tactic, ProofTactic::Simp);
        let pre_capture_branch_skeleton =
            begin_tactic_expansion_capture(source_index, tactic, &mut replay);
        let capture_this_tactic = pre_capture_branch_skeleton.is_some();
        if let Some(branch_skeleton) = pre_capture_branch_skeleton
            && deferred_post_execution
        {
            replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                source_index,
                post_execution_index: replay.post_execution_tactics.len(),
                branch_skeleton,
            });
        }
        if !deferred_post_execution {
            record_surface_replay_tactic(
                &mut replay,
                &state,
                &requirement_pure_facts,
                function_block,
                parsed_function.parameters(),
                arguments,
                predicate_environment,
                click_function_environment,
                tactic,
                None,
            );
        }
        let _timing = (!(deferred_post_execution
            || replay.region_proof && matches!(tactic, ProofTactic::Simp))
            && has_independent_source_timing(tactic))
        .then(|| {
            TacticTiming::new(
                claim_label,
                tactic_index,
                source_index,
                tactic,
                replay.frontier.next_statement_index,
            )
        })
        .flatten();
        if let ProofTactic::Transport {
            source: surface_source,
            target: surface_target,
        } = tactic
            && !replay.is_at_function_exit()
        {
            if replay.is_at_function_entry() || replay.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one execution step"
                )));
            }
            let pre_state = replay.old_reference_state(&state);
            let source = lower_point_proposition(
                surface_source,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                pre_state,
                &state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                ))
            })?;
            if assumptions.derive_proposition(&source).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                    describe_missing_pure_fact(
                        &source,
                        &requirement_pure_facts,
                        state.resources().facts(),
                        parsed_function.parameters(),
                        arguments,
                        &replay.effect_facts,
                    )
                )));
            }
            let target = lower_point_proposition(
                surface_target,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                pre_state,
                &state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts = fact_transport_transition_facts(&replay.effect_facts, &source);
            let premises = plan_explicit_fact_transport(
                surface_source,
                &source,
                &target,
                &requirement_pure_facts,
                &transition_facts,
                parsed_function.parameters(),
                arguments,
                &replay,
                &state,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: {}",
                    fact_transport_planning_failure(
                        surface_source,
                        surface_target,
                        &replay.unfolded_predicates,
                        &error,
                    )
                ))
            })?;
            let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::TransportUsing {
                source: surface_source.clone(),
                target: surface_target.clone(),
                premises,
            }])
            .expect("explicit fact transport is a simple tactic");
            let result = replay_smart_plan(
                ProofReplayContext {
                    state,
                    pure_facts: requirement_pure_facts,
                    replay,
                    branch_path,
                },
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
                tactic_index,
                source_index,
                &plan,
            )?;
            state = result.state;
            requirement_pure_facts = result.pure_facts;
            replay = result.replay;
            branch_path = result.branch_path;
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            if capture_this_tactic {
                return Err(finish_tactic_expansion_capture(
                    &replay.surface_replay,
                    false,
                ));
            }
            continue;
        }
        if let ProofTactic::ApplyTheorem(application) = tactic
            && !replay.is_at_function_exit()
        {
            if theorem_environment.get(&application.name).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                    application.name
                )));
            }
            let premises = plan_explicit_theorem_application(
                theorem_environment,
                application,
                claim_label,
                tactic_index,
                &requirement_pure_facts,
                parsed_function.parameters(),
                arguments,
                &replay,
                &state,
                predicate_environment,
                click_function_environment,
            )?;
            let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::ApplyTheoremUsing {
                application: application.clone(),
                premises,
            }])
            .expect("explicit theorem application is a simple tactic");
            let result = replay_smart_plan(
                ProofReplayContext {
                    state,
                    pure_facts: requirement_pure_facts,
                    replay,
                    branch_path,
                },
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
                tactic_index,
                source_index,
                &plan,
            )?;
            state = result.state;
            requirement_pure_facts = result.pure_facts;
            replay = result.replay;
            branch_path = result.branch_path;
            assumptions = assumptions_from_propositions(&requirement_pure_facts);
            if capture_this_tactic {
                return Err(finish_tactic_expansion_capture(
                    &replay.surface_replay,
                    false,
                ));
            }
            continue;
        }
        match tactic {
            ProofTactic::Mark(name) => {
                let point = ProgramPointRef {
                    region: CodeRegionRef::Mark(name.clone()),
                    kind: ProgramPointKind::Entry,
                };
                if replay.program_point_states.contains_key(&point) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: duplicate proof mark `{name}`"
                    )));
                }
                replay.program_point_states.insert(point, state.clone());
            }
            ProofTactic::UnfoldResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold` must run before execution reaches function exit"
                    )));
                }
                state = unfold_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    arguments,
                    state,
                    &mut requirement_pure_facts,
                    &mut replay.surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    tactic_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ObserveResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `observe` must run before execution reaches function exit"
                    )));
                }
                state = observe_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    arguments,
                    state,
                    &mut requirement_pure_facts,
                    &mut replay.surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    tactic_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Transport {
                source: surface_source,
                target: surface_target,
            }
            | ProofTactic::TransportUsing {
                source: surface_source,
                target: surface_target,
                ..
            } => {
                if replay.is_at_function_exit() {
                    let premises = match tactic {
                        ProofTactic::TransportUsing { premises, .. } => Some(premises.clone()),
                        ProofTactic::Transport { .. } => None,
                        _ => unreachable!(),
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Transport {
                            source: surface_source.clone(),
                            target: surface_target.clone(),
                            premises,
                        },
                    );
                    continue;
                }
                if replay.is_at_function_entry() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport` requires at least one completed execution step"
                    )));
                }
                let pre_state = replay.old_reference_state(&state).clone();
                let surface_premises = match tactic {
                    ProofTactic::TransportUsing { premises, .. } => Some(premises),
                    ProofTactic::Transport { .. } => None,
                    _ => unreachable!(),
                };
                let mut explicit_premises = Vec::new();
                if let Some(surface_premises) = surface_premises {
                    for surface_premise in surface_premises {
                        let premise = if let Some(recorded) = replay
                            .surface_propositions
                            .available_kernel(surface_premise, &requirement_pure_facts)
                        {
                            recorded.clone()
                        } else {
                            lower_point_proposition(
                                surface_premise,
                                &requirement_pure_facts,
                                parsed_function.parameters(),
                                arguments,
                                &pre_state,
                                &state,
                                None,
                                &replay.program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` tactic {tactic_index}: could not lower `transport using` premise: {message}"
                                ))
                            })?
                        };
                        if !exact_fact_is_available(&premise, &requirement_pure_facts) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `transport using` requires an exact premise: {}",
                                describe_missing_pure_fact(
                                    &premise,
                                    &requirement_pure_facts,
                                    state.resources().facts(),
                                    parsed_function.parameters(),
                                    arguments,
                                    &replay.effect_facts,
                                )
                            )));
                        }
                        if !explicit_premises.contains(&premise) {
                            explicit_premises.push(premise);
                        }
                    }
                }
                // Lowering memory expressions uses the already-validated
                // ambient resource/loadability context. The proof search
                // below is still restricted to explicit premises plus
                // certified frame context.
                let lowering_facts = requirement_pure_facts.as_slice();
                let mut direct_lowering_facts =
                    facts_for_direct_surface_lowering(&requirement_pure_facts);
                for premise in &explicit_premises {
                    if !direct_lowering_facts.contains(premise) {
                        direct_lowering_facts.push(premise.clone());
                    }
                }
                let source = if let Some(recorded) = replay
                    .surface_propositions
                    .available_kernel(surface_source, &requirement_pure_facts)
                {
                    recorded.clone()
                } else {
                    lower_point_proposition(
                        surface_source,
                        lowering_facts,
                        parsed_function.parameters(),
                        arguments,
                        &pre_state,
                        &state,
                        None,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                        ))
                    })?
                };
                replay
                    .surface_propositions
                    .record_lowering(surface_source, &source)?;
                let selected_assumptions = if surface_premises.is_some() {
                    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                    let resource_facts = state
                        .resources()
                        .observable_facts_assuming_valid(&explicit_assumptions);
                    requirement_pure_facts
                        .iter()
                        .filter(|fact| is_implicit_fact_transport_context(fact))
                        .cloned()
                        .chain(resource_facts)
                        .fold(explicit_assumptions, |assumptions, fact| {
                            assumptions.assume_proposition(fact)
                        })
                } else {
                    assumptions.clone()
                };
                // A transport source spelled at a later program point than
                // its listed fact is the same fact when the kernel proves the
                // snapshots agree at the loaded pointers. Candidates still
                // come only from the explicit premises, so the transport must
                // still list the fact; the recorded effects and the selected
                // assumptions only supply the frame evidence.
                if !exact_fact_is_available(&source, &explicit_premises)
                    && !snapshot_bridged_fact_is_available_under(
                        &source,
                        &explicit_premises,
                        &selected_assumptions,
                        &replay.effect_facts,
                    )
                    && selected_assumptions
                        .derive_atomic_proposition(&source)
                        .is_none()
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `transport{}` requires a source derivable from its {}facts: {}",
                        if surface_premises.is_some() {
                            " using"
                        } else {
                            ""
                        },
                        if surface_premises.is_some() {
                            "explicit "
                        } else {
                            "ambient "
                        },
                        describe_missing_pure_fact(
                            &source,
                            &requirement_pure_facts,
                            state.resources().facts(),
                            parsed_function.parameters(),
                            arguments,
                            &replay.effect_facts,
                        )
                    )));
                }
                let target = lower_point_proposition(
                    surface_target,
                    &direct_lowering_facts,
                    parsed_function.parameters(),
                    arguments,
                    &pre_state,
                    &state,
                    None,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                    ))
                })?;
                replay
                    .surface_propositions
                    .record_lowering(surface_target, &target)?;
                // The target can already be present under a different snapshot
                // spelling; candidates come from the ambient facts, so the
                // bridge only re-spells a fact that is genuinely available.
                if exact_fact_is_available_across_effects(
                    &target,
                    &requirement_pure_facts,
                    &replay.effect_facts,
                ) || materialization_equivalent_available_fact(&target, &requirement_pure_facts)
                    .is_some()
                {
                    if !requirement_pure_facts.contains(&target) {
                        requirement_pure_facts.push(target.clone());
                        assumptions = assumptions.assume_proposition(target);
                    }
                    continue;
                }
                let transition_facts =
                    fact_transport_transition_facts(&replay.effect_facts, &source);
                if surface_premises.is_none() {
                    match plan_explicit_fact_transport(
                        surface_source,
                        &source,
                        &target,
                        &requirement_pure_facts,
                        &transition_facts,
                        parsed_function.parameters(),
                        arguments,
                        &replay,
                        &state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            replay.surface_replay.push(ProofTactic::TransportUsing {
                                source: surface_source.clone(),
                                target: surface_target.clone(),
                                premises,
                            });
                        }
                        Err(error) => replay.surface_replay.block(fact_transport_planning_failure(
                            surface_source,
                            surface_target,
                            &replay.unfolded_predicates,
                            &error,
                        )),
                    }
                }
                let transport_assumptions = transition_facts
                    .iter()
                    .fold(selected_assumptions, |assumptions, fact| {
                        assumptions.assume_proposition(fact.proposition().clone())
                    })
                    .assume_proposition(source.clone());
                if !certified_fact_transport_reaches_through(
                    &source,
                    &target,
                    state.memory(),
                    &transport_assumptions,
                    &transition_facts,
                ) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: no certified frame transport applies to the exact source fact\n  source: {source:?}\n  current memory: {:?}\n  effect facts: {:?}",
                        state.memory(),
                        replay.effect_facts
                    )));
                }
                if !requirement_pure_facts.contains(&target) {
                    requirement_pure_facts.push(target.clone());
                    assumptions = assumptions.assume_proposition(target);
                }
            }
            ProofTactic::StepUsing(premises) => {
                let all_pure_facts = requirement_pure_facts.clone();
                let tactic_name = "step() using";
                let prerequisite_policy = StatementPrerequisitePolicy::Explicit;
                let loop_step_policy = LoopStepPolicy::EnterBody;
                let pre_state = replay.old_reference_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let recorded = replay
                        .surface_propositions
                        .available_kernel(surface_premise, &all_pure_facts);
                    let recorded_is_constant_truth =
                        recorded.is_some_and(|premise| match premise {
                            Proposition::ConditionIs(ConditionTerm::Constant(true), true) => true,
                            Proposition::ConditionIs(
                                ConditionTerm::Bitvector32SignedLessThan(left, right)
                                | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                                | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                                | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                                | ConditionTerm::Bitvector32Equal(left, right),
                                true,
                            ) => matches!(
                                (left.as_ref(), right.as_ref()),
                                (Bitvector32Term::Constant(_), Bitvector32Term::Constant(_))
                            ),
                            _ => false,
                        });
                    let lower_at_current = || {
                        lower_point_proposition(
                            surface_premise,
                            &all_pure_facts,
                            parsed_function.parameters(),
                            arguments,
                            &pre_state,
                            &state,
                            None,
                            &replay.program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                    };
                    let premise = if recorded_is_constant_truth {
                        match lower_at_current() {
                            Ok(current)
                                if !Assumptions::new().proves(&current)
                                    && (exact_fact_is_available_across_effects(
                                        &current,
                                        &all_pure_facts,
                                        &replay.effect_facts,
                                    ) || materialization_equivalent_available_fact(
                                        &current,
                                        &all_pure_facts,
                                    )
                                    .is_some()) =>
                            {
                                current
                            }
                            _ => recorded.expect("checked recorded truth").clone(),
                        }
                    } else if let Some(recorded) = recorded {
                        recorded.clone()
                    } else {
                        lower_at_current().map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower `{tactic_name}` premise `{}`: {message}",
                                super::printing::source_click_proposition(surface_premise)
                            ))
                        })?
                    };
                    replay
                        .surface_propositions
                        .record_lowering(surface_premise, &premise)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise: {}",
                                error.message()
                            ))
                        })?;
                    let entry_point = ProgramPointRef {
                        region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                        kind: ProgramPointKind::Entry,
                    };
                    let source_surface = surface_with_source_site(surface_premise, &entry_point)?;
                    replay
                        .surface_propositions
                        .record_lowering(&source_surface, &premise)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise source site: {}",
                                error.message()
                            ))
                        })?;
                    // Loadability premises additionally transport across
                    // snapshot spellings and recorded effects: the recorded
                    // fact and the premise print identically but embed
                    // different memory snapshots.
                    let premise_is_available =
                        exact_fact_is_available_across_effects(
                            &premise,
                            &all_pure_facts,
                            &replay.effect_facts,
                        ) || materialization_equivalent_available_fact(&premise, &all_pure_facts)
                            .is_some()
                            || crate::kernel::loadable_covered_by_fact(&assumptions, &premise);
                    if !premise_is_available {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires an exact premise: {}",
                            describe_missing_pure_fact(
                                &premise,
                                &all_pure_facts,
                                state.resources().facts(),
                                parsed_function.parameters(),
                                arguments,
                                &replay.effect_facts,
                            )
                        )));
                    }
                    if !explicit_premises.contains(&premise) {
                        explicit_premises.push(premise);
                    }
                }
                for case in &replay.case_assumptions {
                    let branch_fact = if let Some(fact) = &case.fact {
                        fact.clone()
                    } else {
                        let proposition = lower_point_proposition(
                            &case.condition,
                            &all_pure_facts,
                            parsed_function.parameters(),
                            arguments,
                            &pre_state,
                            &state,
                            None,
                            &replay.program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower enclosing proof-branch condition: {message}"
                            ))
                        })?;
                        if case.value {
                            proposition
                        } else {
                            match proposition {
                                Proposition::ConditionIs(condition, value) => {
                                    Proposition::ConditionIs(condition, !value)
                                }
                                Proposition::Not(body) => *body,
                                proposition => Proposition::Not(Box::new(proposition)),
                            }
                        }
                    };
                    if exact_fact_is_available(&branch_fact, &all_pure_facts)
                        && !explicit_premises.contains(&branch_fact)
                    {
                        explicit_premises.push(branch_fact);
                    }
                }
                let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                for resource_fact in state
                    .resources()
                    .observable_facts_assuming_valid(&explicit_assumptions)
                {
                    if !explicit_premises.contains(&resource_fact) {
                        explicit_premises.push(resource_fact);
                    }
                }
                let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
                execute_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut explicit_premises,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &explicit_assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name,
                    &[],
                    None,
                    prerequisite_policy,
                    // `using` deliberately selects the exact context that may
                    // cross this statement boundary. Transport only those
                    // listed facts through the certified statement effect;
                    // ambient facts are restored below at their original
                    // snapshots.
                    StatementFactTransportPolicy::Selected,
                    loop_step_policy,
                )?;
                for fact in all_pure_facts {
                    if !explicit_premises.contains(&fact) {
                        explicit_premises.push(fact);
                    }
                }
                requirement_pure_facts = explicit_premises;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::Step
            | ProofTactic::CertifiedStatementStep { .. }
            | ProofTactic::CertifiedLoopSummaryStep { .. }
            | ProofTactic::CertifiedStatementReplay(_)
            | ProofTactic::CertifiedLoopSummaryReplay(_) => {
                let (
                    prerequisite_policy,
                    certified_prerequisites,
                    certified_replay,
                    loop_step_policy,
                ) = match tactic {
                    ProofTactic::Step => (
                        StatementPrerequisitePolicy::Exact,
                        &[][..],
                        None,
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::CertifiedStatementStep {
                        prerequisite_derivations,
                        ..
                    } => (
                        StatementPrerequisitePolicy::Certified,
                        prerequisite_derivations.as_slice(),
                        None,
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::CertifiedLoopSummaryStep {
                        prerequisite_derivations,
                        ..
                    } => (
                        StatementPrerequisitePolicy::Certified,
                        prerequisite_derivations.as_slice(),
                        None,
                        LoopStepPolicy::ApplyVerifiedRule,
                    ),
                    ProofTactic::CertifiedStatementReplay(evidence) => (
                        StatementPrerequisitePolicy::Certified,
                        evidence.transition.prerequisite_derivations.as_slice(),
                        Some(evidence.as_ref()),
                        LoopStepPolicy::EnterBody,
                    ),
                    ProofTactic::CertifiedLoopSummaryReplay(evidence) => (
                        StatementPrerequisitePolicy::Certified,
                        evidence.transition.prerequisite_derivations.as_slice(),
                        Some(evidence.as_ref()),
                        LoopStepPolicy::ApplyVerifiedRule,
                    ),
                    _ => unreachable!(),
                };
                execute_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    tactic_name(tactic),
                    certified_prerequisites,
                    certified_replay,
                    prerequisite_policy,
                    StatementFactTransportPolicy::None,
                    loop_step_policy,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CertifiedPathAssumption { facts, theorem, .. } => {
                if !matches!(
                    implication_body(theorem.proposition()),
                    Proposition::CConditionEvaluates { .. }
                ) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified path assumption is not backed by a condition-evaluation theorem"
                    )));
                }
                for fact in facts {
                    if !requirement_pure_facts.contains(fact) {
                        requirement_pure_facts.push(fact.clone());
                    }
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CertifiedAlternatives(alternatives) => {
                let outer_surface_replay = replay.surface_replay.clone();
                let base = ProofReplayContext {
                    state: state.clone(),
                    pure_facts: requirement_pure_facts.clone(),
                    replay: replay.clone(),
                    branch_path: branch_path.clone(),
                };
                let mut completed = Vec::new();
                let mut surface_paths = Vec::new();
                for alternative in alternatives {
                    let mut alternative_base = base.clone();
                    alternative_base.replay.surface_replay = SurfaceReplay::default();
                    let result = replay_internal_plan(
                        alternative_base,
                        function_block,
                        parsed_function,
                        claims,
                        claim_label,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        theorem_environment,
                        function,
                        arguments,
                        tactic_index,
                        source_index,
                        alternative,
                    )?;
                    surface_paths.push(result.replay.surface_replay.clone());
                    completed.push(BoundedProofFrontier {
                        replay: result.replay,
                        state: result.state,
                        pure_facts: result.pure_facts,
                    });
                }
                merge_bounded_execution_frontiers(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    function,
                    arguments,
                    completed,
                    claim_label,
                    tactic_index,
                )?;
                replay.surface_replay = outer_surface_replay;
                match synthesize_surface_alternatives(surface_paths) {
                    Ok(tactics) => {
                        for tactic in tactics {
                            replay.surface_replay.push(tactic);
                        }
                    }
                    Err(message) => replay.surface_replay.block(format!(
                        "could not lower certified branch alternatives: {message}"
                    )),
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartStep => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                execute_step_from_execution_point(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    tactic_index,
                    "step",
                    &[],
                    None,
                    StatementPrerequisitePolicy::Planning,
                    StatementFactTransportPolicy::Automatic,
                    LoopStepPolicy::EnterBody,
                )?;
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `step` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths => {
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                let force_all_paths = matches!(tactic, ProofTactic::SmartExecuteAllPaths);
                let direct_result = (!force_all_paths).then(|| {
                    execute_rest_from_execution_point(
                        &mut planning_replay,
                        &mut planning_state,
                        &mut planning_facts,
                        function_block,
                        function,
                        parsed_function.parameters(),
                        arguments,
                        function_environment,
                        claim_label,
                        tactic_index,
                    )
                });
                if direct_result.is_none_or(|result| result.is_err()) {
                    planning_replay = replay.clone();
                    planning_replay.planned_tactics.clear();
                    planning_state = state.clone();
                    planning_facts = requirement_pure_facts.clone();
                    bounded_execute_from_execution_point(
                        &mut planning_replay,
                        &mut planning_state,
                        &mut planning_facts,
                        function_block,
                        function,
                        parsed_function.parameters(),
                        arguments,
                        function_environment,
                        claim_label,
                        tactic_index,
                        StatementPrerequisitePolicy::Planning,
                    )?;
                }
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ExecuteUntil(region_ref) => {
                let code_region =
                    resolve_code_region_ref(function_block, region_ref, claim_label, tactic_index)?;
                let CodeRegion::Statement(statement_index) = code_region else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `execute_until` expects a statement region"
                    )));
                };
                let mut planning_replay = replay.clone();
                planning_replay.planned_tactics.clear();
                let mut planning_state = state.clone();
                let mut planning_facts = requirement_pure_facts.clone();
                execute_until_statement(
                    &mut planning_replay,
                    &mut planning_state,
                    &mut planning_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    function_environment,
                    statement_index,
                    claim_label,
                    tactic_index,
                    StatementPrerequisitePolicy::Planning,
                )?;
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&planning_replay.planned_tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `execute_until` planned a non-certificate tactic {:?}",
                                error.smart_tactic()
                            ))
                        })?;
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::SmartFrame(region_ref) => {
                if region_ref.is_some() {
                    let certificate =
                        ProofReplayPlan::from_planned_tactics(&[ProofTactic::FrameUsing {
                            region: region_ref.clone(),
                            premises: Vec::new(),
                        }])
                        .expect("exact frame is a simple tactic");
                    let result = replay_smart_plan(
                        ProofReplayContext {
                            state,
                            pure_facts: requirement_pure_facts,
                            replay,
                            branch_path,
                        },
                        function_block,
                        parsed_function,
                        claims,
                        claim_label,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        theorem_environment,
                        function,
                        arguments,
                        tactic_index,
                        source_index,
                        &certificate,
                    )?;
                    state = result.state;
                    requirement_pure_facts = result.pure_facts;
                    replay = result.replay;
                    branch_path = result.branch_path;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "frame")?;
                let Some(effect_claim) = claims
                    .iter()
                    .find(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `frame` has no effect claim to prove"
                    )));
                };
                let FunctionClaimRef::Effect(_, effect_clause) = effect_claim else {
                    unreachable!("selected claim must be an effect claim")
                };
                let execution = replay
                    .execution()
                    .expect("function-exit replay should contain an execution");
                let pre_state = replay.old_reference_state(&state);
                let mut path_derivations = Vec::with_capacity(execution.paths().len());
                for (path_index, path) in execution.paths().iter().enumerate() {
                    if !path.obligations().is_empty() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame` cannot plan from an execution path with unresolved obligations"
                        )));
                    }
                    let mut path_facts = requirement_pure_facts.clone();
                    path_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                    let mut compatible = true;
                    if !replay.case_assumptions.is_empty() {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = path.outcome()
                        else {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: proof-branch `frame` requires a return outcome"
                            )));
                        };
                        for case in &replay.case_assumptions {
                            let fact = if let Some(fact) = &case.fact {
                                fact.clone()
                            } else {
                                let condition = lower_outcome_proposition_with_program_points(
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    post_state,
                                    result,
                                    &path_facts,
                                    &case.condition,
                                    predicate_environment,
                                    click_function_environment,
                                    &replay.program_point_states,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{claim_label}` tactic {tactic_index}: could not align frame path with proof branch: {message}"
                                    ))
                                })?;
                                if case.value {
                                    condition
                                } else {
                                    Proposition::Not(Box::new(condition))
                                }
                            };
                            let mut case_facts = path_facts.clone();
                            case_facts.push(fact.clone());
                            if path_facts
                                .iter()
                                .any(|available| propositions_are_exact_negations(available, &fact))
                                || assumptions_from_propositions(&case_facts)
                                    .derive_proposition(&false_proposition())
                                    .is_some()
                            {
                                compatible = false;
                                break;
                            }
                            path_facts.push(fact);
                        }
                    }
                    if !compatible {
                        // A frame planned inside one proof branch owns only
                        // execution outcomes compatible with that branch.
                        continue;
                    }
                    path_derivations.push(plan_effect_clause_derivations(
                        claim_label,
                        path_index,
                        path.effect_facts(),
                        &path_facts,
                        effect_clause.effect(),
                        parsed_function.parameters(),
                        arguments,
                        pre_state,
                        path.outcome(),
                    )?);
                }
                let certificate =
                    ProofReplayPlan::from_planned_tactics(&[ProofTactic::CertifiedFrame(
                        path_derivations,
                    )])
                    .expect("certified frame is a simple tactic");
                let result = replay_smart_plan(
                    ProofReplayContext {
                        state,
                        pure_facts: requirement_pure_facts,
                        replay,
                        branch_path,
                    },
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                    tactic_index,
                    source_index,
                    &certificate,
                )?;
                state = result.state;
                requirement_pure_facts = result.pure_facts;
                replay = result.replay;
                branch_path = result.branch_path;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FrameUsing {
                region: region_ref,
                premises: surface_premises,
            } => {
                let mut frame_facts = Vec::new();
                if !surface_premises.is_empty() {
                    let all_pure_facts = requirement_pure_facts.clone();
                    let pre_state = replay.old_reference_state(&state).clone();
                    for surface_premise in surface_premises {
                        let premise = if let Some(recorded) = replay
                            .surface_propositions
                            .available_kernel(surface_premise, &all_pure_facts)
                        {
                            recorded.clone()
                        } else {
                            lower_point_proposition(
                                surface_premise,
                                &all_pure_facts,
                                parsed_function.parameters(),
                                arguments,
                                &pre_state,
                                &state,
                                None,
                                &replay.program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` tactic {tactic_index}: could not lower `frame using` premise `{}`: {message}",
                                    super::printing::source_click_proposition(surface_premise)
                                ))
                            })?
                        };
                        replay
                            .surface_propositions
                            .record_lowering(surface_premise, &premise)?;
                        if !(exact_fact_is_available_across_effects(
                            &premise,
                            &all_pure_facts,
                            &replay.effect_facts,
                        ) || replay.ordered_finalization && replay.is_at_function_exit())
                            && materialization_equivalent_available_fact(&premise, &all_pure_facts)
                                .is_none()
                        {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `frame using` requires an exact premise: {}",
                                describe_missing_pure_fact(
                                    &premise,
                                    &all_pure_facts,
                                    state.resources().facts(),
                                    parsed_function.parameters(),
                                    arguments,
                                    &replay.effect_facts,
                                )
                            )));
                        }
                        if !frame_facts.contains(&premise) {
                            frame_facts.push(premise);
                        }
                    }
                } else {
                    frame_facts = requirement_pure_facts.clone();
                }
                let mut loop_effect_facts = frame_facts.clone();
                loop_effect_facts.extend(
                    replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                loop_effect_facts.sort();
                loop_effect_facts.dedup();
                if let Some(goal) = replay.loop_effect_goal.as_mut() {
                    if region_ref.is_some() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: a structural effect proof must use unqualified `frame()`"
                        )));
                    }
                    if goal.closed {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: the structural effect goal was closed more than once"
                        )));
                    }
                    c_loop_effects_hold_at_back_edge(
                        &goal.before_state,
                        &state,
                        std::slice::from_ref(&goal.check),
                        &loop_effect_facts,
                        &assumptions_from_propositions(&loop_effect_facts),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame()` failed: {message}"
                        ))
                    })?;
                    goal.closed = true;
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "frame")?;
                let code_region = region_ref
                    .as_ref()
                    .map(|region_ref| {
                        resolve_code_region_ref(
                            function_block,
                            region_ref,
                            claim_label,
                            tactic_index,
                        )
                    })
                    .transpose()?;
                if replay.ordered_finalization
                    && replay.is_at_function_exit()
                    && matches!(code_region, None | Some(CodeRegion::Function))
                {
                    if !replay.grouped_contract {
                        validate_frame_code_region(
                            function_block,
                            parsed_function,
                            code_region,
                            &claims[0],
                            claim_label,
                            tactic_index,
                        )?;
                    }
                    let Some(effect_claim) = claims
                        .iter()
                        .find(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `frame()` has no effect claim to prove"
                        )));
                    };
                    validate_frame_code_region(
                        function_block,
                        parsed_function,
                        code_region,
                        effect_claim,
                        claim_label,
                        tactic_index,
                    )?;
                    let deferred = if surface_premises.is_empty() {
                        PostExecutionTactic::Frame
                    } else {
                        PostExecutionTactic::FrameUsing {
                            region: region_ref.clone(),
                            premises: surface_premises.clone(),
                            facts: frame_facts,
                        }
                    };
                    replay.defer_post_execution(tactic_index, source_index, deferred);
                    replay.frames.insert(region_ref.clone());
                    continue;
                }
                let effect_claims = claims
                    .iter()
                    .filter(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
                    .collect::<Vec<_>>();
                if effect_claims.is_empty() {
                    validate_frame_code_region(
                        function_block,
                        parsed_function,
                        code_region,
                        &claims[0],
                        claim_label,
                        tactic_index,
                    )?;
                }
                for claim in effect_claims {
                    validate_frame_code_region(
                        function_block,
                        parsed_function,
                        code_region,
                        claim,
                        claim_label,
                        tactic_index,
                    )?;
                    match code_region {
                        None | Some(CodeRegion::Function) => {
                            validate_function_frame_tactic(
                                replay.execution().expect("execution should exist"),
                                claim,
                                claim_label,
                                tactic_index,
                                parsed_function.parameters(),
                                arguments,
                                &state,
                                &frame_facts,
                            )?;
                        }
                        Some(CodeRegion::Loop(_)) => {}
                        Some(CodeRegion::Statement(_)) => {}
                    }
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let region = region_ref.clone().ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: contextual function `frame()` should have been deferred earlier"
                        ))
                    })?;
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::FrameRegion(region),
                    );
                }
                replay.frames.insert(region_ref.clone());
            }
            ProofTactic::CertifiedFrame(path_derivations) => {
                require_function_exit(&replay, claim_label, tactic_index, "certified_frame")?;
                replay.defer_post_execution(
                    tactic_index,
                    source_index,
                    PostExecutionTactic::CertifiedFrame(path_derivations.clone()),
                );
            }
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::UnfoldPredicate(name.clone()),
                    );
                    continue;
                }
                if !replay.unfolded_predicates.contains(name) {
                    replay.unfolded_predicates.push(name.clone());
                }
                let surface_unfoldings = requirement_pure_facts
                    .iter()
                    .filter_map(|kernel| {
                        let Proposition::Predicate {
                            name: kernel_name, ..
                        } = kernel
                        else {
                            return None;
                        };
                        if kernel_name != name {
                            return None;
                        }
                        let ClickProposition::PredicateCall {
                            name: surface_name,
                            arguments: surface_arguments,
                        } = replay.surface_propositions.surface(kernel).ok()?
                        else {
                            return None;
                        };
                        let definition = predicate_environment.get(surface_name)?;
                        let surface =
                            instantiate_click_predicate_definition(definition, surface_arguments)
                                .ok()?;
                        let unfolded = unfold_predicates_in_proposition(
                            predicate_environment,
                            click_function_environment,
                            std::slice::from_ref(name),
                            kernel,
                            &assumptions,
                        )
                        .ok()?;
                        Some((surface, unfolded))
                    })
                    .collect::<Vec<_>>();
                requirement_pure_facts = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &requirement_pure_facts,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
                for (surface, kernel) in surface_unfoldings {
                    replay
                        .surface_propositions
                        .record_lowering(&surface, &kernel)?;
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::ApplyTheorem(application) => {
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Apply(application.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `apply` is not available in this region proof"
                        )));
                    }
                } else {
                    match plan_explicit_theorem_application(
                        theorem_environment,
                        application,
                        claim_label,
                        tactic_index,
                        &requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &replay,
                        &state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            replay.surface_replay.push(ProofTactic::ApplyTheoremUsing {
                                application: application.clone(),
                                premises,
                            });
                        }
                        Err(error) => replay.surface_replay.block(format!(
                            "could not make theorem application premises explicit: {}",
                            error.message()
                        )),
                    }
                    requirement_pure_facts = apply_theorem_at_current_point(
                        theorem_environment,
                        application,
                        claim_label,
                        tactic_index,
                        requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        &replay.unfolded_predicates,
                        None,
                    )?;
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                }
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => {
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::ApplyUsing {
                                application: application.clone(),
                                premises: premises.clone(),
                            },
                        );
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: post-execution `apply using` is not available in this region proof"
                    )));
                }
                let all_pure_facts = requirement_pure_facts.clone();
                let mut lowering_facts = all_pure_facts.clone();
                append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
                let pre_state = replay.old_reference_state(&state).clone();
                let mut explicit_premises = Vec::new();
                for surface_premise in premises {
                    let premise = if let Some(recorded) = replay
                        .surface_propositions
                        .available_kernel(surface_premise, &all_pure_facts)
                    {
                        recorded.clone()
                    } else {
                        lower_point_proposition(
                            surface_premise,
                            &lowering_facts,
                            parsed_function.parameters(),
                            arguments,
                            &pre_state,
                            &state,
                            None,
                            &replay.program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                            ))
                        })?
                    };
                    if !exact_fact_is_available(&premise, &all_pure_facts)
                        && materialization_equivalent_available_fact(&premise, &all_pure_facts)
                            .is_none()
                    {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `apply using` requires an exact premise: {}",
                            describe_missing_pure_fact(
                                &premise,
                                &all_pure_facts,
                                state.resources().facts(),
                                parsed_function.parameters(),
                                arguments,
                                &replay.effect_facts,
                            )
                        )));
                    }
                    if !explicit_premises.contains(&premise) {
                        explicit_premises.push(premise);
                    }
                }
                let mut applied = apply_theorem_at_current_point(
                    theorem_environment,
                    application,
                    claim_label,
                    tactic_index,
                    explicit_premises,
                    parsed_function.parameters(),
                    arguments,
                    &pre_state,
                    &state,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                    &replay.unfolded_predicates,
                    Some(&lowering_facts),
                )?;
                for fact in all_pure_facts {
                    if !applied.contains(&fact) {
                        applied.push(fact);
                    }
                }
                requirement_pure_facts = applied;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FoldResource(resource) => {
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Fold(resource.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `fold` is not available in this region proof"
                        )));
                    }
                } else {
                    let pre_state = replay.old_reference_state(&state).clone();
                    state = fold_composite_resource_at_current_point(
                        resource_environment,
                        resource,
                        claim_label,
                        tactic_index,
                        &requirement_pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        &pre_state,
                        state,
                        predicate_environment,
                        click_function_environment,
                        &replay.unfolded_predicates,
                    )?;
                }
            }
            ProofTactic::Have(have) => {
                if replay.is_at_function_exit() {
                    if replay.ordered_finalization {
                        replay.defer_post_execution(
                            tactic_index,
                            source_index,
                            PostExecutionTactic::Have(have.clone()),
                        );
                    } else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: post-execution `have` is not available in this region proof"
                        )));
                    }
                    continue;
                }
                let mut have_facts = requirement_pure_facts.clone();
                have_facts.extend(
                    replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                for fact in replay.surface_propositions.kernel_facts() {
                    if !have_facts.contains(fact) {
                        have_facts.push(fact.clone());
                    }
                }
                let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
                let smart_plan = if let Some(unfolded_predicates) = &smart_unfolds {
                    let (fact, plan) = plan_smart_have_at_current_point(
                        have,
                        claim_label,
                        tactic_index,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        predicate_environment,
                        click_function_environment,
                        unfolded_predicates,
                        None,
                    )?;
                    Some((fact, plan))
                } else {
                    None
                };
                let fact = match &smart_plan {
                    Some((fact, _)) => fact.clone(),
                    None => prove_have_at_current_point(
                        have,
                        theorem_environment,
                        claim_label,
                        tactic_index,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        replay.old_reference_state(&state),
                        &state,
                        &replay.program_point_states,
                        &replay.surface_propositions,
                        predicate_environment,
                        click_function_environment,
                        function_block.requires(),
                    )?,
                };
                let surface_certificate = if let Some((_, plan)) = &smart_plan {
                    Some(surface_smart_have_certificate(
                        &mut replay,
                        &state,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        have,
                        plan,
                        smart_unfolds.as_deref().unwrap_or(&[]),
                    )?)
                } else {
                    surface_smart_apply_have_certificate(
                        &mut replay,
                        &state,
                        &have_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                        claim_label,
                        tactic_index,
                        have,
                        &fact,
                    )?
                };
                if let Some(mut certificate) = surface_certificate {
                    let replay_certificate = |certificate: &TacticCertificate| {
                        verify_surface_certificate(
                            ProofReplayContext {
                                state: state.clone(),
                                // Replay from the same certified context
                                // used to plan the smart `have`. In
                                // particular, field-derived loadability may
                                // depend on previously established surface
                                // facts or exact execution effects that are
                                // not part of the function's requirements.
                                pure_facts: have_facts.clone(),
                                replay: replay.clone(),
                                branch_path: branch_path.clone(),
                            },
                            function_block,
                            parsed_function,
                            claims,
                            claim_label,
                            function_environment,
                            predicate_environment,
                            click_function_environment,
                            resource_environment,
                            theorem_environment,
                            function,
                            arguments,
                            tactic_index,
                            source_index,
                            certificate,
                        )
                    };
                    let initial_replay = pure_goal_certificate_gateway(
                        claim_label,
                        || Ok(certificate.clone()),
                        replay_certificate,
                    );
                    if let Err(initial_error) = initial_replay {
                        let fallback = smart_plan.as_ref().and_then(|_| {
                            surface_smart_have_derivation_certificate(
                                &replay,
                                &state,
                                &have_facts,
                                parsed_function.parameters(),
                                arguments,
                                predicate_environment,
                                click_function_environment,
                                have,
                            )
                        });
                        let Some(fallback) = fallback else {
                            return Err(initial_error);
                        };
                        pure_goal_certificate_gateway(
                            claim_label,
                            || Ok(fallback.clone()),
                            replay_certificate,
                        )?;
                        certificate = fallback;
                    }
                    replay
                        .surface_replay
                        .tactics
                        .extend_from_slice(certificate.tactics());
                }
                // Do not teach certificate replay the search-time lowering of
                // this goal until the generated surface certificate has
                // independently replayed. Otherwise a richer planner
                // materialization can make a nontrivial snapshot equality
                // appear reflexive and circularly validate `normalize()`.
                replay
                    .surface_propositions
                    .record_lowering(&have.proposition, &fact)?;
                if !requirement_pure_facts.contains(&fact) {
                    requirement_pure_facts.push(fact.clone());
                    assumptions = assumptions.assume_proposition(fact);
                }
            }
            ProofTactic::If(_) | ProofTactic::Branch(_) => {
                unreachable!("structured tactics are represented by internal proof nodes")
            }
            ProofTactic::Loop(_) => {
                unreachable!("frontier-local loops are replayed between linear tactic chunks")
            }
            ProofTactic::Witness(_) => {
                if replay.grouped_contract {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: top-level `witness` is not available in a grouped proof; use it inside `have proposition by {{ ... }}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let ProofTactic::Witness(witness) = tactic else {
                        unreachable!()
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Witness(witness.clone()),
                    );
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "witness")?;
            }
            ProofTactic::Choose(_) => {
                if replay.grouped_contract {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: top-level `choose` is not available in a grouped proof; use it inside `have proposition by {{ ... }}`"
                    )));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let ProofTactic::Choose(choice) = tactic else {
                        unreachable!()
                    };
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Choose(choice.clone()),
                    );
                    continue;
                }
                require_function_exit(&replay, claim_label, tactic_index, "choose")?;
            }
            ProofTactic::Assumption | ProofTactic::Normalize | ProofTactic::Rewrite(_) => {
                if !replay.region_proof {
                    require_function_exit(&replay, claim_label, tactic_index, tactic_name(tactic))?;
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    let post_tactic = match tactic {
                        ProofTactic::Assumption => PostExecutionTactic::Assumption,
                        ProofTactic::Normalize => PostExecutionTactic::Normalize,
                        ProofTactic::Rewrite(equality) => {
                            PostExecutionTactic::Rewrite(equality.clone())
                        }
                        _ => unreachable!(),
                    };
                    replay.defer_post_execution(tactic_index, source_index, post_tactic);
                }
            }
            ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Contradiction(_)
            | ProofTactic::Derive(_) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{}` is only available while proving a pure goal, such as inside `have ... by`",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::ExactPropositionDerivation(derivation) => {
                if !derivation.replay(&assumptions) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: proposition derivation did not replay"
                    )));
                }
                if !requirement_pure_facts.contains(derivation.conclusion()) {
                    requirement_pure_facts.push(derivation.conclusion().clone());
                    assumptions = assumptions_from_propositions(&requirement_pure_facts);
                }
            }
            ProofTactic::CertifiedFactTransport {
                source,
                target,
                theorem,
            } => {
                let Some(available_source) =
                    materialization_equivalent_available_fact(source, &requirement_pure_facts)
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport is missing exact source {source:?}"
                    )));
                };
                if available_source != *source && !requirement_pure_facts.contains(source) {
                    requirement_pure_facts.retain(|fact| fact != &available_source);
                    requirement_pure_facts.push(source.clone());
                }
                let Proposition::Implies(theorem_source, theorem_target) = theorem.proposition()
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport theorem is not an implication"
                    )));
                };
                if theorem_source.as_ref() != source || theorem_target.as_ref() != target {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: certified fact transport theorem does not match its source and target"
                    )));
                }
                if !requirement_pure_facts.contains(target) {
                    requirement_pure_facts.push(target.clone());
                }
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::FinishCertifiedFactTransports(sources) => {
                requirement_pure_facts.retain(|fact| !sources.contains(fact));
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofTactic::CloseInvariants => {
                if !replay.loop_invariant_region {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `close_invariants` is only available in a loop-region proof"
                    )));
                }
                if replay.region_invariants_closed {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: the invariant bundle was closed more than once on one path"
                    )));
                }
                replay.region_invariants_closed = true;
                replay.invariant_closer_step = Some(InvariantCloserStep {
                    tactic_index,
                    source_index,
                    statement_index: replay.frontier.next_statement_index,
                });
            }
            ProofTactic::Induct { .. }
            | ProofTactic::ApplyInduction { .. }
            | ProofTactic::CloseInduction => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `{}` is available only in a pure theorem proof",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::Simp => {
                if !replay.region_proof {
                    require_function_exit(&replay, claim_label, tactic_index, "simp")?;
                }
                if replay.region_proof {
                    replay.region_simp = Some((tactic_index, source_index));
                }
                if replay.ordered_finalization && replay.is_at_function_exit() {
                    replay.defer_post_execution(
                        tactic_index,
                        source_index,
                        PostExecutionTactic::Simp,
                    );
                }
            }
        }
        if capture_this_tactic && !deferred_post_execution && !deferred_region_simp {
            return Err(finish_tactic_expansion_capture(
                &replay.surface_replay,
                false,
            ));
        }
    }

    if crate::instrumentation::deadline_exceeded() {
        return Err(ClickError::new(format!(
            "tactic time limit exceeded: {}",
            crate::instrumentation::deadline_context()
        )));
    }

    Ok(ProofReplayContext {
        state,
        pure_facts: requirement_pure_facts,
        replay,
        branch_path,
    })
}

#[allow(clippy::too_many_arguments)]
fn replay_internal_plan(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    certificate: &ProofReplayPlan,
) -> Result<ProofReplayContext, ClickError> {
    let tactics = certificate
        .tactics()
        .iter()
        .cloned()
        .map(|tactic| IndexedTactic {
            index: tactic_index,
            source_index,
            tactic,
        })
        .collect::<Vec<_>>();
    replay_linear_tactics(
        context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        &tactics,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_internal_plan_to_surface_certificate(
    context: &ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    plan: &ProofReplayPlan,
) -> Result<(TacticCertificate, ProofReplayContext), ClickError> {
    let mut lowering_context = context.clone();
    let tactics = matches!(plan.tactics(), [ProofTactic::CertifiedFrame(_)])
        .then(|| surface_branch_skeleton(&context.replay.surface_replay.tactics))
        .unwrap_or_default();
    lowering_context.replay.surface_replay = SurfaceReplay {
        tactics,
        last_step_entry: context.replay.surface_replay.last_step_entry.clone(),
        ..SurfaceReplay::default()
    };
    let lowered = replay_internal_plan(
        lowering_context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
        source_index,
        plan,
    )?;
    if let Some(blocker) = &lowered.replay.surface_replay.blocker {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart tactic could not produce a surface certificate: {blocker}"
        )));
    }
    if lowered.replay.surface_replay.tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart tactic produced an empty surface certificate"
        )));
    }
    let certificate =
        TacticCertificate::from_proof_tactics(&lowered.replay.surface_replay.tactics).map_err(
            |error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart tactic produced a non-surface certificate at {:?}: {:?}",
                error.path(),
                error.tactic_class()
            ))
            },
        )?;
    Ok((certificate, lowered))
}

#[allow(clippy::too_many_arguments)]
fn verify_surface_certificate(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    certificate: &TacticCertificate,
) -> Result<ProofReplayContext, ClickError> {
    let enclosing_branch_path = context.branch_path.clone();
    let enclosing_case_assumptions = context.replay.case_assumptions.clone();
    let program =
        build_generated_certificate_proof(certificate.tactics(), claim_label, source_index)?;
    let completed = SUPPRESS_TACTIC_EXPANSION_CAPTURE.with(|suppressed| {
        let previous = suppressed.replace(true);
        let result = execute_internal_proof(
            &program,
            context,
            function_block,
            parsed_function,
            claims,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            function,
            arguments,
        );
        suppressed.set(previous);
        result
    })?;
    merge_surface_certificate_contexts(
        completed,
        function,
        arguments,
        claim_label,
        tactic_index,
        source_index,
        &enclosing_branch_path,
        &enclosing_case_assumptions,
    )
}

fn merge_surface_certificate_contexts(
    mut completed: Vec<ProofReplayContext>,
    function: &CFunction,
    arguments: &[CExpression],
    claim_label: &str,
    tactic_index: usize,
    source_index: usize,
    enclosing_branch_path: &[String],
    enclosing_case_assumptions: &[ReplayCaseAssumption],
) -> Result<ProofReplayContext, ClickError> {
    if completed.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: surface certificate at source tactic {source_index} produced no replay contexts"
        )));
    }
    if completed.len() == 1 {
        return Ok(completed.pop().expect("one completed context exists"));
    }
    if completed
        .iter()
        .any(|context| !context.replay.is_at_function_exit())
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: branched surface certificate at source tactic {source_index} did not finish every branch at function exit"
        )));
    }
    let execution_start_state = completed[0]
        .replay
        .frontier
        .execution_start_state
        .clone()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: branched surface certificate has no execution start state"
            ))
        })?;
    let mut common_pure_facts = completed[0].pure_facts.clone();
    common_pure_facts.retain(|fact| {
        completed
            .iter()
            .skip(1)
            .all(|context| context.pure_facts.contains(fact))
    });
    let mut common_program_points = completed[0].replay.program_point_states.clone();
    common_program_points.retain(|point, point_state| {
        completed
            .iter()
            .skip(1)
            .all(|context| context.replay.program_point_states.get(point) == Some(point_state))
    });
    let mut paths = Vec::new();
    for context in &completed {
        let execution = context
            .replay
            .execution()
            .expect("every completed surface branch is at function exit");
        for path in execution.paths() {
            let mut facts = path.execution_facts();
            for fact in &context.pure_facts {
                let fact = ExecutionPureFact::new(fact.clone());
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
            let obligations = path.obligations().to_vec();
            if !paths
                .iter()
                .any(|(existing_outcome, existing_facts, existing_obligations)| {
                    existing_outcome == path.outcome()
                        && existing_facts == &facts
                        && existing_obligations == &obligations
                })
            {
                paths.push((path.outcome().clone(), facts, obligations));
            }
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
    merged.replay.case_assumptions = enclosing_case_assumptions.to_vec();
    merged.state = execution_start_state;
    merged.pure_facts = common_pure_facts;
    merged.branch_path = enclosing_branch_path.to_vec();
    Ok(merged)
}

#[allow(clippy::too_many_arguments)]
fn replay_smart_plan(
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactic_index: usize,
    source_index: usize,
    plan: &ProofReplayPlan,
) -> Result<ProofReplayContext, ClickError> {
    let outer_surface_replay = context.replay.surface_replay.clone();
    let (certificate, mut internal_result) = lower_internal_plan_to_surface_certificate(
        &context,
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
        source_index,
        plan,
    )?;
    let mut verified_result = verify_surface_certificate(
        context.clone(),
        function_block,
        parsed_function,
        claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        function,
        arguments,
        tactic_index,
        source_index,
        &certificate,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: generated surface certificate failed replay:\n{}\n{}",
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    let last_step_entry = internal_result
        .replay
        .surface_replay
        .last_step_entry
        .clone();
    internal_result.replay.surface_replay = outer_surface_replay;
    let replaces_existing_branch = matches!(plan.tactics(), [ProofTactic::CertifiedFrame(_)])
        && matches!(certificate.tactics(), [ProofTactic::If(_)])
        && internal_result
            .replay
            .surface_replay
            .tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::If(_)));
    if replaces_existing_branch {
        let branch_index = internal_result
            .replay
            .surface_replay
            .tactics
            .iter()
            .rposition(|tactic| matches!(tactic, ProofTactic::If(_)))
            .expect("an existing surface branch was checked above");
        internal_result
            .replay
            .surface_replay
            .tactics
            .truncate(branch_index);
        internal_result
            .replay
            .surface_replay
            .tactics
            .extend(certificate.tactics().iter().cloned());
    } else {
        for tactic in certificate.tactics() {
            internal_result.replay.surface_replay.push(tactic.clone());
        }
    }
    internal_result.replay.surface_replay.last_step_entry = last_step_entry;
    verified_result.replay.surface_replay = internal_result.replay.surface_replay;
    Ok(verified_result)
}

#[allow(clippy::too_many_arguments)]
fn execute_internal_proof(
    node: &InternalProofNode,
    context: ProofReplayContext,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
) -> Result<Vec<ProofReplayContext>, ClickError> {
    match node {
        InternalProofNode::Done => Ok(vec![context]),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            let branch_path = context.branch_path.clone();
            let context = replay_linear_tactics(
                context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
                tactics,
            )
            .map_err(|error| add_proof_branch_path(error, &branch_path))?;
            execute_internal_proof(
                continuation,
                context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )
        }
        InternalProofNode::If {
            index,
            condition,
            then_branch,
            else_branch,
            continuation,
        } => {
            let condition_text = describe_click_proposition(condition);
            let mut contexts = Vec::new();
            for (branch_name, value, branch) in [
                ("then", true, then_branch.as_ref()),
                ("else", false, else_branch.as_ref()),
            ] {
                let mut branch_context = context.clone();
                let branch_description =
                    format!("{branch_name} branch of proof `if {condition_text}`");
                branch_context.branch_path.push(branch_description);
                let feasible = introduce_proof_case_assumption(
                    &mut branch_context,
                    condition,
                    value,
                    *index,
                    parsed_function.parameters(),
                    arguments,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                )
                .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                if !feasible {
                    continue;
                }
                let branch_contexts = execute_internal_proof(
                    branch,
                    branch_context,
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                )?;
                for branch_context in branch_contexts {
                    let mut continued = execute_internal_proof(
                        continuation,
                        branch_context,
                        function_block,
                        parsed_function,
                        claims,
                        claim_label,
                        function_environment,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        theorem_environment,
                        function,
                        arguments,
                    )?;
                    contexts.append(&mut continued);
                }
            }
            Ok(contexts)
        }
        InternalProofNode::Branch {
            index,
            ensuring,
            then_branch,
            else_branch,
            continuation,
        } => {
            let statement_index = context.replay.frontier.next_statement_index;
            let source_region = context
                .replay
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` could not resolve source statement({statement_index})"
                    ))
                })?;
            if !matches!(source_region.kind, SourceStatementKind::If { .. }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `branch` requires a C `if` at the execution frontier, but statement({statement_index}) is not an `if`"
                )));
            }
            let continuation_index = source_region.continuation_node;
            let initial_continuation_depth = context.replay.frontier.continuations.len();
            let selected_source_index = context
                .replay
                .proof_site
                .as_ref()
                .and_then(selected_tactic_index_for_site);
            let capture_in_continuation = selected_source_index
                .is_some_and(|wanted| internal_proof_contains_source_index(continuation, wanted));
            let capture_condition = if selected_source_index.is_some() && !capture_in_continuation {
                let (_, _, statement, _) = next_top_level_statement_from_execution_point(
                    &context.replay,
                    &context.state,
                    function,
                    arguments,
                    claim_label,
                    *index,
                    "branch",
                )?;
                let CStatement::If { condition, .. } = statement else {
                    unreachable!("source branch was checked as an if above")
                };
                Some(surface_with_source_site(
                    &surface_c_condition(&condition),
                    &ProgramPointRef {
                        region: CodeRegionRef::Statement(statement_index),
                        kind: ProgramPointKind::Entry,
                    },
                )?)
            } else {
                None
            };
            let mut completed_contexts = Vec::new();
            let mut continuing_contexts = Vec::new();
            for (branch_name, take_then, branch) in [
                ("then", true, then_branch.as_ref()),
                ("else", false, else_branch.as_ref()),
            ] {
                let mut branch_context = context.clone();
                branch_context.branch_path.push(format!(
                    "{branch_name} arm of C `if` at statement({statement_index})"
                ));
                let entered = execute_branch_step_from_execution_point(
                    &mut branch_context.replay,
                    &mut branch_context.state,
                    &mut branch_context.pure_facts,
                    function_block,
                    function,
                    parsed_function.parameters(),
                    arguments,
                    claim_label,
                    *index,
                    "branch",
                    Some(take_then),
                    &[],
                    StatementPrerequisitePolicy::Contextual,
                    BranchStepPolicy::Explore,
                    true,
                )
                .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                if !entered {
                    continue;
                }
                branch_context.replay.has_structured_branch_history = true;
                if let Some(condition) = &capture_condition {
                    branch_context
                        .replay
                        .deferred_expansion_path_choices
                        .push(SurfacePathChoice {
                            occurrence: statement_index,
                            condition: condition.clone(),
                            value: take_then,
                            // The path is attached to the selected tactic's
                            // standalone certificate, whose prefix starts at
                            // offset zero after capture resets surface replay.
                            tactic_offset: 0,
                        });
                }
                let branch_contexts = execute_internal_proof(
                    branch,
                    branch_context,
                    function_block,
                    parsed_function,
                    claims,
                    claim_label,
                    function_environment,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function,
                    arguments,
                )?;
                for branch_context in branch_contexts {
                    let returned = branch_context.replay.is_at_function_exit();
                    let reached_continuation = branch_context
                        .replay
                        .completed_branch_regions
                        .contains(&statement_index)
                        && branch_context.replay.frontier.continuations.len()
                            <= initial_continuation_depth;
                    if !reached_continuation {
                        return Err(add_proof_branch_path(
                            ClickError::new(format!(
                                "`{claim_label}` tactic {index}: `{branch_name}` arm of `branch` must stop at the shared continuation statement({continuation_index}); its frontier is statement({})",
                                branch_context.replay.frontier.next_statement_index
                            )),
                            &branch_context.branch_path,
                        ));
                    }
                    if returned {
                        completed_contexts.push(branch_context);
                        continue;
                    }
                    continuing_contexts.push(branch_context);
                }
            }
            if completed_contexts.is_empty() && continuing_contexts.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {index}: `branch` found no feasible C `if` arm"
                )));
            }
            if continuing_contexts.is_empty() {
                return Ok(completed_contexts);
            }

            let mut joined_context = if let Some(assertions) = ensuring {
                let mut common_pure_facts = continuing_contexts[0].pure_facts.clone();
                common_pure_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.pure_facts.contains(fact))
                });
                let mut common_resource_facts =
                    continuing_contexts[0].state.resources().facts().to_vec();
                common_resource_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.state.resources().facts().contains(fact))
                });
                let mut stable_join_locals = continuing_contexts[0]
                    .state
                    .locals()
                    .object_values()
                    .map(|(name, value)| (name.to_string(), value.clone()))
                    .collect::<BTreeMap<_, _>>();
                stable_join_locals.retain(|name, value| {
                    continuing_contexts
                        .iter()
                        .skip(1)
                        .all(|context| context.state.locals().get(name) == Some(value))
                });
                let joined_frontier = continuing_contexts[0].replay.frontier.next_statement_index;
                if continuing_contexts
                    .iter()
                    .skip(1)
                    .any(|context| context.replay.frontier.next_statement_index != joined_frontier)
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` arms did not reach one common execution frontier"
                    )));
                }
                let target = ProgramPointRef {
                    region: CodeRegionRef::Statement(joined_frontier),
                    kind: ProgramPointKind::Entry,
                };
                let needs_abstraction = continuing_contexts.len() > 1;
                let mut joined: Option<ProofReplayContext> = None;
                for mut branch_context in continuing_contexts {
                    apply_branch_interface(
                        &target,
                        assertions,
                        *index,
                        &mut branch_context.replay,
                        &mut branch_context.state,
                        &mut branch_context.pure_facts,
                        parsed_function.parameters(),
                        arguments,
                        predicate_environment,
                        click_function_environment,
                        resource_environment,
                        claim_label,
                        &stable_join_locals,
                        needs_abstraction,
                    )
                    .map_err(|error| add_proof_branch_path(error, &branch_context.branch_path))?;
                    for fact in &common_pure_facts {
                        if !branch_context.pure_facts.contains(fact) {
                            branch_context.pure_facts.push(fact.clone());
                        }
                    }
                    let assumptions = assumptions_from_propositions(&branch_context.pure_facts);
                    let additional_common_resources = common_resource_facts
                        .iter()
                        .filter(|fact| !branch_context.state.resources().facts().contains(fact))
                        .cloned()
                        .collect::<Vec<_>>();
                    let resources = branch_context
                        .state
                        .resources()
                        .clone()
                        .try_compose_with_facts(additional_common_resources, &assumptions)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {index}: invalid automatic common `branch` resource interface: {error:?}"
                            ))
                        })?;
                    branch_context.state = branch_context.state.with_resource_context(resources);
                    if let Some(joined_context) = &mut joined {
                        append_execution_effect_facts(
                            &mut joined_context.replay.effect_facts,
                            &branch_context.replay.effect_facts,
                        );
                    } else {
                        joined = Some(branch_context);
                    }
                }
                joined.expect("at least one continuing branch context")
            } else if continuing_contexts.len() == 1 {
                continuing_contexts.remove(0)
            } else {
                let common_state = continuing_contexts[0].state.clone();
                if continuing_contexts
                    .iter()
                    .skip(1)
                    .any(|context| context.state != common_state)
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` arms reach the common frontier with different states; add an `ensuring` block describing the facts and resources needed afterward"
                    )));
                }
                let mut joined = continuing_contexts.remove(0);
                joined.pure_facts.retain(|fact| {
                    continuing_contexts
                        .iter()
                        .all(|context| context.pure_facts.contains(fact))
                });
                joined.replay.program_point_states.retain(|point, state| {
                    continuing_contexts.iter().all(|context| {
                        context.replay.program_point_states.get(point) == Some(state)
                    })
                });
                for context in &continuing_contexts {
                    append_execution_effect_facts(
                        &mut joined.replay.effect_facts,
                        &context.replay.effect_facts,
                    );
                }
                joined
            };
            joined_context.branch_path.clear();
            joined_context.replay.case_assumptions.clear();
            let mut continued = execute_internal_proof(
                continuation,
                joined_context,
                function_block,
                parsed_function,
                claims,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                function,
                arguments,
            )?;
            completed_contexts.append(&mut continued);
            Ok(completed_contexts)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn introduce_proof_case_assumption(
    context: &mut ProofReplayContext,
    condition: &ClickProposition,
    value: bool,
    tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<bool, ClickError> {
    if context.replay.is_at_function_exit()
        && context.replay.has_structured_branch_history
        && proof_case_is_stable_program_point_condition(condition)
    {
        // A source-qualified condition can still be lowered without choosing
        // one return outcome. Use it immediately when possible so a logical
        // certificate nested under an already selected C path does not
        // manufacture its contradictory sibling at function exit. Conditions
        // involving `result` or the post-state retain the deferred per-outcome
        // handling below.
        if let Ok(proposition) = lower_point_proposition(
            condition,
            &context.pure_facts,
            parameters,
            arguments,
            context.replay.old_reference_state(&context.state),
            &context.state,
            None,
            &context.replay.program_point_states,
            predicate_environment,
            click_function_environment,
        ) {
            let surface_fact = if value {
                condition.clone()
            } else {
                negate_click_proposition(condition)
            };
            let kernel_fact = if value {
                proposition
            } else {
                match proposition {
                    Proposition::ConditionIs(condition, value) => {
                        Proposition::ConditionIs(condition, !value)
                    }
                    Proposition::Not(body) => *body,
                    proposition => Proposition::Not(Box::new(proposition)),
                }
            };
            if context
                .pure_facts
                .iter()
                .any(|available| propositions_are_exact_negations(available, &kernel_fact))
            {
                return Ok(false);
            }
            context
                .replay
                .surface_propositions
                .record_lowering(&surface_fact, &kernel_fact)?;
            context.pure_facts.push(kernel_fact.clone());
            context.replay.case_assumptions.push(ReplayCaseAssumption {
                tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(kernel_fact),
                at_function_entry: false,
            });
            return Ok(true);
        }
    }
    if context.replay.is_at_function_exit() {
        context.replay.case_assumptions.push(ReplayCaseAssumption {
            tactic_index,
            condition: condition.clone(),
            value,
            fact: None,
            at_function_entry: false,
        });
        return Ok(true);
    }
    let at_function_entry = context.replay.is_at_function_entry();
    let proposition = lower_point_proposition(
        condition,
        &context.pure_facts,
        parameters,
        arguments,
        context.replay.old_reference_state(&context.state),
        &context.state,
        None,
        &context.replay.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower `if` condition: {message}"
        ))
    })?;
    let surface_fact = if value {
        condition.clone()
    } else {
        negate_click_proposition(condition)
    };
    let kernel_fact = if value {
        proposition
    } else {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition, !value)
            }
            Proposition::Not(body) => *body,
            proposition => Proposition::Not(Box::new(proposition)),
        }
    };
    if context
        .pure_facts
        .iter()
        .any(|available| propositions_are_exact_negations(available, &kernel_fact))
    {
        return Ok(false);
    }
    context
        .replay
        .surface_propositions
        .record_lowering(&surface_fact, &kernel_fact)?;
    context.pure_facts.push(kernel_fact.clone());
    context.replay.case_assumptions.push(ReplayCaseAssumption {
        tactic_index,
        condition: condition.clone(),
        value,
        fact: Some(kernel_fact),
        at_function_entry,
    });
    Ok(true)
}

fn proof_case_is_stable_program_point_condition(proposition: &ClickProposition) -> bool {
    let expression_is_stable = |expression: &ContractExpression| {
        matches!(
            expression,
            ContractExpression::At {
                selector: VisitSelector::ProgramPoint(_),
                ..
            } | ContractExpression::Old(_)
        )
    };
    fn stable(
        proposition: &ClickProposition,
        expression_is_stable: &impl Fn(&ContractExpression) -> bool,
    ) -> bool {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                expression_is_stable(left) && expression_is_stable(right)
            }
            ClickProposition::Defined { expression } => expression_is_stable(expression),
            ClickProposition::At {
                selector: VisitSelector::ProgramPoint(_),
                ..
            } => true,
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                stable(left, expression_is_stable) && stable(right, expression_is_stable)
            }
            ClickProposition::Not(body) => stable(body, expression_is_stable),
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::ForAll { .. }
            | ClickProposition::Exists { .. }
            | ClickProposition::RangeAll { .. }
            | ClickProposition::RangeAny { .. }
            | ClickProposition::PredicateCall { .. } => false,
        }
    }
    stable(proposition, &expression_is_stable)
}

fn add_proof_branch_context(error: ClickError, branch: &str) -> ClickError {
    if error.is_expansion_complete() {
        return error;
    }
    ClickError::new(format!("in {branch}:\n{}", error.message()))
}

fn add_proof_branch_path(mut error: ClickError, branch_path: &[String]) -> ClickError {
    for branch in branch_path.iter().rev() {
        error = add_proof_branch_context(error, branch);
    }
    error
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
