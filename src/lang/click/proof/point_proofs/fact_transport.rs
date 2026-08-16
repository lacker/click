use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn plan_explicit_fact_transport(
    surface_source: &ClickProposition,
    source: &Proposition,
    target: &Proposition,
    available: &[Proposition],
    effect_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    replay: &TacticReplayState,
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<ClickProposition>, ClickError> {
    let mut candidates = available
        .iter()
        .filter_map(|kernel| {
            let surface = checked_surface_comparison_fact_at_point(
                replay,
                kernel,
                SurfaceFactMatch::ReplayEquivalent,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .ok();
            surface.map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    let mut selected = Vec::new();
    if exact_fact_is_available(source, available) {
        let source_pair = (source.clone(), surface_source.clone());
        if !candidates.contains(&source_pair) {
            candidates.push(source_pair.clone());
        }
        selected.push(source_pair);
    }
    let replays = |selected: &[(Proposition, ClickProposition)]| {
        let explicit = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let explicit_assumptions = assumptions_from_propositions(&explicit);
        let resource_facts = state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        let selected_assumptions = available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        if selected_assumptions.derive_proposition(source).is_none() {
            return false;
        }
        if selected_assumptions.derive_proposition(target).is_some() {
            return true;
        }
        let transport_assumptions = effect_facts
            .iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        certified_fact_transport_reaches(source, target, state.memory(), &transport_assumptions)
    };

    if !replays(&selected) {
        let rank = |proposition: &Proposition| match proposition {
            Proposition::CResourceSeparate { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. } => 0,
            Proposition::ConditionIs(_, _) => 1,
            Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapLifetimeRetired { .. } => 2,
            _ => 3,
        };
        let mut remaining = candidates
            .iter()
            .filter(|pair| !selected.contains(pair))
            .cloned()
            .collect::<Vec<_>>();
        remaining.sort_by_key(|(kernel, _)| rank(kernel));
        for pair in remaining {
            selected.push(pair);
            if replays(&selected) {
                break;
            }
        }
    }
    if !replays(&selected) {
        let unavailable_count = available
            .iter()
            .filter(|fact| !candidates.iter().any(|(candidate, _)| candidate == *fact))
            .count();
        return Err(ClickError::new(format!(
            "explicit surface premises do not replay the certified fact transport\n  source: {source:?}\n  target: {target:?}\n  selected surface premises: {}\n  unspellable ambient facts: {unavailable_count} (internal facts omitted)",
            selected.len(),
        )));
    }
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if replays(&reduced) {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

pub(in crate::lang::click::proof) struct CheckedPointFactTransport {
    pub(in crate::lang::click::proof) source: Proposition,
    pub(in crate::lang::click::proof) target: Proposition,
}

/// Audited semantic operation for one explicit mid-execution
/// `transport(source, target) using { premises }`.
///
/// Both explicit source replay and `Proof::apply_step` call this operation.
/// It does not mutate surface bookkeeping or proof provenance; it returns the
/// exact checked source and target for those owners to record atomically.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn check_point_fact_transport_using(
    surface_source: &ClickProposition,
    surface_target: &ClickProposition,
    surface_premises: &[ClickProposition],
    claim_label: &str,
    tactic_index: usize,
    available: &[Proposition],
    effect_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CheckedPointFactTransport, ClickError> {
    let mut explicit_premises = Vec::new();
    for surface_premise in surface_premises {
        let premise = if let Some(recorded) =
            surface_propositions.available_kernel(surface_premise, available)
        {
            recorded.clone()
        } else {
            lower_point_proposition(
                surface_premise,
                available,
                parameters,
                arguments,
                pre_state,
                state,
                None,
                program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport using` premise: {message}"
                ))
            })?
        };
        if !exact_fact_is_available(&premise, available) {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `transport using` requires an exact premise: {}",
                describe_missing_pure_fact(
                    &premise,
                    available,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    effect_facts,
                )
            )));
        }
        if !explicit_premises.contains(&premise) {
            explicit_premises.push(premise);
        }
    }

    // Lowering memory expressions may use the validated ambient context, but
    // the proof itself remains restricted to explicit premises, resource
    // observations, and certified frame/effect facts.
    let source = if let Some(recorded) =
        surface_propositions.available_kernel(surface_source, available)
    {
        recorded.clone()
    } else {
        lower_point_proposition(
            surface_source,
            available,
            parameters,
            arguments,
            pre_state,
            state,
            None,
            program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
            ))
        })?
    };
    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
    let resource_facts = state
        .resources()
        .observable_facts_assuming_valid(&explicit_assumptions);
    let selected_assumptions = available
        .iter()
        .filter(|fact| is_implicit_fact_transport_context(fact))
        .cloned()
        .chain(resource_facts)
        .fold(explicit_assumptions, |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });
    if !exact_fact_is_available(&source, &explicit_premises)
        && !snapshot_bridged_fact_is_available_under(
            &source,
            &explicit_premises,
            &selected_assumptions,
            effect_facts,
        )
        && selected_assumptions
            .derive_atomic_proposition(&source)
            .is_none()
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `transport using` requires a source derivable from its explicit facts: {}",
            describe_missing_pure_fact(
                &source,
                available,
                state.resources().facts(),
                parameters,
                arguments,
                effect_facts,
            )
        )));
    }

    let mut direct_lowering_facts = facts_for_direct_surface_lowering(available);
    for premise in &explicit_premises {
        if !direct_lowering_facts.contains(premise) {
            direct_lowering_facts.push(premise.clone());
        }
    }
    // Never resolve the target through the recorded surface map: the same
    // surface spelling may deliberately name an older source snapshot.
    let target = lower_point_proposition(
        surface_target,
        &direct_lowering_facts,
        parameters,
        arguments,
        pre_state,
        state,
        None,
        program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
        ))
    })?;
    if !exact_fact_is_available_across_effects(&target, available, effect_facts)
        && materialization_equivalent_available_fact(&target, available).is_none()
    {
        let transition_facts = fact_transport_transition_facts(effect_facts, &source);
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
                effect_facts
            )));
        }
    }
    Ok(CheckedPointFactTransport { source, target })
}

fn surface_predicate_call_name(proposition: &ClickProposition) -> Option<&str> {
    match proposition {
        ClickProposition::PredicateCall { name, .. } => Some(name),
        ClickProposition::At { proposition, .. }
        | ClickProposition::Not(proposition)
        | ClickProposition::ForAll {
            body: proposition, ..
        }
        | ClickProposition::Exists {
            body: proposition, ..
        }
        | ClickProposition::RangeAll {
            body: proposition, ..
        }
        | ClickProposition::RangeAny {
            body: proposition, ..
        } => surface_predicate_call_name(proposition),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            surface_predicate_call_name(left).or_else(|| surface_predicate_call_name(right))
        }
        ClickProposition::Comparison { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => None,
    }
}

pub(in crate::lang::click::proof) fn fact_transport_planning_failure(
    source: &ClickProposition,
    target: &ClickProposition,
    unfolded_predicates: &[String],
    error: &ClickError,
) -> String {
    let opaque_name = [source, target]
        .into_iter()
        .filter_map(surface_predicate_call_name)
        .find(|name| !unfolded_predicates.iter().any(|unfolded| unfolded == name));
    if let Some(name) = opaque_name {
        return format!(
            "`transport` cannot frame opaque predicate `{name}` across C execution because its memory footprint is hidden; run `unfold({name});` before the execution steps and transport its unfolded definition"
        );
    }
    format!(
        "could not make fact transport premises explicit: {}",
        error.message()
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn replay_fact_transport_at_outcome(
    surface_source: &ClickProposition,
    surface_target: &ClickProposition,
    surface_premises: Option<&[ClickProposition]>,
    function_name: &str,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: &mut Vec<Proposition>,
    surface_propositions: &mut SurfacePropositionMap,
    transition_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ProofTactic, ClickError> {
    let lower = |surface: &ClickProposition, facts: &[Proposition]| {
        lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            facts,
            surface,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
    };
    let recorded_or_lowered = |surface: &ClickProposition,
                               facts: &[Proposition],
                               recorded_surfaces: &SurfacePropositionMap|
     -> Result<Proposition, ClickError> {
        if let Some(recorded) = recorded_surfaces.available_kernel(surface, facts) {
            Ok(recorded.clone())
        } else {
            lower(surface, facts).map_err(ClickError::new)
        }
    };

    for equation in crate::kernel::certified_store_equations(transition_facts) {
        if surface_propositions.surfaces(&equation).next().is_some()
            && !available.contains(&equation)
        {
            available.push(equation);
        }
    }

    let mut explicit_premises = Vec::new();
    let premise_timing = crate::instrumentation::OperationTiming::new(
        function_name,
        claim_label,
        "fact transport explicit premise lowering",
    );
    if let Some(surface_premises) = surface_premises {
        for surface_premise in surface_premises {
            let premise =
                recorded_or_lowered(surface_premise, available, surface_propositions).map_err(
                    |error| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport using` premise: {}",
                            error.message()
                        ))
                    },
                )?;
            if !exact_fact_is_available(&premise, available) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}, tactic {tactic_index}: `transport using` requires an exact premise: {premise:?}"
                )));
            }
            surface_propositions.record_lowering(surface_premise, &premise)?;
            if !explicit_premises.contains(&premise) {
                explicit_premises.push(premise);
            }
        }
    }
    drop(premise_timing);

    let source_timing = crate::instrumentation::OperationTiming::new(
        function_name,
        claim_label,
        "fact transport source lowering",
    );
    let recorded_source = surface_propositions
        .available_kernel(surface_source, available)
        .cloned();
    let ordinary_source = recorded_or_lowered(surface_source, available, surface_propositions)
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport` source: {}",
                error.message()
            ))
        })?;
    let concrete_source =
        lower(surface_source, available).unwrap_or_else(|_| ordinary_source.clone());
    let source = if recorded_source.is_some() {
        ordinary_source.clone()
    } else if proposition_contains_at_expression(surface_source) {
        lower_outcome_proposition_symbolically_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            available,
            surface_source,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
        .unwrap_or_else(|_| ordinary_source.clone())
    } else {
        ordinary_source.clone()
    };
    if matches!(
        normalize_proposition(&concrete_source),
        SimpProposition::True
    ) && !available.contains(&source)
    {
        // The selected snapshot materialized this load to a concrete value.
        // Keep the equivalent symbolic spelling as a checked fact so frame
        // transport can retain its memory identity.
        available.push(source.clone());
    }
    surface_propositions.record_lowering(surface_source, &source)?;
    drop(source_timing);
    let selected_assumptions = crate::instrumentation::measure_operation(
        function_name,
        claim_label,
        "fact transport assumption selection",
        || {
            let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
            if surface_premises.is_some() {
                let resource_facts = post_state
                    .resources()
                    .observable_facts_assuming_valid(&explicit_assumptions);
                available
                    .iter()
                    .filter(|fact| is_implicit_fact_transport_context(fact))
                    .cloned()
                    .chain(resource_facts)
                    .fold(explicit_assumptions, |assumptions, fact| {
                        assumptions.assume_proposition(fact)
                    })
            } else {
                assumptions_from_propositions(available)
            }
        },
    );
    // The source occupies its own checked slot in `transport(source, target)`.
    // It may therefore come from the recorded execution history; `using`
    // names only the auxiliary facts needed to replay the transport.
    if !exact_fact_is_available(&source, available)
        && !exact_fact_is_available(&source, &explicit_premises)
        && !snapshot_bridged_fact_is_available(&source, &explicit_premises, transition_facts)
        && selected_assumptions
            .derive_atomic_proposition(&source)
            .is_none()
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: `transport{}` requires a source derivable from its {}facts: {source:?}",
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
        )));
    }

    let mut direct_lowering_facts = facts_for_direct_surface_lowering(available);
    for premise in &explicit_premises {
        if !direct_lowering_facts.contains(premise) {
            direct_lowering_facts.push(premise.clone());
        }
    }
    let target_timing = crate::instrumentation::OperationTiming::new(
        function_name,
        claim_label,
        "fact transport target lowering",
    );
    let target = lower(surface_target, &direct_lowering_facts).map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport` target: {message}"
        ))
    })?;
    surface_propositions.record_lowering(surface_target, &target)?;
    drop(target_timing);
    let certificate_available = surface_premises.is_none().then(|| available.clone());

    if exact_fact_is_available(&target, available)
        || materialization_equivalent_available_fact(&target, available).is_some()
    {
        if !available.contains(&target) {
            available.push(target.clone());
        }
    } else {
        let transport_assumptions = transition_facts
            .iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        let reaches = crate::instrumentation::measure_operation(
            function_name,
            claim_label,
            "certified fact transport reachability",
            || {
                certified_fact_transport_reaches(
                    &source,
                    &target,
                    post_state.memory(),
                    &transport_assumptions,
                )
            },
        );
        if !reaches {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: no certified frame transport applies to the exact source fact"
            )));
        }
        available.push(target.clone());
    }

    let emitted_premises = if surface_premises.is_some() {
        None
    } else {
        Some(plan_explicit_fact_transport_at_outcome(
            surface_source,
            &source,
            &target,
            certificate_available
                .as_deref()
                .expect("smart transport retained its pre-transport facts"),
            transition_facts,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            replay,
            predicate_environment,
            click_function_environment,
        )?)
    };

    Ok(match emitted_premises {
        Some(premises) => ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        },
        None => ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises: surface_premises.unwrap_or_default().to_vec(),
        },
    })
}

#[allow(clippy::too_many_arguments)]
fn plan_explicit_fact_transport_at_outcome(
    _surface_source: &ClickProposition,
    source: &Proposition,
    target: &Proposition,
    available: &[Proposition],
    transition_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<ClickProposition>, ClickError> {
    let mut candidates = available
        .iter()
        .filter_map(|kernel| {
            checked_surface_fact_at_outcome(
                replay,
                kernel,
                SurfaceFactMatch::CanonicalExact,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            )
            .ok()
            .map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    candidates.retain(|(kernel, _)| kernel != source);
    let mut selected = Vec::new();
    let replays = |selected: &[(Proposition, ClickProposition)]| {
        let explicit = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let explicit_assumptions = assumptions_from_propositions(&explicit);
        let resource_facts = post_state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        let selected_assumptions = available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            })
            .assume_proposition(source.clone());
        if selected_assumptions.derive_proposition(target).is_some() {
            return true;
        }
        let transport_assumptions = transition_facts
            .iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        certified_fact_transport_reaches(
            source,
            target,
            post_state.memory(),
            &transport_assumptions,
        )
    };
    if !replays(&selected) {
        for pair in candidates {
            if !selected.contains(&pair) {
                selected.push(pair);
                if replays(&selected) {
                    break;
                }
            }
        }
    }
    if !replays(&selected) {
        return Err(ClickError::new(
            "post-execution fact transport has no explicit surface-premise certificate",
        ));
    }
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if replays(&reduced) {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

/// Erases every embedded memory snapshot from a comparison proposition so
/// two spellings of the same comparison at different snapshots compare
/// equal; used as a cheap prefilter before attempting a transport proof.
pub(in crate::lang::click::proof) fn memory_erased_comparison(
    proposition: &Proposition,
) -> Option<Proposition> {
    fn erase_term(term: &Bitvector32Term) -> Bitvector32Term {
        match term {
            Bitvector32Term::MemoryLoad(_, pointer) => Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(CMemory::default()),
                Box::new(Pointer {
                    block: pointer.block.clone(),
                    offset: erase_offset(&pointer.offset),
                }),
            ),
            Bitvector32Term::Add(left, right) => {
                Bitvector32Term::Add(Box::new(erase_term(left)), Box::new(erase_term(right)))
            }
            Bitvector32Term::Subtract(left, right) => {
                Bitvector32Term::Subtract(Box::new(erase_term(left)), Box::new(erase_term(right)))
            }
            Bitvector32Term::Multiply(left, right) => {
                Bitvector32Term::Multiply(Box::new(erase_term(left)), Box::new(erase_term(right)))
            }
            other => other.clone(),
        }
    }
    fn erase_offset(offset: &PointerOffsetTerm) -> PointerOffsetTerm {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                PointerOffsetTerm::Add(Box::new(erase_offset(left)), Box::new(erase_offset(right)))
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                PointerOffsetTerm::Int32Scaled {
                    value: Box::new(erase_term(value)),
                    byte_width: *byte_width,
                }
            }
            other => other.clone(),
        }
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let erased = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(erase_term(left)),
                Box::new(erase_term(right)),
            )
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            ConditionTerm::Bitvector32Equal(Box::new(erase_term(left)), Box::new(erase_term(right)))
        }
        _ => return None,
    };
    Some(Proposition::ConditionIs(erased, *value))
}

/// Compares branch facts after erasing the memory snapshot captured at the
/// branch point. In addition to the kernel's canonical spellings, accept the
/// ordinary complementary and operand-reversed spellings of signed order
/// comparisons (for example, `!(a < b)` and `a >= b`).
pub(in crate::lang::click::proof) fn path_condition_equivalent(
    left: &Proposition,
    right: &Proposition,
) -> bool {
    fn signed_order_equivalent(left: &Proposition, right: &Proposition) -> bool {
        let (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) = (left, right)
        else {
            return false;
        };
        use ConditionTerm::{
            Bitvector32SignedGreaterEqual as Ge, Bitvector32SignedGreaterThan as Gt,
            Bitvector32SignedLessEqual as Le, Bitvector32SignedLessThan as Lt,
        };
        match (left_condition, right_condition) {
            (Lt(left, right), Ge(other_left, other_right))
            | (Ge(left, right), Lt(other_left, other_right))
            | (Le(left, right), Gt(other_left, other_right))
            | (Gt(left, right), Le(other_left, other_right)) => {
                left == other_left && right == other_right && left_value != right_value
            }
            (Lt(left, right), Gt(other_left, other_right))
            | (Gt(left, right), Lt(other_left, other_right))
            | (Le(left, right), Ge(other_left, other_right))
            | (Ge(left, right), Le(other_left, other_right)) => {
                left == other_right && right == other_left && left_value == right_value
            }
            _ => false,
        }
    }

    if condition_polarity_equivalent(left, right) || signed_order_equivalent(left, right) {
        return true;
    }
    let (Some(left), Some(right)) = (
        memory_erased_comparison(left),
        memory_erased_comparison(right),
    ) else {
        return false;
    };
    condition_polarity_equivalent(&left, &right) || signed_order_equivalent(&left, &right)
}

/// The outermost memory snapshot a comparison proposition loads from, used
/// to pick the transport destination for certified-fact matching.
pub(in crate::lang::click::proof) fn proposition_outer_load_memory(
    proposition: &Proposition,
) -> Option<&CMemory> {
    fn term_outer(term: &Bitvector32Term) -> Option<&CMemory> {
        match term {
            Bitvector32Term::MemoryLoad(memory, _) => Some(memory),
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right) => {
                term_outer(left).or_else(|| term_outer(right))
            }
            _ => None,
        }
    }
    let Proposition::ConditionIs(condition, _) = proposition else {
        return None;
    };
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right) => {
            term_outer(left).or_else(|| term_outer(right))
        }
        _ => None,
    }
}

/// Like [`certified_fact_transport_reaches`], but first rewrites the source
/// through the transition facts' certified stores, so a fact spelled in
/// pre-store terms can reach a post-store spelling.
pub(in crate::lang::click::proof) fn certified_fact_transport_reaches_through(
    source: &Proposition,
    target: &Proposition,
    after: &CMemory,
    assumptions: &PureFactContext,
    transitions: &[ExecutionPureFact],
) -> bool {
    if certified_fact_transport_reaches(source, target, after, assumptions) {
        return true;
    }
    let rewritten = crate::kernel::rewrite_condition_through_certified_stores(source, transitions);
    if &rewritten == source {
        return false;
    }

    normalize_direct_atomic_memory_loads(&rewritten) == normalize_direct_atomic_memory_loads(target)
        || crate::kernel::c_condition_facts_equivalent_for_memory_resolution(
            &rewritten,
            target,
            assumptions,
        )
        || certified_fact_transport_reaches(&rewritten, target, after, assumptions)
}

pub(in crate::lang::click::proof) fn certified_fact_transport_reaches(
    source: &Proposition,
    target: &Proposition,
    after: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let equivalent = |left: &Proposition, right: &Proposition| {
        left == right
            || crate::kernel::c_condition_facts_equivalent_for_memory_resolution(
                left,
                right,
                assumptions,
            )
    };
    match (source, target) {
        (
            Proposition::ForAll {
                var: source_var,
                sort: source_sort,
                body: source_body,
            },
            Proposition::ForAll {
                var: target_var,
                sort: target_sort,
                body: target_body,
            },
        ) if source_var == target_var && source_sort == target_sort => {
            return certified_fact_transport_reaches(source_body, target_body, after, assumptions);
        }
        (
            Proposition::Implies(source_antecedent, source_consequent),
            Proposition::Implies(target_antecedent, target_consequent),
        ) if equivalent(source_antecedent, target_antecedent) => {
            let consequent_assumptions = assumptions
                .clone()
                .assume_proposition(target_antecedent.as_ref().clone());
            return certified_fact_transport_reaches(
                source_consequent,
                target_consequent,
                after,
                &consequent_assumptions,
            );
        }
        (
            Proposition::And(source_left, source_right),
            Proposition::And(target_left, target_right),
        )
        | (
            Proposition::Or(source_left, source_right),
            Proposition::Or(target_left, target_right),
        ) => {
            return certified_fact_transport_reaches(source_left, target_left, after, assumptions)
                && certified_fact_transport_reaches(
                    source_right,
                    target_right,
                    after,
                    assumptions,
                );
        }
        (Proposition::Not(source_body), Proposition::Not(target_body)) => {
            return equivalent(source_body, target_body);
        }
        (
            Proposition::CResourceSeparate {
                left: source_left,
                right: source_right,
            },
            Proposition::CResourceSeparate {
                left: target_left,
                right: target_right,
            },
        ) => {
            return crate::instrumentation::measure_operation(
                "kernel",
                "fact transport",
                "resource separation transport: direct orientation",
                || {
                    crate::instrumentation::measure_operation(
                        "kernel",
                        "fact transport",
                        "resource separation transport: direct left",
                        || c_resources_directly_match(source_left, target_left, assumptions),
                    ) && crate::instrumentation::measure_operation(
                        "kernel",
                        "fact transport",
                        "resource separation transport: direct right",
                        || c_resources_directly_match(source_right, target_right, assumptions),
                    )
                },
            ) || crate::instrumentation::measure_operation(
                "kernel",
                "fact transport",
                "resource separation transport: swapped orientation",
                || {
                    c_resources_directly_match(source_left, target_right, assumptions)
                        && c_resources_directly_match(source_right, target_left, assumptions)
                },
            );
        }
        (
            Proposition::CResourceContains {
                parent: source_parent,
                child: source_child,
            },
            Proposition::CResourceContains {
                parent: target_parent,
                child: target_child,
            },
        ) => {
            return c_resources_directly_match(source_parent, target_parent, assumptions)
                && c_resources_directly_match(source_child, target_child, assumptions);
        }
        _ => {}
    }
    if matches!(target, Proposition::CMemoryLoadable { .. }) {
        return assumptions.derive_atomic_proposition(target).is_some();
    }
    // Two spellings of the same condition fact — for example an element load
    // whose symbolic index the listed order facts pin to a constant — match
    // by the same bounded rule the atomic prover uses on context facts.
    if crate::kernel::c_condition_facts_match_for_transport(source, target, assumptions) {
        return true;
    }
    if let Some(theorem) =
        crate::kernel::prove_c_condition_fact_target_transport(source, target, assumptions)
    {
        let Proposition::Implies(theorem_source, theorem_target) = theorem.proposition() else {
            unreachable!("target-directed condition transport must produce an implication")
        };
        if theorem_source.as_ref() == source && theorem_target.as_ref() == target {
            return true;
        }
    }
    let Some(theorem) = prove_c_condition_fact_transport(source, after, assumptions) else {
        return false;
    };
    let Proposition::Implies(_, conclusion) = theorem.proposition() else {
        unreachable!("condition transport must produce an implication")
    };
    normalize_direct_atomic_memory_loads(conclusion) == normalize_direct_atomic_memory_loads(target)
}
