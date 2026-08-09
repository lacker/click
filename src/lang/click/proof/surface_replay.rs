use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn checked_surface_fact_at_point(
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

pub(super) fn snapshot_indexed_program_points<'a>(
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
pub(super) enum SurfaceFactMatch {
    CanonicalExact,
    ReplayEquivalent,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn checked_surface_comparison_fact_at_point(
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
        .is_ok_and(|premise| {
            exact_fact_is_available(&premise, available)
                || materialization_equivalent_available_fact(&premise, available).is_some()
        })
    };
    // A snapshot-indexed spelling paired with this exact available kernel fact
    // is replayable through the replay engine's program-point record. Requiring
    // it to lower again against the current heap would incorrectly demand that
    // old loads remain loadable now. Current-state spellings do not have that
    // stable anchor and still go through `strictly_replayable` below.
    let recorded_surfaces = replay
        .surface_propositions
        .surfaces(kernel)
        .collect::<Vec<_>>();
    for surface in recorded_surfaces.into_iter().rev() {
        if (proposition_contains_at_expression(surface)
            || proposition_contains_old_expression(surface))
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
pub(super) fn record_surface_replay_tactic(
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
            let mut exact_premises = evidence.transition.planning_premises.clone();
            for transport in &evidence.transition.fact_transports {
                if !transport.statement_local
                    && exact_fact_is_available(&transport.source, available)
                    && !exact_premises.contains(&transport.source)
                {
                    exact_premises.push(transport.source.clone());
                }
            }
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
                    // Planning records the exact entry-state premises consumed
                    // by successful checks without changing the authoritative
                    // execution transition.
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
            let premises = (|| -> Result<Vec<ClickProposition>, ClickError> {
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
                    let surface = checked_surface_fact_at_point(
                        replay,
                        fact,
                        available,
                        parameters,
                        arguments,
                        state,
                        predicate_environment,
                        click_function_environment,
                    )
                    .or_else(|_| {
                        checked_surface_comparison_fact_at_point(
                            replay,
                            fact,
                            SurfaceFactMatch::ReplayEquivalent,
                            available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        )
                    });
                    let Ok(mut surface) = surface else {
                        continue;
                    };
                    if !proposition_contains_at_expression(&surface)
                        && replay
                            .surface_propositions
                            .has_distinct_lowering(&surface, fact)
                    {
                        let entry_point = ProgramPointRef {
                            region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                            kind: ProgramPointKind::Entry,
                        };
                        let indexed = surface_with_source_site(&surface, &entry_point)?;
                        let lowered = lower_surface_candidate_at_point(
                            replay,
                            &indexed,
                            available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        );
                        if lowered.is_ok_and(|lowered| {
                            normalize_direct_atomic_memory_loads(&lowered)
                                == normalize_direct_atomic_memory_loads(fact)
                                || materialization_equivalent_available_fact(
                                    fact,
                                    std::slice::from_ref(&lowered),
                                )
                                .is_some()
                        }) {
                            surface = indexed;
                        }
                    }
                    replay
                        .surface_propositions
                        .record_lowering(&surface, fact)?;
                    if !premises.contains(&surface) {
                        premises.push(surface);
                    }
                }
                Ok(premises)
            })();
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

pub(super) fn statement_step_permission_needs_surface_premise(
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

pub(super) fn smart_simp_unfold_prefix(proof: &Proof) -> Option<Vec<String>> {
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
pub(super) fn lower_smart_simp_suffix_have(
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
pub(super) fn surface_simp_plan_proof(
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
pub(super) fn surface_smart_have_certificate(
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
pub(super) fn surface_smart_have_derivation_certificate(
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
pub(super) fn surface_outcome_smart_have_derivation(
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
pub(super) fn surface_smart_apply_have_certificate(
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
