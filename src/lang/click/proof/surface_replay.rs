use super::*;

#[allow(clippy::too_many_arguments)]
/// True when the proposition asserts a syntactically reflexive equality —
/// the shape defining-equation bridging facts collapse to once kernel-minted
/// load variables are resolved to their loads.
fn proposition_is_reflexive_equality(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::ConditionIs(condition, true) => match condition {
            ConditionTerm::Bitvector32Equal(left, right) => left == right,
            ConditionTerm::PointerOffsetEqual(left, right) => left == right,
            ConditionTerm::PointerEqual(left, right) => left == right,
            _ => false,
        },
        _ => false,
    }
}

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
    let assumptions = assumptions_from_propositions(available);
    checked_surface_fact_at_point_with_assumptions(
        replay,
        kernel,
        &assumptions,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
fn checked_surface_fact_at_point_with_assumptions(
    replay: &TacticReplayState,
    kernel: &Proposition,
    assumptions: &PureFactContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let check = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            assumptions,
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
    if let Ok(ClickProposition::Defined { expression }) =
        replay.surface_propositions.surface(kernel)
    {
        let old_candidate = ClickProposition::Defined {
            expression: ContractExpression::Old(Box::new(expression.clone())),
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
    let resolved_kernel =
        crate::kernel::resolve_minted_load_variables(kernel, &replay.effect_facts);
    // Representative selection can derive facts through load variables
    // whose defining facts are not in this replay's effect stream; the
    // registry is the kernel's own record of what each one stands for, and
    // resolving through it is the sanctioned display direction.
    let resolved_kernel =
        if crate::kernel::proposition_mentions_registered_canonical_load(&resolved_kernel) {
            crate::kernel::resolve_canonical_load_variables_from_registry(&resolved_kernel)
        } else {
            resolved_kernel
        };
    // The round trip is judged against the resolved fact: fresh lowering
    // writes loads as load terms, while the original may name them through
    // kernel-minted variables whose defining equations the resolution
    // already substituted.
    let round_trip_matches =
        |lowered: &Proposition| lowered == kernel || *lowered == resolved_kernel;
    // A fact that mentions a load variable is anchored to the snapshot its
    // cell was read from; synthesize it through the program point recorded
    // for that snapshot, so the form stays correct at every later proof
    // point where the certificate is replayed, rather than a plain form
    // that is correct only until the cell changes.
    if crate::kernel::proposition_mentions_registered_canonical_load(kernel) {
        let (exact_points, compatible_points) =
            snapshot_indexed_program_points(&resolved_kernel, &replay.program_point_states);
        for (point, point_state) in exact_points.iter().chain(&compatible_points) {
            let Some(candidate) = synthesize_surface_proposition(
                &resolved_kernel,
                parameters,
                arguments,
                point_state,
            ) else {
                continue;
            };
            let Ok(anchored) = surface_with_source_site(&candidate, point) else {
                continue;
            };
            if check(&anchored).as_ref().is_ok_and(&round_trip_matches) {
                return Ok(anchored);
            }
        }
    }
    let candidate = synthesize_surface_proposition(&resolved_kernel, parameters, arguments, state)
        .ok_or_else(|| {
            ClickError::new(surface_synthesis_failure(
                "kernel fact has no recorded or structurally synthesized surface form",
                kernel,
            ))
        })?;
    let lowered = check(&candidate);
    if lowered.as_ref().is_ok_and(&round_trip_matches) {
        return Ok(candidate);
    }
    if let ClickProposition::Loadable { segment } = &candidate {
        let mut old_segment = segment.clone();
        old_segment.state = ContractSegmentState::Old;
        let old_candidate = ClickProposition::Loadable {
            segment: old_segment,
        };
        if check(&old_candidate)
            .ok()
            .as_ref()
            .is_some_and(round_trip_matches)
        {
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
    let assumptions = assumptions_from_propositions(available);
    checked_surface_comparison_fact_at_point_with_availability(
        replay,
        kernel,
        match_kind,
        available,
        &assumptions,
        None,
        false,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn checked_surface_comparison_fact_at_point_with_indexed_facts(
    replay: &TacticReplayState,
    kernel: &Proposition,
    match_kind: SurfaceFactMatch,
    available: &ProofFacts,
    assumptions: &PureFactContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    checked_surface_comparison_fact_at_point_with_availability(
        replay,
        kernel,
        match_kind,
        &[],
        assumptions,
        Some(available),
        false,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn checked_surface_comparison_fact_for_typed_derivation(
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
    let assumptions = assumptions_from_propositions(available);
    checked_surface_comparison_fact_at_point_with_availability(
        replay,
        kernel,
        match_kind,
        available,
        &assumptions,
        None,
        true,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
fn checked_surface_comparison_fact_at_point_with_availability(
    replay: &TacticReplayState,
    kernel: &Proposition,
    match_kind: SurfaceFactMatch,
    available: &[Proposition],
    assumptions: &PureFactContext,
    indexed_available: Option<&ProofFacts>,
    allow_snapshot_blind_candidates: bool,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let matches_kernel = |lowered: &Proposition| {
        if matches!(match_kind, SurfaceFactMatch::CanonicalExact) {
            return lowered.clone() == kernel.clone();
        }
        let lowered = lowered.clone();
        let kernel = kernel.clone();
        condition_polarity_equivalent(&lowered, &kernel)
            || lowered == kernel
            || exactly_available_fact(&kernel, std::slice::from_ref(&lowered)).is_some()
            || quantified_binder_equivalent(&lowered, &kernel)
            || (allow_snapshot_blind_candidates
                && (separation_bridged_fact_is_available(
                    &kernel,
                    std::slice::from_ref(&lowered),
                    assumptions,
                    &[],
                ) || assumptions_from_propositions(std::slice::from_ref(&lowered))
                    .derive_simp_atomic_proposition(&kernel)
                    .is_some()))
    };
    let fact_is_available = |fact: &Proposition| {
        indexed_available.map_or_else(
            || {
                exact_fact_is_available(fact, available)
                    || exactly_available_fact(fact, available).is_some()
            },
            |indexed| indexed.replay_available_across_effects(fact, &[]),
        )
    };
    // Candidates below are matched through the permissive candidate lowering
    // (symbolic contract loads allowed), but the emitted certificate is
    // replayed by the ordinary executor, whose strict lowering carries
    // loadability obligations. A form that only lowers permissively —
    // for example a snapshot fact whose `at(...)` anchor was dropped so its
    // current-state loads are not provably loadable — must not be emitted.
    let strictly_replayable = |surface: &ClickProposition| {
        lower_point_proposition_with_assumptions(
            surface,
            assumptions,
            parameters,
            arguments,
            replay.old_reference_state(state),
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .as_ref()
        .is_ok_and(&fact_is_available)
    };
    // A snapshot-indexed form paired with this exact available kernel fact
    // is replayable through the replay engine's program-point record. Requiring
    // it to lower again against the current heap would incorrectly demand that
    // old loads remain loadable now. Current-state forms do not have that
    // stable anchor and still go through `strictly_replayable` below.
    let mut recorded_surfaces = replay
        .surface_propositions
        .surfaces(kernel)
        .cloned()
        .collect::<Vec<_>>();
    if allow_snapshot_blind_candidates {
        for candidate in replay.surface_propositions.snapshot_blind_kernels(kernel) {
            for surface in replay.surface_propositions.surfaces(candidate) {
                if !recorded_surfaces.contains(surface) {
                    recorded_surfaces.push(surface.clone());
                }
            }
        }
    }
    let parameter_names = parameters
        .iter()
        .map(syntax::C0Parameter::name)
        .collect::<BTreeSet<_>>();
    for surface in &recorded_surfaces {
        if matches!(
            surface,
            ClickProposition::Defined { expression }
                if !super::surface_certificates::contract_expression_mentions_c_local(
                    expression,
                    &parameter_names,
                )
        ) && replay
            .surface_propositions
            .available_kernel_matching(surface, &fact_is_available)
            == Some(kernel)
        {
            return Ok(surface.clone());
        }
    }
    for surface in recorded_surfaces.iter().rev() {
        if (proposition_contains_at_expression(surface)
            || proposition_contains_old_expression(surface))
            && replay
                .surface_propositions
                .available_kernel_matching(surface, &fact_is_available)
                .is_some_and(&matches_kernel)
            // A recorded pair can name a program point outside the current
            // replay scope (for example a function-prefix statement inside a
            // loop-region proof). The candidate lowering resolves recorded
            // snapshots without demanding current loadability, so it is the
            // right scope check here.
            && lower_surface_candidate_at_point_with_assumptions(
                replay,
                surface,
                assumptions,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            )
            .is_ok()
        {
            return Ok(surface.clone());
        }
    }
    // A fact that mentions a load variable is anchored to the snapshot the
    // cell was read from, so its program-point-anchored surface forms stay
    // correct at every later proof point, while a plain current-state form
    // is correct only until the cell changes: anchored forms are tried first
    // and plain forms last.
    let prefer_anchored = crate::kernel::proposition_mentions_registered_canonical_load(kernel);
    if !prefer_anchored
        && let Ok(surface) = checked_surface_fact_at_point_with_assumptions(
            replay,
            kernel,
            assumptions,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )
        && strictly_replayable(&surface)
    {
        return Ok(surface);
    }

    let mut bases = Vec::new();
    for surface in &recorded_surfaces {
        if !bases.contains(surface) {
            bases.push(surface.clone());
        }
    }
    let resolved_kernel =
        crate::kernel::resolve_minted_load_variables(kernel, &replay.effect_facts);
    // Canonical variables name loads whose snapshots the point index needs;
    // resolve through the registry when no defining fact is in scope, and
    // index points from the load term rather than the internal name.
    let resolved_kernel = if &resolved_kernel == kernel {
        crate::kernel::resolve_canonical_load_variables_from_registry(kernel)
    } else {
        resolved_kernel
    };
    let (exact_points, compatible_points) =
        snapshot_indexed_program_points(&resolved_kernel, &replay.program_point_states);
    if let Some(surface) =
        synthesize_surface_proposition(&resolved_kernel, parameters, arguments, state)
        && !bases.contains(&surface)
    {
        bases.push(surface);
    }
    for (_, point_state) in exact_points.iter().chain(&compatible_points) {
        if let Some(surface) =
            synthesize_surface_proposition(&resolved_kernel, parameters, arguments, point_state)
            && !bases.contains(&surface)
        {
            bases.push(surface);
        }
    }
    let plain_base_candidate = |bases: &[ClickProposition]| {
        bases
            .iter()
            .find(|base| {
                lower_surface_candidate_at_point_with_assumptions(
                    replay,
                    base,
                    assumptions,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                )
                .is_ok_and(|lowered| {
                    matches_kernel(&lowered)
                        || proposition_contains_at_expression(base)
                            && quantified_replay_equivalent_available_fact(
                                kernel,
                                std::slice::from_ref(&lowered),
                            )
                            .is_some()
                }) && strictly_replayable(base)
            })
            .cloned()
    };
    if !prefer_anchored && let Some(base) = plain_base_candidate(&bases) {
        return Ok(base);
    }
    for (point, _) in exact_points.iter().chain(&compatible_points) {
        for base in &bases {
            if let Ok(candidate) = surface_with_source_site(base, point)
                && lower_surface_candidate_at_point_with_assumptions(
                    replay,
                    &candidate,
                    assumptions,
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
                let lowered = lower_surface_candidate_at_point_with_assumptions(
                    replay,
                    &candidate,
                    assumptions,
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
                if lower_surface_candidate_at_point_with_assumptions(
                    replay,
                    &candidate,
                    assumptions,
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
    if prefer_anchored {
        if let Ok(surface) = checked_surface_fact_at_point_with_assumptions(
            replay,
            kernel,
            assumptions,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        ) && strictly_replayable(&surface)
        {
            return Ok(surface);
        }
        if let Some(base) = plain_base_candidate(&bases) {
            return Ok(base);
        }
    }
    if let Some(exhaustion) = surface_synthesis_exhaustion_description() {
        return Err(ClickError::new(format!(
            "comparison fact has no checked surface form at this proof point: {exhaustion}"
        )));
    }
    Err(ClickError::new(format!(
        "comparison fact has no replayable surface form at this proof point ({} exact and {} compatible recorded snapshots, {} structural bases)",
        exact_points.len(),
        compatible_points.len(),
        bases.len(),
    )))
}

pub(super) struct ProofCertificateConstructionContext<'a> {
    replay: &'a mut TacticReplayState,
    pub(super) proof_certificate_builder: &'a mut ProofCertificateBuilder,
}

impl<'a> ProofCertificateConstructionContext<'a> {
    pub(super) fn new(
        replay: &'a mut TacticReplayState,
        proof_certificate_builder: &'a mut ProofCertificateBuilder,
    ) -> Self {
        Self {
            replay,
            proof_certificate_builder,
        }
    }
}

impl std::ops::Deref for ProofCertificateConstructionContext<'_> {
    type Target = TacticReplayState;

    fn deref(&self) -> &Self::Target {
        self.replay
    }
}

impl std::ops::DerefMut for ProofCertificateConstructionContext<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.replay
    }
}

/// Constructs the surface step(s) for one planned operation directly into the
/// planning replay's own [`ProofCertificateBuilder`]. This is the plan-time
/// counterpart of the old plan-lowering replay: search commits to a move and
/// immediately records how that move is written in Surface Click, so a smart
/// tactic's result is a [`ProofCertificate`] value rather than a private operation
/// program that must be re-executed to discover its form.
///
/// Premises are written against the builder's replay-visible
/// `certificate_facts`, not the planning executor's own fact set.
pub(super) fn construct_simple_step_for_planned_operation(
    replay: &mut TacticReplayState,
    state: &CState,
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    environments: ConstructionEnvironments<'_>,
    operation: &ConstructionEvidence,
) {
    let mut builder = std::mem::take(&mut replay.proof_certificate_builder);
    let available = std::mem::take(&mut builder.certificate_facts);
    let available_facts = available.to_vec();
    {
        let mut context = ProofCertificateConstructionContext::new(replay, &mut builder);
        append_simple_proof_step_for_operation(
            &mut context,
            state,
            &available_facts,
            function_block,
            parameters,
            arguments,
            environments.predicate_environment,
            environments.click_function_environment,
            None,
            Some(operation),
            None,
        );
    }
    builder.certificate_facts = available;
    replay.proof_certificate_builder = builder;
}

#[allow(clippy::too_many_arguments)]
pub(super) fn append_simple_proof_step_for_operation(
    replay: &mut ProofCertificateConstructionContext<'_>,
    state: &CState,
    available: &[Proposition],
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    surface_tactic: Option<&ProofTactic>,
    internal_operation: Option<&ConstructionEvidence>,
    _statement_uses_memory_context: Option<bool>,
) {
    if replay.proof_certificate_builder.blocker.is_some() {
        return;
    }
    if let Err(error) = check_verification_deadline() {
        replay.proof_certificate_builder.block(error.message());
        return;
    }
    match (surface_tactic, internal_operation) {
        (
            None,
            Some(ConstructionEvidence::CertifiedStatementStep {
                prerequisite_derivations,
                exact_premises,
                planned_transition: Some(planned_transition),
            }),
        ) if !replay.proof_certificate_builder.lowering_planned_transition
            && replay
                .planned_statement_transitions
                .get(*planned_transition)
                .is_some() =>
        {
            let evidence = replay.planned_statement_transitions[*planned_transition].clone();
            replay.proof_certificate_builder.lowering_planned_transition = true;
            append_simple_proof_step_for_operation(
                replay,
                state,
                available,
                function_block,
                parameters,
                arguments,
                predicate_environment,
                click_function_environment,
                None,
                Some(&ConstructionEvidence::CertifiedStatementStep {
                    prerequisite_derivations: prerequisite_derivations.clone(),
                    exact_premises: exact_premises.clone(),
                    planned_transition: None,
                }),
                None,
            );
            replay.proof_certificate_builder.lowering_planned_transition = false;
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
                                &crate::kernel::resolve_minted_load_variables(
                                    &transport.target,
                                    &replay.effect_facts,
                                ),
                                parameters,
                                arguments,
                                state,
                            )
                        })
                    });
                let Some(surface) = surface else {
                    replay.proof_certificate_builder.block(format!(
                        "statement-local frame witness has no checked surface form: {:?}",
                        transport.target
                    ));
                    continue;
                };
                replay
                    .proof_certificate_builder
                    .push_have(surface, SourceProof::Script(vec![ProofTactic::Normalize]));
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
                        replay.proof_certificate_builder.block(format!(
                            "public opaque-call result fact has no stable surface form: {}",
                            error.message()
                        ));
                        continue;
                    }
                    emitted.push(surface.clone());
                    replay
                        .proof_certificate_builder
                        .push_have(surface, SourceProof::Script(vec![ProofTactic::Assumption]));
                }
            }
        }
        (
            None,
            Some(ConstructionEvidence::CertifiedLoopSummaryStep {
                prerequisite_derivations,
                exact_premises,
                planned_transition: Some(planned_transition),
            }),
        ) if !replay.proof_certificate_builder.lowering_planned_transition
            && replay
                .planned_statement_transitions
                .get(*planned_transition)
                .is_some() =>
        {
            replay.proof_certificate_builder.lowering_planned_transition = true;
            append_simple_proof_step_for_operation(
                replay,
                state,
                available,
                function_block,
                parameters,
                arguments,
                predicate_environment,
                click_function_environment,
                None,
                Some(&ConstructionEvidence::CertifiedLoopSummaryStep {
                    prerequisite_derivations: prerequisite_derivations.clone(),
                    exact_premises: exact_premises.clone(),
                    planned_transition: None,
                }),
                _statement_uses_memory_context,
            );
            replay.proof_certificate_builder.lowering_planned_transition = false;
        }
        (
            None,
            Some(ConstructionEvidence::CertifiedStatementStep {
                prerequisite_derivations: derivations,
                exact_premises,
                ..
            }),
        ) => {
            replay.proof_certificate_builder.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            });
            let mut selectable_available = available.to_vec();
            let mut unfolded_dependency_facts = BTreeSet::new();
            let mut local_unfold_haves: Vec<(String, ClickProposition, Proposition)> = Vec::new();
            for exact in exact_premises {
                // Preserve an explicit unfolding already present in the
                // ambient proof. Reconstructing the same prerequisite from
                // an opaque predicate would add an unnecessary local `have`
                // and discard the user's established source form.
                if let Ok(Some(derivation)) = minimal_proposition_derivation(exact, available)
                    && !derivation
                        .context_premises()
                        .iter()
                        .any(|premise| matches!(premise, Proposition::Predicate { .. }))
                    && replay.surface_propositions.surfaces(exact).next().is_some()
                {
                    continue;
                }
                for predicate in available {
                    let Proposition::Predicate { name, .. } = predicate else {
                        continue;
                    };
                    let Ok(unfolded) = unfold_predicates_in_proposition(
                        predicate_environment,
                        click_function_environment,
                        std::slice::from_ref(name),
                        predicate,
                        &assumptions_from_propositions(available),
                    ) else {
                        continue;
                    };
                    let mut conjuncts = Vec::new();
                    atomic_conjuncts(&unfolded, &mut conjuncts);
                    let mut candidate_context = available
                        .iter()
                        .filter(|fact| *fact != exact && *fact != predicate)
                        .cloned()
                        .collect::<Vec<_>>();
                    candidate_context.extend(conjuncts.iter().map(|fact| (*fact).clone()));
                    if !matches!(
                        minimal_proposition_derivation(exact, &candidate_context),
                        Ok(Some(_))
                    ) {
                        continue;
                    }
                    let surface_predicate = replay
                        .surface_propositions
                        .surface(predicate)
                        .ok()
                        .cloned()
                        .or_else(|| {
                            synthesize_surface_proposition(predicate, parameters, arguments, state)
                        });
                    let Some(ClickProposition::PredicateCall {
                        name: surface_name,
                        arguments: surface_arguments,
                    }) = surface_predicate.as_ref()
                    else {
                        continue;
                    };
                    let Some(definition) = predicate_environment.get(surface_name) else {
                        continue;
                    };
                    let Ok(mut surface_body) =
                        instantiate_click_predicate_definition(definition, surface_arguments)
                    else {
                        continue;
                    };
                    if replay.execution_start_facts.contains(predicate) {
                        let point = ProgramPointRef {
                            region: CodeRegionRef::Function,
                            kind: ProgramPointKind::Entry,
                        };
                        let Ok(indexed) = surface_with_source_site(&surface_body, &point) else {
                            continue;
                        };
                        surface_body = indexed;
                    }
                    if !local_unfold_haves
                        .iter()
                        .any(|(_, existing, _)| existing == &surface_body)
                    {
                        local_unfold_haves.push((name.clone(), surface_body, unfolded.clone()));
                    }
                    for conjunct in conjuncts {
                        unfolded_dependency_facts.insert(conjunct.clone());
                        if !selectable_available.contains(conjunct) {
                            selectable_available.push(conjunct.clone());
                        }
                    }
                    break;
                }
            }
            for (name, surface, kernel) in local_unfold_haves {
                if let Err(error) = replay
                    .surface_propositions
                    .record_lowering(&surface, &kernel)
                {
                    replay.proof_certificate_builder.block(format!(
                        "could not record local predicate-unfold prerequisite: {}",
                        error.message()
                    ));
                    return;
                }
                replay.proof_certificate_builder.push_have(
                    surface,
                    SourceProof::Script(vec![
                        ProofTactic::UnfoldPredicate(name),
                        ProofTactic::Assumption,
                    ]),
                );
            }
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
                for fact in &selectable_available {
                    atomic_conjuncts(fact, &mut available_conjuncts);
                }
                // Source-written memory-range separation facts (for example
                // a resource body's canonical
                // `separate(memory(object(owner)), ...)` aggregate) that can
                // re-fold a decomposed per-field separation back to its
                // declared form below. Entailment assumptions are built
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
                let mut written_separations = available_conjuncts
                    .iter()
                    .copied()
                    .filter_map(|candidate| {
                        let bases = memory_separation_bases(candidate)?;
                        replay
                            .surface_propositions
                            .surfaces(candidate)
                            .next()
                            .is_some()
                            .then_some((candidate, bases, None::<PureFactContext>))
                    })
                    .collect::<Vec<_>>();
                for fact in &available_conjuncts {
                    let fact = *fact;
                    let selected_by_derivation =
                        derivation_context.iter().any(|required| {
                            (*required).eq(fact) || required.clone() == fact.clone()
                        }) || exact_premises.iter().any(|required| {
                            required == fact
                                || required.clone() == fact.clone()
                                || exactly_available_fact(required, std::slice::from_ref(fact))
                                    .is_some()
                        }) || unfolded_dependency_facts.contains(fact);
                    // A permission the resource projection reproduces is
                    // reconstructed by the replay for itself. One it does not
                    // reproduce is only available because the ambient context
                    // carried it, so the certificate has to write it.
                    let non_reconstructible_permission =
                        statement_step_permission_needs_surface_premise(
                            fact,
                            &projected_resource_facts,
                        );
                    if !selected_by_derivation && !non_reconstructible_permission {
                        continue;
                    }
                    // A separation carried only as an ambient permission may
                    // be one piece of a source-written aggregate (`unfold`
                    // decomposes `separate(memory(object(owner)), ...)` into
                    // per-field separations). Re-fold it: emit the strictly
                    // stronger declared fact, whose canonical form the
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
                        for (candidate, (left, right), cached) in &mut written_separations {
                            if *candidate == fact
                                || !(*left == fact_left && *right == fact_right
                                    || *left == fact_right && *right == fact_left)
                            {
                                continue;
                            }
                            // An arithmetically true separation (same base,
                            // disjoint constant ranges) is derivable from
                            // any premise set, so entailment cannot pick a
                            // fold target for it; keep its own form.
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
                        &selectable_available,
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
                            &selectable_available,
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
                            &selectable_available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        );
                        if lowered.is_ok_and(|lowered| {
                            lowered.clone() == fact.clone()
                                || exactly_available_fact(fact, std::slice::from_ref(&lowered))
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
                Ok(premises) => replay
                    .proof_certificate_builder
                    .push_step(SimpleProofStep::StepUsing(premises)),
                Err(error) => replay.proof_certificate_builder.block(format!(
                    "could not express a statement-step premise at the current proof point: {}",
                    error.message()
                )),
            }
        }
        (
            None,
            Some(ConstructionEvidence::CertifiedLoopSummaryStep {
                prerequisite_derivations: derivations,
                exact_premises,
                ..
            }),
        ) => {
            let loop_index = replay
                .source_layout
                .statement(replay.frontier.next_statement_index)
                .and_then(|region| match region.kind {
                    SourceStatementKind::Loop { loop_index } => Some(loop_index),
                    SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
                });
            let Some(loop_index) = loop_index else {
                replay
                    .proof_certificate_builder
                    .block("certified loop-summary replay is not at a source loop entry");
                return;
            };
            replay.proof_certificate_builder.last_step_entry = Some(ProgramPointRef {
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
                        .proof_certificate_builder
                        .push_step(SimpleProofStep::UnfoldPredicate(name));
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
                            proof: SourceProof::Tactic(SmartTactic::Simp),
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
                        &replay.surface_propositions,
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
                            .proof_certificate_builder
                            .steps
                            .extend(certificate.steps().iter().cloned()),
                        Err(error) => replay.proof_certificate_builder.block(error.message()),
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
                        proof: SourceProof::Tactic(SmartTactic::Simp),
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
                        &replay.surface_propositions,
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
                            replay.proof_certificate_builder.block(format!(
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
                                .proof_certificate_builder
                                .steps
                                .extend(certificate.steps().iter().cloned()),
                            Err(error) => replay.proof_certificate_builder.block(error.message()),
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
                    None,
                    &surface_available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                ) {
                    replay
                        .proof_certificate_builder
                        .push_have(conclusion, proof);
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
                    .map(|fact| (fact, normalize_proposition(fact), fact.clone()))
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
                                || **available == materialized
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
            replay.proof_certificate_builder.block(match premises {
                Ok(_) => "a detached loop-summary certificate has no surface form; use a frontier-local `loop { ... }` tactic".to_string(),
                Err(error) => format!(
                    "could not express a loop-summary premise at the current proof point: {}",
                    error.message()
                ),
            });
        }
        (None, Some(ConstructionEvidence::CertifiedFactTransport { source, target, .. })) => {
            // A canonical-load defining equation is kernel-internal naming
            // with no user-visible form; its transported form at the new
            // snapshot is itself certified by construction, so expansion
            // needs no explicit step for it.
            if crate::kernel::is_canonical_load_defining_fact(source)
                && crate::kernel::is_canonical_load_defining_fact(target)
            {
                return;
            }
            let Some(step_entry) = replay.proof_certificate_builder.last_step_entry.clone() else {
                replay
                    .proof_certificate_builder
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
                for recorded in replay.surface_propositions.kernel_facts() {
                    let matches = recorded == proposition
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
                replay.proof_certificate_builder.block(format!(
                    "fact transport has no recorded or synthesized Click comparison form\n  source: {source:?}\n  target: {target:?}"
                ));
                return;
            }
            let mut points = replay
                .program_point_states
                .keys()
                .cloned()
                .collect::<Vec<_>>();
            if !points.contains(&step_entry) {
                points.push(step_entry.clone());
            }
            let mut candidates = Vec::new();
            for base_surface in base_surfaces {
                let mut variants = vec![base_surface.clone()];
                for point in &points {
                    if let Ok(candidate) = surface_with_source_site(&base_surface, point)
                        && !variants.contains(&candidate)
                    {
                        variants.push(candidate);
                    }
                }
                if let Some(comparison_variants) =
                    comparison_program_point_variants(&base_surface, &points)
                {
                    for candidate in comparison_variants {
                        if !variants.contains(&candidate) {
                            variants.push(candidate);
                        }
                    }
                }
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
                    if &actual == expected {
                        return Some((candidate.clone(), actual));
                    }
                    // The certified pair may sit at a snapshot no recorded
                    // point reproduces syntactically; accept a candidate
                    // whose lowering provably transports to the certified
                    // form.
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
                .proof_certificate_builder
                .steps
                .iter()
                .rev()
                .find_map(|step| match step {
                    SimpleProofStep::StepUsing(premises) => Some(Some(premises)),
                    SimpleProofStep::Step => Some(None),
                    _ => None,
                })
                .flatten()
                .and_then(|premises| {
                    premises.iter().find_map(|premise| {
                        let recorded = replay
                            .surface_propositions
                            .surfaces(source)
                            .any(|surface| surface == premise);
                        let entry_form_matches = surface_with_source_site(premise, &step_entry)
                            .ok()
                            .and_then(|candidate| {
                                lower_surface_candidate_at_point(
                                    replay,
                                    &candidate,
                                    available,
                                    parameters,
                                    arguments,
                                    state,
                                    predicate_environment,
                                    click_function_environment,
                                )
                                .ok()
                            })
                            .is_some_and(|lowered| lowered.clone() == source.clone());
                        (recorded || entry_form_matches).then_some(premise.clone())
                    })
                });
            if let Some(surface_source) = &selected_by_preceding_step {
                let target_point = ProgramPointRef {
                    region: step_entry.region.clone(),
                    kind: ProgramPointKind::Exit,
                };
                let surface_target = surface_with_source_site(surface_source, &target_point)
                    .unwrap_or_else(|_| surface_source.clone());
                if let Err(error) = replay
                    .surface_propositions
                    .record_lowering(&surface_target, target)
                {
                    replay.proof_certificate_builder.block(format!(
                        "could not retain the selected statement transport target form: {}",
                        error.message()
                    ));
                }
                return;
            }
            match (find_candidate(source), find_candidate(target)) {
                (
                    Some((surface_source, _)),
                    Some((surface_target, lowered_surface_target)),
                ) if surface_source == surface_target => {
                    if let Err(error) = replay
                        .surface_propositions
                        .record_lowering(&surface_target, &lowered_surface_target)
                    {
                        replay.proof_certificate_builder.block(format!(
                            "could not retain the certified fact transport target form: {}",
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
                            replay.proof_certificate_builder.push_step(SimpleProofStep::TransportUsing {
                                source: surface_source,
                                target: surface_target.clone(),
                                premises,
                            });
                            if let Err(error) = replay
                                .surface_propositions
                                .record_lowering(&surface_target, &lowered_surface_target)
                            {
                                replay.proof_certificate_builder.block(format!(
                                    "could not retain the certified fact transport target form: {}",
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
                                .proof_certificate_builder
                                .steps
                                .iter_mut()
                                .rev()
                                .find_map(|step| match step {
                                    SimpleProofStep::StepUsing(premises) => {
                                        if !premises.contains(&surface_source) {
                                            premises.push(surface_source.clone());
                                        }
                                        Some(true)
                                    }
                                    SimpleProofStep::Step => Some(false),
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
                                    replay.proof_certificate_builder.block(format!(
                                        "could not retain the statement-attached fact transport form: {}",
                                        record_error.message()
                                    ));
                                }
                            } else {
                                replay.proof_certificate_builder.block(fact_transport_planning_failure(
                                    &surface_source,
                                    &surface_target,
                                    &replay.unfolded_predicates,
                                    &error,
                                ));
                            }
                        }
                    }
                }
                _ => replay.proof_certificate_builder.block(format!(
                    "no placement of the comparison operands at the {} recorded program points lowered to the certified fact transport\n  certified source: {source:?}\n  certified target: {target:?}",
                    points.len()
                )),
            }
        }
        (None, Some(ConstructionEvidence::FinishCertifiedFactTransports(_))) => {}
        (
            None,
            Some(ConstructionEvidence::CertifiedPathAssumption {
                occurrence,
                condition,
                value,
                facts,
                ..
            }),
        ) => {
            // Planning records the exact statement-entry point where the
            // branch decision was made. Keep that form here: alternatives
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
                        replay.proof_certificate_builder.block(format!(
                            "could not retain the certified path-condition form: {}",
                            error.message()
                        ));
                        return;
                    }
                }
                Ok(kernel_fact) => {
                    replay.proof_certificate_builder.block(format!(
                        "surface branch condition did not lower to a certified path fact\n  lowered: {kernel_fact:?}\n  certified facts: {facts:?}"
                    ));
                    return;
                }
                Err(error) => {
                    replay.proof_certificate_builder.block(format!(
                        "could not lower the certified path condition: {}",
                        error.message()
                    ));
                    return;
                }
            }
            replay
                .proof_certificate_builder
                .path_choices
                .push(SurfacePathChoice {
                    occurrence: *occurrence,
                    condition,
                    value: *value,
                    tactic_offset: replay.proof_certificate_builder.steps.len(),
                });
        }
        (Some(tactic @ ProofTactic::Have(_)), None) => {
            match ProofCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                Ok(_) => replay
                    .proof_certificate_builder
                    .push_source_tactic(tactic.clone()),
                Err(_) => {
                    // A `have` with a smart body records nothing here. The
                    // `ProofTactic::Have` replay arm generates a simple
                    // certificate for the body once the smart proof has
                    // produced its checked kernel fact, independently replays
                    // it, and pushes it — or fails the tactic.
                }
            }
        }
        (None, Some(ConstructionEvidence::CertifiedFrame(path_derivations))) => {
            let lowered = path_derivations
                .iter()
                .map(|derivations| {
                    check_verification_deadline()?;
                    let mut tactics = Vec::new();
                    let mut premises = Vec::new();
                    let mut path_available = available.to_vec();
                    for fact in derivations
                        .iter()
                        .flat_map(PropositionDerivation::context_premises)
                    {
                        if !path_available.contains(&fact) {
                            path_available.push(fact);
                        }
                    }
                    // A certified frame's derivation contexts are its exact
                    // per-path dependency boundary. Lower against that
                    // boundary rather than the global proof facts: a branch
                    // fact may be named only in the leaf whose derivation
                    // selected it, while unrelated ambient history remains
                    // invisible.
                    for fact in derivations
                        .iter()
                        .flat_map(PropositionDerivation::context_premises)
                    {
                        check_verification_deadline()?;
                        if let Ok(surface) = checked_surface_fact_at_point(
                            replay,
                            &fact,
                            &path_available,
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
                        // A derivation that merely bridges a kernel-minted
                        // load variable to its defining load term is
                        // certified bookkeeping: replay re-mints the same
                        // variable and equation deterministically, so the
                        // generated certificate neither needs nor can name
                        // it as a Click-visible premise.
                        let resolved = crate::kernel::resolve_minted_load_variables(
                            derivation.conclusion(),
                            &replay.effect_facts,
                        );
                        if resolved != *derivation.conclusion()
                            && proposition_is_reflexive_equality(&resolved)
                        {
                            continue;
                        }
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
                        let anchor_point = candidate_points
                            .into_iter()
                            .find(|(_, point_state)| {
                                !memories.is_empty()
                                    && memories.iter().any(|memory| {
                                        memory.has_same_snapshot_markers(point_state.memory())
                                    })
                            })
                            .map(|(point, _)| point);
                        let (conclusion, proof) = lower_surface_atomic_derivation(
                            replay,
                            derivation,
                            None,
                            anchor_point.as_ref(),
                            &path_available,
                            parameters,
                            arguments,
                            state,
                            predicate_environment,
                            click_function_environment,
                        )?;
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
                        &mut replay.proof_certificate_builder.steps,
                        &path_tactics,
                    ) {
                        replay.proof_certificate_builder.block(message);
                    }
                }
                Err(error) => replay.proof_certificate_builder.block(format!(
                    "could not lower contextual frame certificate: {}",
                    error.message()
                )),
            }
        }
        // A frontier-local loop is lowered after its initialization,
        // preservation, and effect certificates have been checked. Recording
        // the source block here would either retain smart defaults or mark
        // the replay blocked before those certificates exist.
        (Some(ProofTactic::Loop(_)), None) => {}
        (Some(tactic), None) => match tactic.class() {
            TacticClass::Simple(_) => replay
                .proof_certificate_builder
                .push_source_tactic(tactic.clone()),
            TacticClass::ControlFlow(_) => {
                match ProofCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                    Ok(_) => replay
                        .proof_certificate_builder
                        .push_source_tactic(tactic.clone()),
                    Err(error) => replay
                        .proof_certificate_builder
                        .block(format!("could not lower control-flow tactic: {error:?}")),
                }
            }
            TacticClass::Smart(_) => {}
        },
        (Some(_), Some(_)) | (None, None) => {
            unreachable!("invalid simple-proof construction operation")
        }
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

fn have_proof_is_smart_simp(proof: &SourceProof) -> bool {
    match proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => true,
        SourceProof::Script(tactics) => matches!(
            tactics.as_slice(),
            [ProofTactic::Simp] | [ProofTactic::SimpUsing(_)]
        ),
        SourceProof::Tactic(SmartTactic::Frame) => false,
    }
}

pub(super) fn smart_simp_unfold_prefix(proof: &SourceProof) -> Option<Vec<String>> {
    if have_proof_is_smart_simp(proof) {
        return Some(Vec::new());
    }
    let SourceProof::Script(tactics) = proof else {
        return None;
    };
    let (last, prefix) = tactics.split_last()?;
    if !matches!(last, ProofTactic::Simp | ProofTactic::SimpUsing(_)) {
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

/// Candidate simple bodies for a smart `have` script: each trailing smart
/// `simp` (including one inside a proof-level `if` case) is replaced by an
/// explicit goal-closing simple tactic. Bounded by construction — one closer
/// choice per `simp` occurrence over a fixed closer set.
fn simple_have_body_candidates(tactics: &[ProofTactic]) -> Vec<Vec<ProofTactic>> {
    const CANDIDATE_LIMIT: usize = 16;
    let mut candidates = match tactics {
        [] => Vec::new(),
        [ProofTactic::If(proof_if)] => {
            let then_candidates = simple_have_body_candidates(&proof_if.then_tactics);
            let else_candidates = simple_have_body_candidates(&proof_if.else_tactics);
            let mut candidates = Vec::new();
            for then_tactics in &then_candidates {
                for else_tactics in &else_candidates {
                    candidates.push(vec![ProofTactic::If(ProofIf {
                        condition: proof_if.condition.clone(),
                        then_tactics: then_tactics.clone(),
                        else_tactics: else_tactics.clone(),
                    })]);
                }
            }
            candidates
        }
        [ProofTactic::Cases(proof_cases)] => {
            let left_candidates = simple_have_body_candidates(&proof_cases.left_tactics);
            let right_candidates = simple_have_body_candidates(&proof_cases.right_tactics);
            let mut candidates = Vec::new();
            for left_tactics in &left_candidates {
                for right_tactics in &right_candidates {
                    candidates.push(vec![ProofTactic::Cases(ProofCases {
                        disjunction: proof_cases.disjunction.clone(),
                        left_tactics: left_tactics.clone(),
                        right_tactics: right_tactics.clone(),
                    })]);
                }
            }
            candidates
        }
        [prefix @ .., ProofTactic::Simp] => [
            ProofTactic::Assumption,
            ProofTactic::Normalize,
            ProofTactic::Left,
            ProofTactic::Right,
        ]
        .into_iter()
        .map(|closer| {
            let mut candidate = prefix.to_vec();
            candidate.push(closer);
            candidate
        })
        .collect(),
        _ => Vec::new(),
    };
    candidates.truncate(CANDIDATE_LIMIT);
    candidates
}

/// Constructs the simple certificate for a mid-execution smart `have` whose
/// body is neither simple nor covered by the `[unfold*, simp]` or smart
/// `apply` lowerings — a `witness`/`choose` prefix before its `simp`, or a
/// proof-level `if` whose cases close by `simp`.
///
/// Every candidate is accepted only when the replay judgment
/// (`prove_have_at_current_point`) proves it AND yields exactly the fact the
/// smart script established. A smart `have` with no accepted candidate fails
/// here instead of silently losing the enclosing proof's expansion.
#[allow(clippy::too_many_arguments)]
pub(super) fn certify_general_smart_have(
    have: &ProofHave,
    fact: &Proposition,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    tactic_index: usize,
    available: &[Proposition],
    transition_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_requires: &[Requirement],
) -> Result<ProofCertificate, ClickError> {
    let SourceProof::Script(tactics) = &have.proof else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart `have` succeeded, but its non-script body has no simple certificate"
        )));
    };
    for candidate_tactics in simple_have_body_candidates(tactics) {
        let candidate = ProofHave {
            proposition: have.proposition.clone(),
            proof: SourceProof::Script(candidate_tactics),
        };
        let Ok(proof) = ProofCertificate::from_proof_tactics(std::slice::from_ref(
            &ProofTactic::Have(candidate.clone()),
        )) else {
            continue;
        };
        let replayed = prove_have_at_current_point(
            &candidate,
            theorem_environment,
            claim_label,
            tactic_index,
            available,
            transition_facts,
            parameters,
            arguments,
            pre_state,
            state,
            program_point_states,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            function_requires,
        );
        if replayed.is_ok_and(|replayed| replayed == *fact) {
            return Ok(proof);
        }
    }
    Err(ClickError::new(format!(
        "`{claim_label}` tactic {tactic_index}: smart `have {}` succeeded, but no simple certificate for its proof body replayed; close each case with explicit simple tactics",
        describe_click_proposition(&have.proposition)
    )))
}

fn have_proof_contains_smart_apply(proof: &SourceProof) -> bool {
    let SourceProof::Script(tactics) = proof else {
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
    plan: &SimpEvidence,
    unfolded_predicates: &[String],
) -> Result<SourceProof, ClickError> {
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
    let proof = match plan {
        SimpEvidence::Assumption => SourceProof::Script(vec![ProofTactic::Assumption]),
        SimpEvidence::Normalize => SourceProof::Script(vec![ProofTactic::Normalize]),
        SimpEvidence::Derivation(derivation) => {
            let (_, proof) = lower_surface_atomic_derivation(
                replay,
                derivation,
                Some(&active_surface_goal),
                None,
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
    };
    if unfolded_predicates.is_empty() {
        return Ok(proof);
    }
    let mut tactics = unfolded_predicates
        .iter()
        .cloned()
        .map(ProofTactic::UnfoldPredicate)
        .collect::<Vec<_>>();
    let SourceProof::Script(suffix) = proof else {
        return Err(ClickError::new(
            "planned smart proof certificate was not a tactic script",
        ));
    };
    tactics.extend(suffix);
    Ok(SourceProof::Script(tactics))
}

/// A restricted-`simp` premise's certificate form is exactly available in
/// the replay-visible fact set; certificates cite it directly.
enum PremiseForm {
    ExactlyAvailable,
}

/// The single construction event for a smart `have`/`simp` at the current
/// proof point: kernel search selects its evidence and the same call writes
/// that evidence as a replayable [`ProofCertificate`]. Search may only succeed
/// through derivations the surface vocabulary can write; there is no retained
/// plan between the two, and no separate lowering pass to disagree with the
/// search that already succeeded.
#[allow(clippy::too_many_arguments)]
pub(super) fn construct_smart_have_certificate(
    replay: &mut TacticReplayState,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    have: &ProofHave,
    claim_label: &str,
    tactic_index: usize,
    unfolded_predicates: &[String],
) -> Result<(Proposition, ProofCertificate), ClickError> {
    let planning_span =
        crate::instrumentation::OperationTiming::new("have", claim_label, "smart have planning");
    let (fact, evidence) = plan_smart_have_at_current_point(
        have,
        claim_label,
        tactic_index,
        available,
        parameters,
        arguments,
        replay.old_reference_state(state),
        state,
        &replay.program_point_states,
        &replay.surface_propositions,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        None,
    )?;
    drop(planning_span);
    let _construction_span = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have certificate construction",
    );
    let certificate = surface_smart_have_certificate(
        replay,
        state,
        available,
        parameters,
        arguments,
        predicate_environment,
        click_function_environment,
        have,
        &evidence,
        unfolded_predicates,
    )?;
    Ok((fact, certificate))
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
    plan: &SimpEvidence,
    unfolded_predicates: &[String],
) -> Result<ProofCertificate, ClickError> {
    let restricted_simp = matches!(
        &have.proof,
        SourceProof::Script(tactics) if matches!(tactics.last(), Some(ProofTactic::SimpUsing(_)))
    );
    let unfolded_available = (restricted_simp && !unfolded_predicates.is_empty())
        .then(|| {
            unfold_available_predicate_facts(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                available,
            )
            .map_err(ClickError::new)
        })
        .transpose()?;
    let restricted_context_available = unfolded_available.as_deref().unwrap_or(available);
    let restricted_resolved = match &have.proof {
        SourceProof::Script(tactics) => tactics.last().and_then(|tactic| match tactic {
            ProofTactic::SimpUsing(simp) => Some(
                simp.premises
                    .iter()
                    .map(|surface| {
                        if let Some(kernel) = replay
                            .surface_propositions
                            .available_kernel(surface, restricted_context_available)
                            .cloned()
                        {
                            return Ok((kernel, PremiseForm::ExactlyAvailable));
                        }
                        let freshly_lowered = lower_point_proposition(
                            surface,
                            &facts_for_restricted_simp_lowering(restricted_context_available),
                            parameters,
                            arguments,
                            replay.old_reference_state(state),
                            state,
                            None,
                            &replay.program_point_states,
                            predicate_environment,
                            click_function_environment,
                        );
                        if let Ok(lowered) = &freshly_lowered
                            && let Some(fact) = restricted_context_available.iter().find(|fact| {
                                *fact == lowered
                                    || condition_polarity_equivalent(fact, lowered)
                            })
                        {
                            return Ok((fact.clone(), PremiseForm::ExactlyAvailable));
                        }
                        if let Ok(lowered) = &freshly_lowered
                            && exact_proper_conjunct_is_available(
                                lowered,
                                restricted_context_available,
                            )
                        {
                            return Ok((lowered.clone(), PremiseForm::ExactlyAvailable));
                        }
                        if let Ok(lowered) = &freshly_lowered
                            && let Some(fact) =
                                exactly_available_fact(
                                    lowered,
                                    restricted_context_available,
                                )
                        {
                            return Ok((fact, PremiseForm::ExactlyAvailable));
                        }
                        if let Ok(lowered) = &freshly_lowered
                            && premise_bridged_by_canonical_name_chain(
                                lowered,
                                restricted_context_available,
                            )
                        {
                            // Canonical load variables are kernel-internal
                            // names; recorded equalities chained through one
                            // are the same user-level fact, and replay closes
                            // over the same chain, so the listed form is
                            // exactly citable.
                            return Ok((lowered.clone(), PremiseForm::ExactlyAvailable));
                        }
                        Err(ClickError::new(match freshly_lowered {
                            Ok(_) => format!(
                                "`simp() using` premise is not in the certified proof context: {}",
                                describe_click_proposition(surface)
                            ),
                            Err(message) => format!(
                                "could not lower `simp() using` premise `{}` while producing its certificate: {message}",
                                describe_click_proposition(surface)
                            ),
                        }))
                    })
                    .collect::<Result<Vec<_>, _>>(),
            ),
            _ => None,
        }),
        _ => None,
    }
    .transpose()?;
    let restricted_available = restricted_resolved.as_ref().map(|resolved| {
        resolved
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>()
    });
    let certificate_available = restricted_available.as_deref().unwrap_or(available);
    let proof = if let (Some(exact), SourceProof::Script(source_tactics)) =
        (restricted_available.as_ref(), &have.proof)
        && let Some(ProofTactic::SimpUsing(simp)) = source_tactics.last()
    {
        let active_surface_goal = if unfolded_predicates.is_empty() {
            have.proposition.clone()
        } else {
            unfold_structural_invariant_proposition(
                predicate_environment,
                &have.proposition,
                unfolded_predicates,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "could not express the restricted smart proof goal after predicate unfolding: {message}"
                ))
            })?
        };
        let explicit_goal = lower_point_proposition(
            &active_surface_goal,
            &facts_for_restricted_simp_lowering(available),
            parameters,
            arguments,
            replay.old_reference_state(state),
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(ClickError::new)?;
        let pairs = exact
            .iter()
            .cloned()
            .zip(simp.premises.iter().cloned())
            .collect::<Vec<_>>();
        let restricted_derivation =
            plan_restricted_simp_goal(&explicit_goal, exact.clone(), &explicit_goal, exact)
                .map_err(ClickError::new)?;
        let explicit = lower_restricted_simp_plan(
            &explicit_goal,
            Some(&active_surface_goal),
            &SimpEvidence::Derivation(restricted_derivation),
            &pairs,
        )?;
        let mut tactics = unfolded_predicates
            .iter()
            .cloned()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.extend(
            pairs
                .iter()
                .filter(|(kernel, _)| {
                    exact_proper_conjunct_is_available(kernel, restricted_context_available)
                })
                .map(|(_, surface)| ProofTactic::Extract(surface.clone())),
        );
        tactics.extend(explicit);
        SourceProof::Script(tactics)
    } else {
        surface_simp_plan_proof(
            replay,
            state,
            certificate_available,
            parameters,
            arguments,
            predicate_environment,
            click_function_environment,
            &have.proposition,
            plan,
            unfolded_predicates,
        )?
    };
    let tactic = ProofTactic::Have(ProofHave {
        proposition: have.proposition.clone(),
        proof,
    });
    ProofCertificate::from_proof_tactics(&[tactic]).map_err(|error| {
        ClickError::new(format!(
            "smart `have` produced an invalid certificate: {error:?}"
        ))
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
) -> Result<Option<ProofCertificate>, ClickError> {
    if !have_proof_contains_smart_apply(&have.proof) {
        return Ok(None);
    }
    let SourceProof::Script(tactics) = &have.proof else {
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
                let SourceProof::Script(lowered) = surface_simp_plan_proof(
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
        proof: SourceProof::Script(surface_tactics),
    });
    let certificate = ProofCertificate::from_proof_tactics(&[tactic]).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart `apply` inside `have` produced an invalid certificate: {error:?}"
        ))
    })?;
    Ok(Some(certificate))
}
