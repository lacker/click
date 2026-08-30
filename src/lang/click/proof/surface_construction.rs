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

pub(super) fn checked_surface_fact_in_state(
    view: ExecutionView<'_>,
    kernel: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let assumptions = assumptions_from_propositions(available);
    checked_surface_fact_in_state_with_assumptions(
        view,
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
fn checked_surface_fact_in_state_with_assumptions(
    view: ExecutionView<'_>,
    kernel: &Proposition,
    assumptions: &PureFactContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    let check = |surface: &ClickProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            assumptions,
            parameters,
            arguments,
            view.old_reference_state(state),
            state,
            None,
            &view.recorded_snapshots,
            predicate_environment,
            click_function_environment,
        )
        .map_err(ClickError::new)
    };
    if let Ok(surface) = view.surface_propositions.checked_surface(kernel, check) {
        return Ok(surface);
    }
    if let Ok(ClickProposition::Loadable { segment }) = view.surface_propositions.surface(kernel) {
        let mut old_segment = segment.clone();
        old_segment.state = ContractSegmentState::Old;
        let old_candidate = ClickProposition::Loadable {
            segment: old_segment,
        };
        if check(&old_candidate).ok().as_ref() == Some(kernel) {
            return Ok(old_candidate);
        }
    }
    if let Ok(ClickProposition::Defined { expression }) = view.surface_propositions.surface(kernel)
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
        for recorded in view.surface_propositions.kernel_facts() {
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
            }) = view.surface_propositions.surface(recorded)
            else {
                continue;
            };
            for selector in view.recorded_snapshots.keys().rev() {
                let candidate = ClickProposition::PredicateCall {
                    name: surface_name.clone(),
                    arguments: surface_arguments
                        .iter()
                        .map(|argument| ContractExpression::At {
                            selector: selector.clone(),
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
    let resolved_kernel = crate::kernel::resolve_minted_load_variables(kernel, &view.effect_facts);
    // Representative selection can derive facts through load variables
    // whose defining facts are not in this view's effect stream; the
    // registry is the kernel's own record of what each one stands for, and
    // resolving through it is the sanctioned display direction.
    let resolved_kernel =
        if crate::kernel::proposition_mentions_registered_load_variable(&resolved_kernel) {
            crate::kernel::resolve_load_variables_from_registry(&resolved_kernel)
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
    // cell was read from; synthesize it through the selector recorded for
    // that snapshot, so the form stays correct in every later proof state
    // where the certificate is checked, rather than a plain form
    // that is correct only until the cell changes.
    if crate::kernel::proposition_mentions_registered_load_variable(kernel) {
        let (exact_snapshots, compatible_snapshots) =
            snapshot_indexed_selectors(&resolved_kernel, &view.recorded_snapshots);
        for (selector, snapshot_state) in exact_snapshots.iter().chain(&compatible_snapshots) {
            let Some(candidate) = synthesize_surface_proposition(
                &resolved_kernel,
                parameters,
                arguments,
                snapshot_state,
            ) else {
                continue;
            };
            let Ok(anchored) = surface_at_snapshot(&candidate, *selector) else {
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
            "synthesized Click fact does not lower to the kernel fact at this proof state\n  Click: {candidate:?}\n  lowered: {lowered:?}\n  kernel: {kernel:?}"
        ))),
        Err(error) => Err(ClickError::new(format!(
            "synthesized Click fact could not be lowered at this proof state\n  Click: {candidate:?}\n  error: {}\n  kernel: {kernel:?}",
            error.message()
        ))),
    }
}

#[allow(clippy::too_many_arguments)]
fn checked_surface_frame_premise_in_state(
    view: ExecutionView<'_>,
    kernel: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    checked_surface_fact_in_state(
        view,
        kernel,
        available,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    )
    .or_else(|_| {
        // The exact kernel footprint fact can be a snapshot-normalized form
        // of an earlier recorded `old(...)` comparison. The snapshot-blind
        // index recovers only forms in that structural bucket.
        checked_surface_comparison_fact_for_typed_derivation(
            view,
            kernel,
            SurfaceFactMatch::CanonicalExact,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )
    })
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

type SnapshotMatches<'a> = Vec<(&'a SnapshotSelector, &'a CState)>;

pub(super) fn snapshot_indexed_selectors<'a>(
    kernel: &Proposition,
    recorded_snapshots: &'a RecordedSnapshots,
) -> (SnapshotMatches<'a>, SnapshotMatches<'a>) {
    let memories = proposition_snapshot_memories(kernel);
    let mut exact = Vec::new();
    let mut compatible = Vec::new();
    for (selector, state) in recorded_snapshots.iter().rev() {
        if memories.iter().any(|memory| memory == state.memory()) {
            exact.push((selector, state));
        } else if memories
            .iter()
            .any(|memory| memory.has_same_snapshot_markers(state.memory()))
        {
            compatible.push((selector, state));
        }
    }
    (exact, compatible)
}

#[derive(Clone, Copy)]
pub(super) enum SurfaceFactMatch {
    CanonicalExact,
    AvailabilityEquivalent,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn checked_surface_comparison_fact_in_state(
    view: ExecutionView<'_>,
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
    checked_surface_comparison_fact_in_state_with_availability(
        view,
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
pub(super) fn checked_surface_comparison_fact_in_state_with_indexed_facts(
    view: ExecutionView<'_>,
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
    checked_surface_comparison_fact_in_state_with_availability(
        view,
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
    view: ExecutionView<'_>,
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
    checked_surface_comparison_fact_in_state_with_availability(
        view,
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
fn checked_surface_comparison_fact_in_state_with_availability(
    view: ExecutionView<'_>,
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
            |indexed| indexed.available_across_effects(fact, &[]),
        )
    };
    // Candidates below are matched through the permissive candidate lowering
    // (symbolic contract loads allowed), but the emitted certificate is
    // checked by the ordinary executor, whose strict lowering requires every
    // load to be justified. A form that only lowers permissively —
    // for example a snapshot fact whose `at(...)` anchor was dropped so its
    // current-state loads are not provably loadable — must not be emitted.
    let strictly_available = |surface: &ClickProposition| {
        lower_fixed_state_proposition_with_assumptions(
            surface,
            assumptions,
            parameters,
            arguments,
            view.old_reference_state(state),
            state,
            None,
            &view.recorded_snapshots,
            predicate_environment,
            click_function_environment,
        )
        .as_ref()
        .is_ok_and(&fact_is_available)
    };
    // A snapshot-indexed form paired with this exact available kernel fact
    // is checkable through the recorded-snapshot map. Requiring
    // it to lower again against the current heap would incorrectly demand that
    // old loads remain loadable now. Current-state forms do not have that
    // stable anchor and still go through `strictly_available` below.
    let mut recorded_surfaces = view
        .surface_propositions
        .surfaces(kernel)
        .cloned()
        .collect::<Vec<_>>();
    if allow_snapshot_blind_candidates {
        for candidate in view.surface_propositions.snapshot_blind_kernels(kernel) {
            for surface in view.surface_propositions.surfaces(candidate) {
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
        ) && view
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
            && view
                .surface_propositions
                .available_kernel_matching(surface, &fact_is_available)
                .is_some_and(&matches_kernel)
            // A recorded pair can name a program point outside the current
            // view scope (for example a function-prefix statement inside a
            // loop-region proof). The candidate lowering resolves recorded
            // snapshots without demanding current loadability, so it is the
            // right scope check here.
            && lower_surface_candidate_in_state_with_assumptions(
                view,
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
    // correct at every later proof state, while a plain current-state form
    // is correct only until the cell changes: anchored forms are tried first
    // and plain forms last.
    let prefer_anchored = crate::kernel::proposition_mentions_registered_load_variable(kernel);
    if !prefer_anchored
        && let Ok(surface) = checked_surface_fact_in_state_with_assumptions(
            view,
            kernel,
            assumptions,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )
        && strictly_available(&surface)
    {
        return Ok(surface);
    }

    let mut bases = Vec::new();
    for surface in &recorded_surfaces {
        if !bases.contains(surface) {
            bases.push(surface.clone());
        }
    }
    let resolved_kernel = crate::kernel::resolve_minted_load_variables(kernel, &view.effect_facts);
    // Load variables represent loads whose snapshots the snapshot index needs;
    // resolve through the registry when no defining fact is in scope, and
    // index points from the load term rather than the kernel variable.
    let resolved_kernel = if &resolved_kernel == kernel {
        crate::kernel::resolve_load_variables_from_registry(kernel)
    } else {
        resolved_kernel
    };
    let (exact_snapshots, compatible_snapshots) =
        snapshot_indexed_selectors(&resolved_kernel, &view.recorded_snapshots);
    if let Some(surface) =
        synthesize_surface_proposition(&resolved_kernel, parameters, arguments, state)
        && !bases.contains(&surface)
    {
        bases.push(surface);
    }
    for (_, snapshot_state) in exact_snapshots.iter().chain(&compatible_snapshots) {
        if let Some(surface) =
            synthesize_surface_proposition(&resolved_kernel, parameters, arguments, snapshot_state)
            && !bases.contains(&surface)
        {
            bases.push(surface);
        }
    }
    let plain_base_candidate = |bases: &[ClickProposition]| {
        bases
            .iter()
            .find(|base| {
                lower_surface_candidate_in_state_with_assumptions(
                    view,
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
                            && quantified_equivalent_available_fact(
                                kernel,
                                std::slice::from_ref(&lowered),
                            )
                            .is_some()
                }) && strictly_available(base)
            })
            .cloned()
    };
    if !prefer_anchored && let Some(base) = plain_base_candidate(&bases) {
        return Ok(base);
    }
    for (selector, _) in exact_snapshots.iter().chain(&compatible_snapshots) {
        for base in &bases {
            if let Ok(candidate) = surface_at_snapshot(base, *selector)
                && lower_surface_candidate_in_state_with_assumptions(
                    view,
                    &candidate,
                    assumptions,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                )
                .is_ok_and(|lowered| matches_kernel(&lowered))
                && strictly_available(&candidate)
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
            let at_snapshot = |expression: &ContractExpression| ContractExpression::At {
                selector: (*selector).clone(),
                expression: Box::new(expression.clone()),
            };
            let candidates = [
                ClickProposition::Comparison {
                    left: at_snapshot(left),
                    operator: *operator,
                    right: at_snapshot(right),
                },
                ClickProposition::Comparison {
                    left: at_snapshot(left),
                    operator: *operator,
                    right: right.clone(),
                },
                ClickProposition::Comparison {
                    left: left.clone(),
                    operator: *operator,
                    right: at_snapshot(right),
                },
            ];
            for candidate in candidates {
                let lowered = lower_surface_candidate_in_state_with_assumptions(
                    view,
                    &candidate,
                    assumptions,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                );
                if lowered.is_ok_and(|lowered| matches_kernel(&lowered))
                    && strictly_available(&candidate)
                {
                    return Ok(candidate);
                }
            }
        }
    }
    for indexed_snapshots in [&exact_snapshots, &compatible_snapshots] {
        let selectors = indexed_snapshots
            .iter()
            .map(|(selector, _)| (*selector).clone())
            .collect::<Vec<_>>();
        for base in &bases {
            let Some(variants) = comparison_snapshot_variants(base, &selectors) else {
                continue;
            };
            for candidate in variants {
                check_verification_deadline()?;
                if lower_surface_candidate_in_state_with_assumptions(
                    view,
                    &candidate,
                    assumptions,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                )
                .is_ok_and(|lowered| matches_kernel(&lowered))
                    && strictly_available(&candidate)
                {
                    return Ok(candidate);
                }
            }
        }
    }
    if prefer_anchored {
        if let Ok(surface) = checked_surface_fact_in_state_with_assumptions(
            view,
            kernel,
            assumptions,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        ) && strictly_available(&surface)
        {
            return Ok(surface);
        }
        if let Some(base) = plain_base_candidate(&bases) {
            return Ok(base);
        }
    }
    if let Some(exhaustion) = surface_synthesis_exhaustion_description() {
        return Err(ClickError::new(format!(
            "comparison fact has no checked surface form at this proof state: {exhaustion}"
        )));
    }
    Err(ClickError::new(format!(
        "comparison fact has no checkable surface form at this proof state ({} exact and {} compatible recorded snapshots, {} structural bases)",
        exact_snapshots.len(),
        compatible_snapshots.len(),
        bases.len(),
    )))
}

pub(super) struct ProofCertificateConstructionContext<'a> {
    execution: &'a mut ExecutionProofState,
    context: &'a ExecutionProofContext<'a>,
    pub(super) proof_certificate_builder: &'a mut ProofCertificateBuilder,
    /// The predicates unfolded on the execution path being planned for.
    pub(super) unfolded_predicates: &'a [String],
}

impl<'a> ProofCertificateConstructionContext<'a> {
    pub(super) fn new(
        execution: &'a mut ExecutionProofState,
        context: &'a ExecutionProofContext<'a>,
        proof_certificate_builder: &'a mut ProofCertificateBuilder,
        unfolded_predicates: &'a [String],
    ) -> Self {
        Self {
            execution,
            context,
            proof_certificate_builder,
            unfolded_predicates,
        }
    }
}

impl std::ops::Deref for ProofCertificateConstructionContext<'_> {
    type Target = ExecutionProofState;

    fn deref(&self) -> &Self::Target {
        self.execution
    }
}

impl std::ops::DerefMut for ProofCertificateConstructionContext<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.execution
    }
}

/// Lowers checked per-path frame derivations into their exact Surface plans.
///
/// This operation records stable Surface identities in the planning cursor,
/// but it does not build or interpret a certificate. Callers choose whether
/// the returned path-local tactics feed legacy serialization or a typed
/// Proof-owned plan.
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_certified_frame_path_tactics(
    surface_propositions: &mut SurfacePropositionMap,
    frontier: &ExecutionFrontier,
    effect_facts: &[ExecutionPureFact],
    recorded_snapshots: &RecordedSnapshots,
    proof_context: &ExecutionProofContext<'_>,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    path_derivations: &[Vec<PropositionDerivation>],
) -> Result<Vec<Vec<ProofTactic>>, ClickError> {
    path_derivations
        .iter()
        .map(|derivations| {
            check_verification_deadline()?;
            let mut tactics = Vec::new();
            let mut premises = Vec::new();
            let mut surfaced_premise_facts = Vec::new();
            let mut path_available = available.to_vec();
            for fact in derivations
                .iter()
                .flat_map(PropositionDerivation::context_premises)
            {
                if !path_available.contains(&fact) {
                    path_available.push(fact);
                }
            }
            // A certified frame's derivation contexts are its exact per-path
            // dependency boundary. A branch fact may be named only in the
            // leaf whose derivation selected it.
            for fact in derivations
                .iter()
                .flat_map(PropositionDerivation::context_premises)
            {
                check_verification_deadline()?;
                if let Ok(surface) = checked_surface_frame_premise_in_state(
                    ExecutionView::new(
                        frontier,
                        effect_facts,
                        recorded_snapshots,
                        surface_propositions,
                        proof_context.constants.function_entry_state.as_ref(),
                    ),
                    &fact,
                    &path_available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                ) {
                    if !premises.contains(&surface) {
                        premises.push(surface);
                    }
                    if !surfaced_premise_facts.contains(&fact) {
                        surfaced_premise_facts.push(fact);
                    }
                }
            }
            for derivation in derivations {
                check_verification_deadline()?;
                let canonical_conclusion =
                    crate::kernel::canonical_condition_fact(derivation.conclusion());
                // An exact context fact may already be the frame checker's
                // canonical spelling of this planning goal. Naming that
                // Surface premise is sufficient; synthesizing a redundant
                // `have` can erase the old/current snapshot distinction while
                // pretty-printing the canonical kernel form.
                if surfaced_premise_facts.iter().any(|premise| {
                    crate::kernel::canonical_condition_fact(premise) == canonical_conclusion
                }) {
                    continue;
                }
                // Kernel-minted load-variable bridges are deterministic
                // bookkeeping and have no Surface premise to emit.
                let resolved = crate::kernel::resolve_minted_load_variables(
                    derivation.conclusion(),
                    &effect_facts,
                );
                if resolved != *derivation.conclusion()
                    && proposition_is_reflexive_equality(&resolved)
                {
                    continue;
                }
                let memories = c_condition_fact_memories(derivation.conclusion());
                // Prefer the stable function-entry selector. Statement-entry
                // states are transient planning artifacts.
                let mut candidate_snapshots = Vec::new();
                if let Some(entry_state) = &proof_context.constants.function_entry_state {
                    candidate_snapshots.push((
                        SnapshotSelector::ProgramPoint(ProgramPointRef {
                            region: CodeRegionRef::Function,
                            kind: ProgramPointKind::Entry,
                        }),
                        entry_state.clone(),
                    ));
                }
                candidate_snapshots.extend(
                    recorded_snapshots
                        .iter()
                        .rev()
                        .map(|(selector, state)| (selector.clone(), state.clone())),
                );
                let anchor_snapshot = candidate_snapshots
                    .into_iter()
                    .find(|(_, snapshot_state)| {
                        !memories.is_empty()
                            && memories.iter().any(|memory| {
                                memory.has_same_snapshot_markers(snapshot_state.memory())
                            })
                    })
                    .map(|(selector, _)| selector);
                let (conclusion, proof) = lower_surface_atomic_derivation(
                    ExecutionView::new(
                        frontier,
                        effect_facts,
                        recorded_snapshots,
                        surface_propositions,
                        proof_context.constants.function_entry_state.as_ref(),
                    ),
                    derivation,
                    None,
                    anchor_snapshot.as_ref(),
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
            Ok(tactics)
        })
        .collect()
}

/// Constructs the surface step(s) for one planned operation directly into the
/// planning construction's own [`ProofCertificateBuilder`]. This is the plan-time
/// counterpart of the old plan-lowering construction: search commits to a move and
/// immediately records how that move is written in Surface Click, so a smart
/// tactic's result is a [`ProofCertificate`] value rather than a private operation
/// program that must be re-executed to discover its form.
///
/// Premises are written against the builder's construction-visible
/// `certificate_facts`, not the planning executor's own fact set.
pub(super) fn construct_proof_step_for_planned_operation(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    sink: &mut ProofCertificateBuilder,
    state: &CState,
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    environments: ConstructionEnvironments<'_>,
    operation: &ConstructionEvidence,
) {
    let available = std::mem::take(&mut execution.surface_record.certificate_facts);
    let available_facts = available.to_vec();
    {
        // Planner construction runs on a construction context that carries no typed
        // path state; the unfold set only refines a transport-planning
        // diagnostic here.
        let mut context =
            ProofCertificateConstructionContext::new(execution, proof_context, sink, &[]);
        append_proof_step_for_operation(
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
    execution.surface_record.certificate_facts = available;
}

#[allow(clippy::too_many_arguments)]
pub(super) fn append_proof_step_for_operation(
    construction: &mut ProofCertificateConstructionContext<'_>,
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
    if construction.proof_certificate_builder.blocker.is_some() {
        return;
    }
    if let Err(error) = check_verification_deadline() {
        construction
            .proof_certificate_builder
            .block(error.message());
        return;
    }
    match (surface_tactic, internal_operation) {
        (
            None,
            Some(ConstructionEvidence::CertifiedStatementStep {
                planned_transition: Some(planned_transition),
            }),
        ) if !construction
            .proof_certificate_builder
            .lowering_planned_transition
            && construction
                .planned_statement_transitions
                .get(*planned_transition)
                .is_some() =>
        {
            let evidence = construction.planned_statement_transitions[*planned_transition].clone();
            construction
                .proof_certificate_builder
                .lowering_planned_transition = true;
            append_proof_step_for_operation(
                construction,
                state,
                available,
                function_block,
                parameters,
                arguments,
                predicate_environment,
                click_function_environment,
                None,
                Some(&ConstructionEvidence::CertifiedStatementStep {
                    planned_transition: None,
                }),
                None,
            );
            construction
                .proof_certificate_builder
                .lowering_planned_transition = false;
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
                let surface = construction
                    .surface_propositions
                    .surface(&transport.target)
                    .ok()
                    .cloned()
                    .or_else(|| {
                        post_state.and_then(|state| {
                            synthesize_surface_proposition(
                                &crate::kernel::resolve_minted_load_variables(
                                    &transport.target,
                                    &construction.execution.core.effect_facts,
                                ),
                                parameters,
                                arguments,
                                state,
                            )
                        })
                    });
                let Some(surface) = surface else {
                    construction.proof_certificate_builder.block(format!(
                        "statement-local frame witness has no checked surface form: {:?}",
                        transport.target
                    ));
                    continue;
                };
                construction
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
                    let Ok(lowered) = lower_surface_candidate_in_state(
                        construction.view(construction.context),
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
                    if let Err(error) = construction
                        .surface_propositions
                        .record_lowering(&surface, &lowered)
                    {
                        construction.proof_certificate_builder.block(format!(
                            "public opaque-call result fact has no stable surface form: {}",
                            error.message()
                        ));
                        continue;
                    }
                    emitted.push(surface.clone());
                    construction
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
        ) if !construction
            .proof_certificate_builder
            .lowering_planned_transition
            && construction
                .planned_statement_transitions
                .get(*planned_transition)
                .is_some() =>
        {
            construction
                .proof_certificate_builder
                .lowering_planned_transition = true;
            append_proof_step_for_operation(
                construction,
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
            construction
                .proof_certificate_builder
                .lowering_planned_transition = false;
        }
        (None, Some(ConstructionEvidence::CertifiedStatementStep { .. })) => {
            construction.proof_certificate_builder.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Statement(
                    construction.execution.core.frontier.next_statement_index,
                ),
                kind: ProgramPointKind::Entry,
            });
            construction
                .proof_certificate_builder
                .push_step(ProofStep::Step);
        }
        (
            None,
            Some(ConstructionEvidence::CertifiedLoopSummaryStep {
                prerequisite_derivations: derivations,
                exact_premises,
                ..
            }),
        ) => {
            let loop_index = construction
                .context
                .constants
                .source_layout
                .statement(construction.execution.core.frontier.next_statement_index)
                .and_then(|region| match region.kind {
                    SourceStatementKind::Loop { loop_index } => Some(loop_index),
                    SourceStatementKind::Plain | SourceStatementKind::If { .. } => None,
                });
            let Some(loop_index) = loop_index else {
                construction
                    .proof_certificate_builder
                    .block("certified loop-summary construction is not at a source loop entry");
                return;
            };
            construction.proof_certificate_builder.last_step_entry = Some(ProgramPointRef {
                region: CodeRegionRef::Statement(
                    construction.execution.core.frontier.next_statement_index,
                ),
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
                            construction
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
                                    let source_selector = predicate_call_snapshot_selector(surface);
                                    let definition = predicate_environment.get(surface_name)?;
                                    let mut surface = instantiate_click_predicate_definition(
                                        definition,
                                        surface_arguments,
                                    )
                                    .ok()?;
                                    if let Some(selector) = source_selector {
                                        surface = surface_at_snapshot(&surface, &selector).ok()?;
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
                        if construction
                            .surface_propositions
                            .record_lowering(&surface, &kernel)
                            .is_err()
                        {
                            continue;
                        }
                    }
                    construction
                        .proof_certificate_builder
                        .push_step(ProofStep::UnfoldPredicate(name));
                }
                let current_loadable_haves = surface_available
                    .iter()
                    .filter_map(|kernel| {
                        if !matches!(kernel, Proposition::CMemoryLoadable { .. }) {
                            return None;
                        }
                        let ClickProposition::Loadable { segment } =
                            construction.surface_propositions.surface(kernel).ok()?
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
                    let Ok((fact, plan)) = plan_smart_have_in_current_state(
                        &have,
                        "surface loop-summary certificate",
                        0,
                        &surface_available,
                        parameters,
                        arguments,
                        construction
                            .context
                            .old_reference_state(&construction.execution.core.frontier, state),
                        state,
                        &construction.recorded_snapshots,
                        &construction.surface_propositions,
                        predicate_environment,
                        click_function_environment,
                        &[],
                        None,
                    ) else {
                        continue;
                    };
                    if construction
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
                        construction.view(construction.context),
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
                        Ok(certificate) => construction
                            .proof_certificate_builder
                            .steps
                            .extend(certificate.steps().iter().cloned()),
                        Err(error) => construction
                            .proof_certificate_builder
                            .block(error.message()),
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
                    let planned = plan_smart_have_in_current_state(
                        &have,
                        "surface loop-summary certificate",
                        0,
                        &surface_available,
                        parameters,
                        arguments,
                        construction
                            .context
                            .old_reference_state(&construction.execution.core.frontier, state),
                        state,
                        &construction.recorded_snapshots,
                        &construction.surface_propositions,
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
                        if let Err(error) = construction
                            .surface_propositions
                            .record_lowering(&have.proposition, &fact)
                        {
                            construction.proof_certificate_builder.block(format!(
                                "could not record a loop invariant for its surface certificate: {}",
                                error.message()
                            ));
                            return;
                        }
                        match surface_smart_have_certificate(
                            construction.view(construction.context),
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
                            Ok(certificate) => construction
                                .proof_certificate_builder
                                .steps
                                .extend(certificate.steps().iter().cloned()),
                            Err(error) => construction
                                .proof_certificate_builder
                                .block(error.message()),
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
                    construction.view(construction.context),
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
                    construction
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
            let contextual_step = |view: ExecutionView<'_>, needed: &[Proposition]| {
                let normalized_needed = needed
                    .iter()
                    .map(|fact| (fact, normalize_proposition(fact), fact.clone()))
                    .collect::<Vec<_>>();
                let mut premises = Vec::new();
                for (fact, normalized, materialized) in normalized_needed {
                    let check_candidate = |available_fact: &Proposition| {
                        checked_surface_comparison_fact_in_state(
                            view,
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
            let premises = contextual_step(construction.view(construction.context), &needed).map(
                |mut premises| {
                    for (_, surface) in &loop_summary_premises {
                        if !premises.contains(surface) {
                            premises.push(surface.clone());
                        }
                    }
                    premises
                },
            );
            construction.proof_certificate_builder.block(match premises {
                Ok(_) => "a detached loop-summary certificate has no surface form; use a frontier-local `loop { ... }` tactic".to_string(),
                Err(error) => format!(
                    "could not express a loop-summary premise at the current proof state: {}",
                    error.message()
                ),
            });
        }
        (None, Some(ConstructionEvidence::CertifiedFactTransport { source, target, .. })) => {
            // A load-variable defining equation has no user-visible form;
            // its transported form at the new snapshot is itself certified
            // by construction, so expansion
            // needs no explicit step for it.
            if crate::kernel::is_load_variable_defining_fact(source)
                && crate::kernel::is_load_variable_defining_fact(target)
            {
                return;
            }
            let Some(step_entry) = construction
                .proof_certificate_builder
                .last_step_entry
                .clone()
            else {
                construction
                    .proof_certificate_builder
                    .block("fact transport has no preceding statement-entry snapshot");
                return;
            };
            let transport_assumptions = assumptions_from_propositions(available);
            let mut base_surfaces = Vec::new();
            for proposition in [source, target] {
                for surface in construction.surface_propositions.surfaces(proposition) {
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
                for recorded in construction.surface_propositions.kernel_facts() {
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
                                    &construction.execution.core.effect_facts,
                                )
                            }));
                    if !matches {
                        continue;
                    }
                    for surface in construction.surface_propositions.surfaces(recorded) {
                        if !base_surfaces.contains(surface) {
                            base_surfaces.push(surface.clone());
                        }
                    }
                }
            }
            if base_surfaces.is_empty() {
                construction.proof_certificate_builder.block(format!(
                    "fact transport has no recorded or synthesized Click comparison form\n  source: {source:?}\n  target: {target:?}"
                ));
                return;
            }
            let mut selectors = construction
                .recorded_snapshots
                .keys()
                .cloned()
                .collect::<Vec<_>>();
            let step_entry = SnapshotSelector::ProgramPoint(step_entry);
            if !selectors.contains(&step_entry) {
                selectors.push(step_entry);
            }
            let mut candidates = Vec::new();
            for base_surface in base_surfaces {
                let mut variants = vec![base_surface.clone()];
                for selector in &selectors {
                    if let Ok(candidate) = surface_at_snapshot(&base_surface, selector)
                        && !variants.contains(&candidate)
                    {
                        variants.push(candidate);
                    }
                }
                if let Some(comparison_variants) =
                    comparison_snapshot_variants(&base_surface, &selectors)
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
                    lower_surface_candidate_in_state(
                        construction.view(construction.context),
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
                    // The certified pair may sit at a snapshot that no
                    // recorded selector reproduces syntactically; accept a candidate
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
                            &construction.execution.core.effect_facts,
                        )
                    {
                        return Some((candidate.clone(), actual));
                    }
                }
                None
            };
            match (find_candidate(source), find_candidate(target)) {
                (
                    Some((surface_source, _)),
                    Some((surface_target, lowered_surface_target)),
                ) if surface_source == surface_target => {
                    if let Err(error) = construction
                        .surface_propositions
                        .record_lowering(&surface_target, &lowered_surface_target)
                    {
                        construction.proof_certificate_builder.block(format!(
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
                        fact_transport_transition_facts(&construction.execution.core.effect_facts, &lowered_surface_source);
                    match plan_explicit_fact_transport(
                        &surface_source,
                        &lowered_surface_source,
                        &lowered_surface_target,
                        available,
                        &transition_facts,
                        parameters,
                        arguments,
                        construction.view(construction.context),
                        state,
                        predicate_environment,
                        click_function_environment,
                    ) {
                        Ok(premises) => {
                            construction.proof_certificate_builder.push_step(ProofStep::TransportUsing {
                                source: surface_source,
                                target: surface_target.clone(),
                                premises,
                            });
                            if let Err(error) = construction
                                .surface_propositions
                                .record_lowering(&surface_target, &lowered_surface_target)
                            {
                                construction.proof_certificate_builder.block(format!(
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
                            // Selected transport checks it as part of the
                            // statement certificate itself.
                            let attached = construction
                                .proof_certificate_builder
                                .steps
                                .iter_mut()
                                .rev()
                                .find_map(|step| match step {
                                    ProofStep::Step => Some(false),
                                    _ => None,
                                })
                                .unwrap_or(false);
                            if attached {
                                if let Err(record_error) = construction
                                    .surface_propositions
                                    .record_lowering(&surface_source, &lowered_surface_source)
                                    .and_then(|()| {
                                        construction.surface_propositions.record_lowering(
                                            &surface_target,
                                            &lowered_surface_target,
                                        )
                                    })
                                {
                                    construction.proof_certificate_builder.block(format!(
                                        "could not retain the statement-attached fact transport form: {}",
                                        record_error.message()
                                    ));
                                }
                            } else {
                                construction.proof_certificate_builder.block(fact_transport_planning_failure(
                                    &surface_source,
                                    &surface_target,
                                    construction.unfolded_predicates,
                                    &error,
                                ));
                            }
                        }
                    }
                }
                _ => construction.proof_certificate_builder.block(format!(
                    "no placement of the comparison operands at the {} recorded snapshots lowered to the certified fact transport\n  certified source: {source:?}\n  certified target: {target:?}",
                    selectors.len()
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
            // can construction without their common statement-step prefix, so a
            // transient "last step" pointer is not a reliable anchor.
            let condition = condition.clone();
            let surface_fact = if *value {
                condition.clone()
            } else {
                negate_click_proposition(&condition)
            };
            let lowered = lower_surface_candidate_in_state(
                construction.view(construction.context),
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
                    if let Err(error) = construction
                        .surface_propositions
                        .record_lowering(&surface_fact, certified_fact)
                    {
                        construction.proof_certificate_builder.block(format!(
                            "could not retain the certified path-condition form: {}",
                            error.message()
                        ));
                        return;
                    }
                }
                Ok(kernel_fact) => {
                    construction.proof_certificate_builder.block(format!(
                        "surface branch condition did not lower to a certified path fact\n  lowered: {kernel_fact:?}\n  certified facts: {facts:?}"
                    ));
                    return;
                }
                Err(error) => {
                    construction.proof_certificate_builder.block(format!(
                        "could not lower the certified path condition: {}",
                        error.message()
                    ));
                    return;
                }
            }
            construction
                .proof_certificate_builder
                .path_choices
                .push(SurfacePathChoice {
                    occurrence: *occurrence,
                    condition,
                    value: *value,
                    tactic_offset: construction.proof_certificate_builder.steps.len(),
                });
        }
        (Some(tactic @ ProofTactic::Have(_)), None) => {
            match ProofCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                Ok(_) => construction
                    .proof_certificate_builder
                    .push_source_tactic(tactic.clone()),
                Err(_) => {
                    // A `have` with a smart body records nothing here. The
                    // `ProofTactic::Have` construction arm generates a simple
                    // certificate for the body once the smart proof has
                    // produced its checked kernel fact, independently checks
                    // it, and pushes it — or fails the tactic.
                }
            }
        }
        // A frontier-local loop is lowered after its initialization,
        // preservation, and effect certificates have been checked. Recording
        // the source block here would either retain smart defaults or mark
        // the construction blocked before those certificates exist.
        (Some(ProofTactic::Loop(_)), None) => {}
        (Some(tactic), None) => match tactic.class() {
            TacticClass::Simple(_) => construction
                .proof_certificate_builder
                .push_source_tactic(tactic.clone()),
            TacticClass::ControlFlow(_) => {
                match ProofCertificate::from_proof_tactics(std::slice::from_ref(tactic)) {
                    Ok(_) => construction
                        .proof_certificate_builder
                        .push_source_tactic(tactic.clone()),
                    Err(error) => construction
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

#[allow(clippy::too_many_arguments)]
pub(super) fn surface_simp_plan_proof(
    view: ExecutionView<'_>,
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
                view,
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
/// the construction-visible fact set; certificates cite it directly.
enum PremiseForm {
    ExactlyAvailable,
}

/// Selects a Surface-expressible operation plan for a smart `have`/`simp` at
/// the current proof state. The caller must apply this plan to `Proof`; the
/// planner result itself has no semantic authority.
#[allow(clippy::too_many_arguments)]
pub(super) fn construct_smart_have_plan(
    view: ExecutionView<'_>,
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
) -> Result<(Proposition, SourceProof), ClickError> {
    let planning_span =
        crate::instrumentation::OperationTiming::new("have", claim_label, "smart have planning");
    let (fact, evidence) = plan_smart_have_in_current_state(
        have,
        claim_label,
        tactic_index,
        available,
        parameters,
        arguments,
        view.old_reference_state(state),
        state,
        &view.recorded_snapshots,
        &view.surface_propositions,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        None,
    )?;
    drop(planning_span);
    let _construction_span = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have operation materialization",
    );
    let proof = surface_smart_have_proof(
        view,
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
    Ok((fact, proof))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn surface_smart_have_proof(
    view: ExecutionView<'_>,
    state: &CState,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    have: &ProofHave,
    plan: &SimpEvidence,
    unfolded_predicates: &[String],
) -> Result<SourceProof, ClickError> {
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
                        if let Some(kernel) = view
                            .surface_propositions
                            .available_kernel(surface, restricted_context_available)
                            .cloned()
                        {
                            return Ok((kernel, PremiseForm::ExactlyAvailable));
                        }
                        let freshly_lowered = lower_fixed_state_proposition(
                            surface,
                            &facts_for_restricted_simp_lowering(restricted_context_available),
                            parameters,
                            arguments,
                            view.old_reference_state(state),
                            state,
                            None,
                            &view.recorded_snapshots,
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
                            && premise_bridged_by_load_variable_chain(
                                lowered,
                                restricted_context_available,
                            )
                        {
                            // Load variables are kernel-internal
                            // names; recorded equalities chained through one
                            // are the same user-level fact, and view closes
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
        let explicit_goal = lower_fixed_state_proposition(
            &active_surface_goal,
            &facts_for_restricted_simp_lowering(available),
            parameters,
            arguments,
            view.old_reference_state(state),
            state,
            None,
            &view.recorded_snapshots,
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
            view,
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
    Ok(proof)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn surface_smart_have_certificate(
    view: ExecutionView<'_>,
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
    let proof = surface_smart_have_proof(
        view,
        state,
        available,
        parameters,
        arguments,
        predicate_environment,
        click_function_environment,
        have,
        plan,
        unfolded_predicates,
    )?;
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
