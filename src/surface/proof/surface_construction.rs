use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

#[allow(clippy::too_many_arguments)]
fn checked_surface_fact_in_state_with_assumptions(
    view: ExecutionView<'_>,
    kernel: &Proposition,
    assumptions: &PureFactContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
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
            view.recorded_snapshots,
            spec_definitions,
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
        for recorded in view.surface_propositions.atomic_kernel_facts() {
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
    let resolved_kernel = crate::kernel::resolve_minted_load_variables(kernel, view.effect_facts);
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
            snapshot_indexed_selectors(&resolved_kernel, view.recorded_snapshots);
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
            "synthesized Click fact does not lower to the kernel fact at this proof state\n  Click: `{}`\n  lowered: `{}`\n  kernel: `{}`",
            crate::surface::diagnostics::describe_click_proposition(&candidate),
            crate::surface::proof_diagnostics::render::render_proposition(&lowered),
            crate::surface::proof_diagnostics::render::render_proposition(kernel),
        ))),
        Err(error) => Err(ClickError::new(format!(
            "synthesized Click fact could not be lowered at this proof state\n  Click: `{}`\n  error: {}\n  kernel: `{}`",
            crate::surface::diagnostics::describe_click_proposition(&candidate),
            error.raw_summary(),
            crate::surface::proof_diagnostics::render::render_proposition(kernel),
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
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
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
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
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
    spec_definitions: SpecDefinitions<'_>,
) -> Result<ClickProposition, ClickError> {
    let _qualified_sources =
        super::surface_synthesis::QualifiedSynthesisScope::enter(view.surface_propositions);
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
            view.recorded_snapshots,
            spec_definitions,
        )
        .as_ref()
        .is_ok_and(&fact_is_available)
    };
    // The ordinary inverse synthesis sees C variables, but a proof `match`
    // arm's scalar is a fresh kernel variable. Reconstruct its lexical name
    // only at this selected-premise site. A candidate is accepted solely when
    // scoped lowering recovers an available, matching semantic fact.
    if let Some(bindings) = view.proof_bindings {
        let binding_values = bindings
            .iter()
            .map(|(name, value)| (name.clone(), value.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut names = BTreeMap::<Variable, Option<String>>::new();
        for (name, expression) in bindings.iter() {
            if let ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(variable),
            ))) = expression
            {
                names
                    .entry(*variable)
                    .and_modify(|name| *name = None)
                    .or_insert_with(|| Some(name.clone()));
            }
        }
        let names = names
            .into_iter()
            .filter_map(|(variable, name)| name.map(|name| (variable, name)))
            .collect::<BTreeMap<_, _>>();
        if !names.is_empty() {
            let exact_scoped_candidate = |surface: &ClickProposition| {
                let Ok(resolved) = substitute_click_proposition(surface, &binding_values) else {
                    return false;
                };
                lower_fixed_state_proposition_with_assumptions(
                    &resolved,
                    assumptions,
                    parameters,
                    arguments,
                    view.old_reference_state(state),
                    state,
                    None,
                    view.recorded_snapshots,
                    spec_definitions,
                )
                .is_ok_and(|lowered| lowered == *kernel && fact_is_available(&lowered))
            };
            // A named historical premise can mix an introduced binder with
            // a local's iteration-entry value. Prefer its recorded spelling.
            if let Some(surface) = view.surface_propositions.surfaces(kernel).find(|surface| {
                (proposition_contains_at_expression(surface)
                    || proposition_contains_old_expression(surface))
                    && exact_scoped_candidate(surface)
            }) {
                return Ok(surface.clone());
            }
            if let Some(surface) = synthesize_surface_proposition_with_bound_variable_names(
                kernel, parameters, arguments, state, &names,
            ) && exact_scoped_candidate(&surface)
            {
                return Ok(surface);
            }
            // An immutable old scalar has no memory-load snapshot to index.
            // Try the same bounded source points as snapshot transport, with
            // this scope's lexical binder names. Checking the resolved form
            // must recover the exact available fact at the selected point.
            for (selector, snapshot) in view
                .recorded_snapshots
                .recent(super::smart_closures::MAX_TRANSPORT_SOURCE_POINTS)
            {
                if let Some(surface) = synthesize_surface_proposition_with_bound_variable_names(
                    kernel, parameters, arguments, snapshot, &names,
                ) && let Ok(anchored) = surface_at_snapshot(&surface, selector)
                    && exact_scoped_candidate(&anchored)
                {
                    return Ok(anchored);
                }
            }
        }
    }
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
                spec_definitions,
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
            spec_definitions,
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
    let resolved_kernel = crate::kernel::resolve_minted_load_variables(kernel, view.effect_facts);
    // Load variables represent loads whose snapshots the snapshot index needs;
    // resolve through the registry when no defining fact is in scope, and
    // index points from the load term rather than the kernel variable.
    let resolved_kernel = if &resolved_kernel == kernel {
        crate::kernel::resolve_load_variables_from_registry(kernel)
    } else {
        resolved_kernel
    };
    let (exact_snapshots, compatible_snapshots) =
        snapshot_indexed_selectors(&resolved_kernel, view.recorded_snapshots);
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
                    spec_definitions,
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
                    spec_definitions,
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
                    spec_definitions,
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
                    spec_definitions,
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
            spec_definitions,
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

fn have_proof_is_smart_simp(proof: &SourceProof) -> bool {
    match proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => true,
        SourceProof::Script(tactics) => matches!(
            tactics.as_slice(),
            [ProofTactic::Simp] | [ProofTactic::SimpUsing(_)]
        ),
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
