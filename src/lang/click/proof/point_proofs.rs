use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn apply_theorem_at_current_point(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    tactic_index: usize,
    available: Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    lowering_context: Option<&[Proposition]>,
) -> Result<Vec<Proposition>, ClickError> {
    let values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        pre_state,
        post_state: state,
        result: None,
        program_point_states,
    };
    let available = apply_theorem_applications_to_available_with_lowering_context(
        theorem_environment,
        &[(tactic_index, application.clone())],
        claim_label,
        None,
        available,
        lowering_context,
        &context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    Ok(available)
}

#[allow(clippy::too_many_arguments)]
fn lower_theorem_application_requirements(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    premises: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, String> {
    let theorem = theorem_environment
        .get(&application.name)
        .ok_or_else(|| format!("unknown theorem `{}`", application.name))?;
    let assumptions = assumptions_from_propositions(premises);
    let (values, array_refs) = theorem_application_bindings(
        theorem,
        application,
        context,
        &assumptions,
        predicate_environment,
        click_function_environment,
    )?;
    let mut lowerer = KernelPropositionLowerer::new(
        values,
        array_refs,
        context.post_state.memory().clone(),
        predicate_environment,
        click_function_environment,
    );
    theorem
        .requires()
        .iter()
        .map(|requirement| {
            let requirement = requirement.proposition().ok_or_else(|| {
                format!(
                    "theorem `{}` has a non-proposition requirement",
                    theorem.name()
                )
            })?;
            let lowered = lowerer
                .lower_requirement_proposition(requirement)
                .map_err(|error| error.message().to_string())?;
            unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &lowered,
                &assumptions,
            )
            .map(|lowered| normalize_direct_atomic_memory_loads(&lowered))
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn plan_explicit_theorem_application(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    replay: &TacticReplayState,
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<ClickProposition>, ClickError> {
    let pre_state = replay.old_reference_state(state);
    let values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        pre_state,
        post_state: state,
        result: None,
        program_point_states: &replay.program_point_states,
    };
    let requirements = lower_theorem_application_requirements(
        theorem_environment,
        application,
        &context,
        available,
        predicate_environment,
        click_function_environment,
        &replay.unfolded_predicates,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower theorem requirements: {message}"
        ))
    })?;
    let mut lowering_facts = available.to_vec();
    append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
    let mut selected = Vec::new();
    for requirement in requirements {
        if matches!(normalize_proposition(&requirement), SimpProposition::True) {
            continue;
        }
        let matched = materialization_equivalent_available_fact(&requirement, available)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "theorem application `{}` requires an unavailable exact premise: {requirement:?}",
                    application.name
                ))
            })?;
        let surface = checked_surface_comparison_fact_at_point(
            replay,
            &matched,
            SurfaceFactMatch::CanonicalExact,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "theorem application `{}` has no checked Click spelling for exact premise `{requirement:?}`: {}",
                application.name,
                error.message(),
            ))
        })?;
        let lowered = lower_point_proposition(
            &surface,
            &lowering_facts,
            parameters,
            arguments,
            pre_state,
            state,
            None,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "theorem application `{}` could not check premise `{}`: {message}",
                application.name,
                describe_click_proposition(&surface),
            ))
        })?;
        if materialization_equivalent_available_fact(&lowered, available).is_none() {
            return Err(ClickError::new(format!(
                "theorem application `{}` synthesized a premise that is not exactly available\n  Click: {}\n  lowered: {lowered:?}\n  required: {requirement:?}",
                application.name,
                describe_click_proposition(&surface),
            )));
        }
        if !selected
            .iter()
            .any(|(_, selected_surface)| selected_surface == &surface)
        {
            selected.push((matched, surface));
        }
    }
    let application_replays = |selected: &[(Proposition, ClickProposition)]| {
        let mut lowering_facts = available.to_vec();
        append_resource_context_observable_facts(state.resources(), &mut lowering_facts);
        let mut explicit_premises = Vec::new();
        for (_, surface) in selected {
            let premise = if let Some(recorded) = replay
                .surface_propositions
                .available_kernel(surface, available)
            {
                recorded.clone()
            } else {
                let Ok(premise) = lower_point_proposition(
                    surface,
                    &lowering_facts,
                    parameters,
                    arguments,
                    pre_state,
                    state,
                    None,
                    &replay.program_point_states,
                    predicate_environment,
                    click_function_environment,
                ) else {
                    return Err(ClickError::new(format!(
                        "could not lower explicit premise `{}`",
                        describe_click_proposition(surface),
                    )));
                };
                premise
            };
            if !exact_fact_is_available(&premise, available)
                && materialization_equivalent_available_fact(&premise, available).is_none()
            {
                return Err(ClickError::new(format!(
                    "explicit premise `{}` did not lower to an available fact: {premise:?}",
                    describe_click_proposition(surface),
                )));
            }
            if !explicit_premises.contains(&premise) {
                explicit_premises.push(premise);
            }
        }
        apply_theorem_at_current_point(
            theorem_environment,
            application,
            claim_label,
            tactic_index,
            explicit_premises,
            parameters,
            arguments,
            pre_state,
            state,
            &replay.program_point_states,
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
            Some(&lowering_facts),
        )
    };
    if let Err(error) = application_replays(&selected) {
        return Err(ClickError::new(format!(
            "theorem application `{}` did not replay from its exact synthesized premises: {}\n  premises: {}",
            application.name,
            error.message(),
            selected
                .iter()
                .map(|(kernel, surface)| format!(
                    "{} => {kernel:?}",
                    describe_click_proposition(surface)
                ))
                .collect::<Vec<_>>()
                .join("\n            "),
        )));
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn checked_surface_fact_at_outcome(
    replay: &TacticReplayState,
    kernel: &Proposition,
    match_kind: SurfaceFactMatch,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickProposition, ClickError> {
    check_verification_deadline()?;
    let lowering_facts = facts_for_smart_have_lowering(available);
    let check = |surface: &ClickProposition| {
        lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            &lowering_facts,
            surface,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
        .map_err(ClickError::new)
    };
    let matches_kernel = |lowered: &Proposition| {
        if matches!(match_kind, SurfaceFactMatch::CanonicalExact) {
            return condition_polarity_equivalent(lowered, kernel);
        }
        condition_polarity_equivalent(
            &normalize_direct_atomic_memory_loads(lowered),
            &normalize_direct_atomic_memory_loads(kernel),
        ) || materialization_equivalent_available_fact(
            &normalize_direct_atomic_memory_loads(kernel),
            std::slice::from_ref(&normalize_direct_atomic_memory_loads(lowered)),
        )
        .is_some()
            || quantified_replay_equivalent_available_fact(kernel, std::slice::from_ref(lowered))
                .is_some()
    };
    // Recorded source spellings are the cheapest exact candidates and cover
    // ordinary premises. Check them before synthesizing variants at every
    // retained program point; an ambiguous spelling simply fails `check` and
    // falls through to the point-qualified search below.
    if let Ok(surface) = replay.surface_propositions.checked_surface(kernel, check) {
        return Ok(surface);
    }
    let (exact_points, compatible_points) =
        snapshot_indexed_program_points(kernel, &replay.program_point_states);
    for (point, point_state) in exact_points.iter().chain(&compatible_points) {
        check_verification_deadline()?;
        let Some(base) = synthesize_surface_proposition(kernel, parameters, arguments, point_state)
        else {
            continue;
        };
        let Some(variants) = comparison_program_point_variants(&base, std::slice::from_ref(*point))
        else {
            continue;
        };
        for candidate in variants {
            check_verification_deadline()?;
            if check(&candidate).is_ok_and(|lowered| matches_kernel(&lowered)) {
                return Ok(candidate);
            }
        }
    }
    let mut bases = Vec::new();
    if let Ok(surface) = replay.surface_propositions.surface(kernel) {
        bases.push(surface.clone());
    }
    for recorded in replay.surface_propositions.kernel_facts() {
        check_verification_deadline()?;
        // The quantifier-shape test is checked first on purpose: it is the
        // weaker of the two conditions, so whenever it holds the mutual
        // `derive_simp_proposition` search below is redundant — and on nested
        // quantified predicate bodies that search costs minutes.
        if (matches!(
            (kernel, recorded),
            (Proposition::ForAll { .. }, Proposition::ForAll { .. })
        ) || quantified_replay_equivalent_available_fact(
            kernel,
            std::slice::from_ref(recorded),
        )
        .is_some())
            && let Ok(surface) = replay.surface_propositions.surface(recorded)
            && !bases.contains(surface)
        {
            bases.push(surface.clone());
        }
    }
    if let Some(surface) = synthesize_surface_proposition(kernel, parameters, arguments, post_state)
        && !bases.contains(&surface)
    {
        bases.push(surface);
    }
    let points = exact_points
        .iter()
        .chain(&compatible_points)
        .map(|(point, _)| (*point).clone())
        .collect::<Vec<_>>();
    for indexed_points in [&exact_points, &compatible_points] {
        let indexed_points = indexed_points
            .iter()
            .map(|(point, _)| (*point).clone())
            .collect::<Vec<_>>();
        for base in &bases {
            check_verification_deadline()?;
            let Some(variants) = comparison_program_point_variants(base, &indexed_points) else {
                continue;
            };
            for candidate in variants {
                check_verification_deadline()?;
                if check(&candidate).is_ok_and(|lowered| matches_kernel(&lowered)) {
                    return Ok(candidate);
                }
            }
        }
    }
    for (point, point_state) in exact_points.iter().chain(&compatible_points) {
        check_verification_deadline()?;
        let Some(base) = synthesize_surface_proposition(kernel, parameters, arguments, point_state)
        else {
            continue;
        };
        let Some(variants) = comparison_program_point_variants(&base, std::slice::from_ref(*point))
        else {
            continue;
        };
        for candidate in variants {
            check_verification_deadline()?;
            if check(&candidate).is_ok_and(|lowered| matches_kernel(&lowered)) {
                return Ok(candidate);
            }
        }
    }
    // A drain that unfolds predicates unfolds its ambient facts too, and the
    // unfolded body of an opaque predicate is not itself a recorded fact, so
    // it has no spelling of its own. Unfold a spelling of the FOLDED fact at
    // the surface instead — the same rewrite the script's `unfold(...)`
    // performs — and let the round trip below decide whether the result is the
    // fact we were asked for.
    if matches!(
        kernel,
        Proposition::ForAll { .. } | Proposition::Exists { .. }
    ) && !replay.unfolded_predicates.is_empty()
    {
        // A drain that unfolds an ambient predicate replaces the folded fact
        // with its quantified body, so the body can carry a recorded folded
        // spelling while no Predicate fact survives in `available` for the
        // loop below to start from. Unfold that recorded spelling at the
        // surface and let the round trip decide.
        let mut kernel_folded_bases = Vec::new();
        for surface in replay.surface_propositions.surfaces(kernel) {
            if matches!(surface, ClickProposition::PredicateCall { .. })
                && !kernel_folded_bases.contains(surface)
            {
                kernel_folded_bases.push(surface.clone());
            }
        }
        for base in &kernel_folded_bases {
            check_verification_deadline()?;
            let Some(variants) = comparison_program_point_variants(base, &points) else {
                continue;
            };
            for candidate in variants {
                check_verification_deadline()?;
                let Ok(unfolded) = unfold_structural_invariant_proposition(
                    predicate_environment,
                    &candidate,
                    &replay.unfolded_predicates,
                ) else {
                    continue;
                };
                if unfolded == candidate {
                    continue;
                }
                if check(&unfolded).is_ok_and(|lowered| {
                    matches_kernel(&lowered)
                        || nested_quantified_binder_equivalent(&lowered, kernel, 8)
                }) {
                    return Ok(unfolded);
                }
            }
        }
        for fact in available {
            check_verification_deadline()?;
            if !matches!(fact, Proposition::Predicate { .. }) {
                continue;
            }
            let mut folded_bases = Vec::new();
            for surface in replay.surface_propositions.surfaces(fact) {
                if !folded_bases.contains(surface) {
                    folded_bases.push(surface.clone());
                }
            }
            let (folded_exact_points, folded_compatible_points) =
                snapshot_indexed_program_points(fact, &replay.program_point_states);
            for state in std::iter::once(post_state).chain(
                folded_exact_points
                    .iter()
                    .chain(&folded_compatible_points)
                    .map(|(_, state)| *state),
            ) {
                check_verification_deadline()?;
                if let Some(surface) =
                    synthesize_surface_proposition(fact, parameters, arguments, state)
                    && !folded_bases.contains(&surface)
                {
                    folded_bases.push(surface);
                }
            }
            for base in &folded_bases {
                check_verification_deadline()?;
                let Some(variants) = comparison_program_point_variants(base, &points) else {
                    continue;
                };
                for candidate in variants {
                    check_verification_deadline()?;
                    let Ok(unfolded) = unfold_structural_invariant_proposition(
                        predicate_environment,
                        &candidate,
                        &replay.unfolded_predicates,
                    ) else {
                        continue;
                    };
                    if unfolded == candidate {
                        continue;
                    }
                    if check(&unfolded).is_ok_and(|lowered| {
                        matches_kernel(&lowered)
                            || nested_quantified_binder_equivalent(&lowered, kernel, 8)
                    }) {
                        return Ok(unfolded);
                    }
                }
            }
        }
    }
    let surface = synthesize_surface_proposition(kernel, parameters, arguments, post_state)
        .ok_or_else(|| {
            ClickError::new(surface_synthesis_failure(
                "no checked Click spelling for post-execution fact",
                kernel,
            ))
        })?;
    if matches_kernel(&check(&surface)?) {
        Ok(surface)
    } else {
        Err(ClickError::new(format!(
            "synthesized post-execution spelling did not lower to {kernel:?}"
        )))
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn apply_theorem_using_at_outcome(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    surface_premises: &[ClickProposition],
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let mut lowering_available = available.clone();
    append_resource_context_observable_facts(post_state.resources(), &mut lowering_available);
    let mut explicit_premises = Vec::new();
    for surface_premise in surface_premises {
        let premise = lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            &lowering_available,
            surface_premise,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `apply using` premise: {message}"
            ))
        })?;
        if !exact_fact_is_available(&premise, &available)
            && materialization_equivalent_available_fact(&premise, &available).is_none()
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: `apply using` requires an exact post-execution premise: {premise:?}"
            )));
        }
        if !explicit_premises.contains(&premise) {
            explicit_premises.push(premise);
        }
    }
    let values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let application_context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        pre_state,
        post_state,
        result: Some(result),
        program_point_states: &replay.program_point_states,
    };
    let mut applied = apply_theorem_applications_to_available_with_lowering_context(
        theorem_environment,
        &[(tactic_index, application.clone())],
        claim_label,
        Some(path_index),
        explicit_premises,
        Some(&lowering_available),
        &application_context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    for fact in available {
        if !applied.contains(&fact) {
            applied.push(fact);
        }
    }
    Ok(applied)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn plan_explicit_theorem_application_at_outcome(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<ClickProposition>, ClickError> {
    let candidates = available
        .iter()
        .filter_map(|kernel| {
            checked_surface_fact_at_outcome(
                replay,
                kernel,
                SurfaceFactMatch::ReplayEquivalent,
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
    let application_replays = |selected: &[(Proposition, ClickProposition)]| {
        apply_theorem_using_at_outcome(
            theorem_environment,
            application,
            &selected
                .iter()
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>(),
            claim_label,
            path_index,
            tactic_index,
            available.to_vec(),
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            replay,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )
        .is_ok()
    };
    if !application_replays(&candidates) {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: theorem application depends on a post-execution fact with no checked Click spelling"
        )));
    }
    let mut selected = candidates;
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if application_replays(&reduced) {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn replay_outcome_apply_certificate(
    certificate: &TacticCertificate,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    available: Vec<Proposition>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    replay: &TacticReplayState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let [
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        },
    ] = certificate.tactics()
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: post-execution `apply` produced an unexpected certificate"
        )));
    };
    apply_theorem_using_at_outcome(
        theorem_environment,
        application,
        premises,
        claim_label,
        path_index,
        tactic_index,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        replay,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: post-execution `apply` certificate failed replay: {}",
            error.message()
        ))
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn plan_explicit_fact_transport(
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

pub(super) fn fact_transport_planning_failure(
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
pub(super) fn replay_fact_transport_at_outcome(
    surface_source: &ClickProposition,
    surface_target: &ClickProposition,
    surface_premises: Option<&[ClickProposition]>,
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

    let mut explicit_premises = Vec::new();
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

    let source = recorded_or_lowered(surface_source, available, surface_propositions).map_err(
        |error| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport` source: {}",
                error.message()
            ))
        },
    )?;
    surface_propositions.record_lowering(surface_source, &source)?;
    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
    let selected_assumptions = if surface_premises.is_some() {
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
    };
    // A transport source spelled at a different snapshot than its explicit
    // fact is the same fact when the kernel proves the snapshots agree at
    // the loaded pointers; this previously matched only through the
    // None==None polarity bug, so make the legitimate case deliberate.
    if !exact_fact_is_available(&source, &explicit_premises)
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
    let target = lower(surface_target, &direct_lowering_facts).map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: could not lower `transport` target: {message}"
        ))
    })?;
    surface_propositions.record_lowering(surface_target, &target)?;

    let emitted_premises = if surface_premises.is_some() {
        None
    } else {
        Some(plan_explicit_fact_transport_at_outcome(
            surface_source,
            &source,
            &target,
            available,
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
        if !certified_fact_transport_reaches(
            &source,
            &target,
            post_state.memory(),
            &transport_assumptions,
        ) {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: no certified frame transport applies to the exact source fact"
            )));
        }
        available.push(target.clone());
    }

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
    surface_source: &ClickProposition,
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
                SurfaceFactMatch::ReplayEquivalent,
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
            });
        if selected_assumptions.derive_proposition(source).is_none() {
            return false;
        }
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
pub(super) fn memory_erased_comparison(proposition: &Proposition) -> Option<Proposition> {
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
pub(super) fn path_condition_equivalent(left: &Proposition, right: &Proposition) -> bool {
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
pub(super) fn proposition_outer_load_memory(proposition: &Proposition) -> Option<&CMemory> {
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
pub(super) fn certified_fact_transport_reaches_through(
    source: &Proposition,
    target: &Proposition,
    after: &CMemory,
    assumptions: &Assumptions,
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

pub(super) fn certified_fact_transport_reaches(
    source: &Proposition,
    target: &Proposition,
    after: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    if matches!(target, Proposition::CMemoryLoadable { .. }) {
        return assumptions.derive_atomic_proposition(target).is_some();
    }
    let Some(theorem) = prove_c_condition_fact_transport(source, after, assumptions) else {
        return false;
    };
    let Proposition::Implies(_, conclusion) = theorem.proposition() else {
        unreachable!("condition transport must produce an implication")
    };
    normalize_direct_atomic_memory_loads(conclusion) == normalize_direct_atomic_memory_loads(target)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn fold_composite_resource_at_current_point(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
    available_pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<CState, ClickError> {
    let surface_propositions = SurfacePropositionMap::default();
    let outcome = CFunctionOutcome::Return {
        value: CValue::Int32(Bitvector32Term::Constant(0)),
        state,
    };
    let outcome = fold_composite_resources_on_outcome(
        resource_environment,
        std::slice::from_ref(resource),
        claim_label,
        tactic_index,
        &[],
        available_pure_facts,
        &surface_propositions,
        parameters,
        arguments,
        pre_state,
        outcome,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    let CFunctionOutcome::Return { state, .. } = outcome else {
        unreachable!("folding a synthetic return outcome preserves its outcome kind")
    };
    Ok(state)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_point_proposition(
    proposition: &ClickProposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    lower_point_proposition_with_values(
        proposition,
        available,
        values,
        &array_refs,
        pre_state,
        state,
        result,
        program_point_states,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_point_proposition_with_values(
    proposition: &ClickProposition,
    available: &[Proposition],
    mut values: BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let assumptions = assumptions_from_propositions(available);
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        array_refs,
        pre_state,
        state,
        result,
        &assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        program_point_states,
        &mut active_functions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_have_at_current_point(
    have: &ProofHave,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
) -> Result<Proposition, ClickError> {
    prove_have_at_point(
        have,
        theorem_environment,
        claim_label,
        outer_tactic_index,
        outer_available,
        parameters,
        arguments,
        pre_state,
        state,
        None,
        program_point_states,
        Some(surface_propositions),
        predicate_environment,
        click_function_environment,
        original_requirements,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn plan_smart_have_at_current_point(
    have: &ProofHave,
    claim_label: &str,
    outer_tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    prelowered_goal: Option<&Proposition>,
) -> Result<(Proposition, ProofReplayPlan), ClickError> {
    // Plan and replay this proof once. Surface expansion must lower this exact
    // plan; it must not search for a different proof if lowering is incomplete.
    // Snapshot transport belongs to the statement transition that changed the
    // memory and reaches a later `have` as an exact current-state assumption.
    let direct_lowering_facts = facts_for_smart_have_lowering(available);
    let fact = match lower_point_proposition(
        &have.proposition,
        &direct_lowering_facts,
        parameters,
        arguments,
        pre_state,
        state,
        None,
        program_point_states,
        predicate_environment,
        click_function_environment,
    ) {
        Ok(fact) => fact,
        Err(_) if prelowered_goal.is_some() => prelowered_goal.expect("checked above").clone(),
        Err(message) => match lower_point_proposition(
            &have.proposition,
            &facts_for_simple_goal_lowering(available),
            parameters,
            arguments,
            pre_state,
            state,
            None,
            program_point_states,
            predicate_environment,
            click_function_environment,
        ) {
            Ok(fact) => fact,
            Err(fallback_message) => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` have proof {outer_tactic_index}: could not lower pure goal: {fallback_message}\n  direct lowering also failed: {message}"
                )));
            }
        },
    };
    let available = if unfolded_predicates.is_empty() {
        available.to_vec()
    } else {
        unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            available,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` have proof {outer_tactic_index}: could not unfold available facts: {message}"
            ))
        })?
    };
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &fact,
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` have proof {outer_tactic_index}: could not unfold pure goal: {message}"
        ))
    })?;
    if available.contains(&goal) {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }
    if matches!(normalize_proposition(&goal), SimpProposition::True) {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Normalize])
            .expect("normalize is a simple replay tactic");
        return Ok((fact, plan));
    }
    if quantified_replay_equivalent_available_fact(&goal, &available).is_some() {
        let plan = ProofReplayPlan::from_planned_tactics(&[ProofTactic::Assumption])
            .expect("assumption is a simple replay tactic");
        return Ok((fact, plan));
    }
    let normalized_fact = normalize_direct_atomic_memory_loads(&goal);
    if let Some(equivalent) = available
        .iter()
        .find(|available| normalize_direct_atomic_memory_loads(available) == normalized_fact)
        && let Some(derivation) =
            minimal_proposition_derivation(&goal, std::slice::from_ref(equivalent))?
    {
        let plan =
            ProofReplayPlan::from_planned_tactics(&[ProofTactic::ExactPropositionDerivation(
                derivation,
            )])
            .expect("a directly normalized derivation is a simple replay tactic");
        return Ok((fact, plan));
    }
    if let Some(derivation) = search_condition_derivation(&goal, &available)? {
        let plan =
            ProofReplayPlan::from_planned_tactics(&[ProofTactic::ExactPropositionDerivation(
                derivation,
            )])
            .expect("a bounded condition derivation is a simple replay tactic");
        return Ok((fact, plan));
    }

    let Some(plan) = plan_simp_certificate(&goal, &assumptions) else {
        if let Ok(dir) = std::env::var("CLICK_HAVE_DUMP_DIR") {
            let _ = std::fs::write(format!("{dir}/have-goal.txt"), format!("{goal:#?}"));
            if let Proposition::ForAll { body, .. } = &goal
                && let Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::Bitvector32Equal(left, right),
                    _,
                ) = body.as_ref()
            {
                let canonical_left = crate::kernel::canonicalize_atomic_loads(left);
                let canonical_right = crate::kernel::canonicalize_atomic_loads(right);
                eprintln!(
                    "HAVE PROBE canonical_eq={}",
                    canonical_left == canonical_right
                );
                let _ = std::fs::write(
                    format!("{dir}/canonical-left.txt"),
                    format!("{canonical_left:#?}"),
                );
                let _ = std::fs::write(
                    format!("{dir}/canonical-right.txt"),
                    format!("{canonical_right:#?}"),
                );
            }
        }
        let mut message = format!(
            "`{claim_label}` tactic {outer_tactic_index}: `have` failed: {}",
            describe_missing_pure_fact(
                &goal,
                &available,
                state.resources().facts(),
                parameters,
                arguments,
                &[],
            )
        );
        if matches!(goal, Proposition::ConditionIs(_, _)) {
            message.push_str("\n  ");
            message.push_str(&describe_condition_search_miss(
                &goal, &available, parameters, arguments,
            ));
        }
        return Err(ClickError::new(message));
    };
    if !replay_simp_certificate(&goal, &assumptions, &plan) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: planned smart `have` certificate did not replay"
        )));
    }
    Ok((fact, plan))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_have_at_point(
    have: &ProofHave,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    path_index: Option<usize>,
) -> Result<Proposition, ClickError> {
    prove_pure_proposition_at_point(
        &have.proposition,
        None,
        &have.proof,
        "have",
        theorem_environment,
        claim_label,
        outer_tactic_index,
        outer_available,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        program_point_states,
        surface_propositions,
        predicate_environment,
        click_function_environment,
        original_requirements,
        path_index,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_pure_proposition_at_point(
    proposition: &ClickProposition,
    prelowered_goal: Option<&Proposition>,
    proof: &Proof,
    proof_name: &str,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    path_index: Option<usize>,
) -> Result<Proposition, ClickError> {
    let (proof_cases, tactic_simp) = match proof {
        Proof::Script(tactics) => (expand_proof_if_cases(tactics)?, false),
        Proof::Default | Proof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => (
            vec![ExpandedProofCase {
                tactics: Vec::new(),
                assumptions: Vec::new(),
            }],
            true,
        ),
        Proof::Tactic(SmartTactic::Frame) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `frame` is not available in a pure proof"
            )));
        }
    };
    let mut proven_fact = None;
    for proof_case in proof_cases {
        let fact = prove_pure_proposition_case_at_point(
            proposition,
            prelowered_goal,
            &proof_case,
            tactic_simp,
            proof_name,
            theorem_environment,
            claim_label,
            outer_tactic_index,
            outer_available,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            program_point_states,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            original_requirements,
            path_index,
        )?;
        if let Some(expected) = &proven_fact
            && expected != &fact
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {outer_tactic_index}: `have` cases lowered the same surface fact differently"
            )));
        }
        proven_fact = Some(fact);
    }
    proven_fact.ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index} has no proof cases"
        ))
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_pure_proposition_case_at_point(
    proposition: &ClickProposition,
    prelowered_goal: Option<&Proposition>,
    proof_case: &ExpandedProofCase,
    tactic_simp: bool,
    proof_name: &str,
    theorem_environment: &TheoremEnvironment,
    claim_label: &str,
    outer_tactic_index: usize,
    outer_available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    surface_propositions: Option<&SurfacePropositionMap>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    original_requirements: &[Requirement],
    path_index: Option<usize>,
) -> Result<Proposition, ClickError> {
    let mut available = outer_available.to_vec();
    let mut unfolded_predicates = Vec::new();
    let mut use_simp = tactic_simp;
    let parameter_values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, state.memory());
    let (mut values, array_refs) =
        contract_environment_at_state(&parameter_values, &array_refs, state);
    let mut fact = None;
    let mut goal = None;
    let mut goal_closed = false;
    let mut next_choice_variable = 3_000_000;

    for (inner_tactic_index, tactic) in proof_case.tactics.iter().enumerate() {
        add_have_case_assumptions(
            proof_case,
            inner_tactic_index,
            &mut available,
            claim_label,
            outer_tactic_index,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            program_point_states,
            predicate_environment,
            click_function_environment,
        )?;
        if goal_closed {
            return Err(ClickError::new(format!(
                "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `{}` follows a goal-closing simple tactic",
                tactic_name(tactic)
            )));
        }
        match tactic {
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: unknown predicate `{name}`"
                    )));
                }
                if !unfolded_predicates.contains(name) {
                    unfolded_predicates.push(name.clone());
                }
                available = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &available,
                )
                .map_err(|message| ClickError::new(format!(
                    "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: {message}"
                )))?;
            }
            ProofTactic::ApplyTheorem(application) => {
                let application_context = TheoremApplicationContext {
                    values: &values,
                    array_refs: &array_refs,
                    pre_state,
                    post_state: state,
                    result,
                    program_point_states,
                };
                available = apply_theorem_applications_to_available(
                    theorem_environment,
                    &[(inner_tactic_index, application.clone())],
                    claim_label,
                    path_index,
                    available,
                    &application_context,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => {
                let explicit_premises = premises
                    .iter()
                    .map(|premise| {
                        lower_point_proposition_with_values(
                            premise,
                            &available,
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: could not lower `apply using` premise: {message}"
                        ))
                    })?;
                for premise in &explicit_premises {
                    if !exact_fact_is_available(premise, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `apply using` requires an unavailable exact premise: {premise:?}"
                        )));
                    }
                }
                let application_context = TheoremApplicationContext {
                    values: &values,
                    array_refs: &array_refs,
                    pre_state,
                    post_state: state,
                    result,
                    program_point_states,
                };
                let mut applied = apply_theorem_applications_to_available_with_lowering_context(
                    theorem_environment,
                    &[(inner_tactic_index, application.clone())],
                    claim_label,
                    path_index,
                    explicit_premises,
                    Some(&available),
                    &application_context,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
                for available_fact in available {
                    if !applied.contains(&available_fact) {
                        applied.push(available_fact);
                    }
                }
                available = applied;
            }
            ProofTactic::Have(inner_have) => {
                let inner_fact = prove_have_at_point(
                    inner_have,
                    theorem_environment,
                    claim_label,
                    outer_tactic_index,
                    &available,
                    parameters,
                    arguments,
                    pre_state,
                    state,
                    result,
                    program_point_states,
                    surface_propositions,
                    predicate_environment,
                    click_function_environment,
                    original_requirements,
                    path_index,
                )?;
                if !available.contains(&inner_fact) {
                    available.push(inner_fact);
                }
            }
            ProofTactic::Choose(choice) => {
                apply_choose_tactic(
                    choice,
                    claim_label,
                    path_index.unwrap_or(0),
                    inner_tactic_index,
                    &mut available,
                    &mut values,
                    original_requirements,
                    &mut next_choice_variable,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
            }
            ProofTactic::Witness(witness) => {
                if goal.is_none() {
                    let lowered = if let Some(prelowered_goal) = prelowered_goal {
                        prelowered_goal.clone()
                    } else {
                        lower_point_proposition_with_values(
                            proposition,
                            &available,
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower pure goal: {message}"
                            ))
                        })?
                    };
                    fact = Some(lowered.clone());
                    goal = Some(lowered);
                }
                let assumptions = assumptions_from_propositions(&available);
                let unfolded_goal = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                    goal.as_ref().expect("witness goal should be initialized"),
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not unfold pure goal: {message}"
                    ))
                })?;
                let witness_value = evaluate_witness_tactic_value(
                    witness,
                    claim_label,
                    path_index.unwrap_or(0),
                    inner_tactic_index,
                    &values,
                    &array_refs,
                    pre_state,
                    state,
                    result,
                    &assumptions,
                    predicate_environment,
                    click_function_environment,
                    program_point_states,
                )?;
                goal = Some(apply_witness_tactic(
                    witness,
                    witness_value,
                    unfolded_goal,
                    claim_label,
                    path_index.unwrap_or(0),
                    inner_tactic_index,
                )?);
            }
            ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Contradiction(_)
            | ProofTactic::Derive(_)
            | ProofTactic::Rewrite(_) => {
                let mut prepared_derivation_lowering_facts = None;
                let direct_goal_lowering_facts =
                    matches!(tactic, ProofTactic::Assumption | ProofTactic::Normalize)
                        .then(|| facts_for_simple_goal_lowering(&available));
                if let ProofTactic::Derive(derive) = tactic {
                    let mut lowering_facts = facts_for_direct_derivation_lowering(&available);
                    let mut unresolved = derive.premises.iter().collect::<Vec<_>>();
                    while !unresolved.is_empty() {
                        let mut next = Vec::new();
                        let prior_fact_count = lowering_facts.len();
                        for premise in unresolved {
                            let lowered = surface_propositions
                                .and_then(|propositions| {
                                    propositions.available_kernel(premise, &available).cloned()
                                })
                                .map(Ok)
                                .unwrap_or_else(|| {
                                    lower_point_proposition_with_values(
                                        premise,
                                        &lowering_facts,
                                        values.clone(),
                                        &array_refs,
                                        pre_state,
                                        state,
                                        result,
                                        program_point_states,
                                        predicate_environment,
                                        click_function_environment,
                                    )
                                });
                            match lowered {
                                Ok(lowered) => {
                                    if !lowering_facts.contains(&lowered) {
                                        lowering_facts.push(lowered);
                                    }
                                }
                                Err(_) => next.push(premise),
                            }
                        }
                        if lowering_facts.len() == prior_fact_count && !next.is_empty() {
                            let premise = next[0];
                            let message = lower_point_proposition_with_values(
                                premise,
                                &lowering_facts,
                                values.clone(),
                                &array_refs,
                                pre_state,
                                state,
                                result,
                                program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            .err()
                            .unwrap_or_else(|| {
                                "no further premise lowered against the facts already available"
                                    .to_string()
                            });
                            return Err(ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower `{}` premise `{}`: {message}",
                                tactic_name(tactic),
                                describe_click_proposition(premise),
                            )));
                        }
                        unresolved = next;
                    }
                    prepared_derivation_lowering_facts = Some(lowering_facts);
                }
                if goal.is_none() {
                    let lowered = if let Some(prelowered_goal) = prelowered_goal {
                        prelowered_goal.clone()
                    } else {
                        lower_point_proposition_with_values(
                            proposition,
                            prepared_derivation_lowering_facts
                                .as_deref()
                                .or(direct_goal_lowering_facts.as_deref())
                                .unwrap_or(&available),
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower pure goal: {message}"
                            ))
                        })?
                    };
                    fact = Some(lowered.clone());
                    goal = Some(lowered);
                }
                let unfolded_goal = if unfolded_predicates.is_empty() {
                    goal.as_ref()
                        .expect("simple tactic goal should be initialized")
                        .clone()
                } else {
                    let assumptions = assumptions_from_propositions(&available);
                    unfold_predicates_in_proposition(
                        predicate_environment,
                        click_function_environment,
                        &unfolded_predicates,
                        goal.as_ref().expect("simple tactic goal should be initialized"),
                        &assumptions,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not unfold pure goal: {message}"
                        ))
                    })?
                };
                match tactic {
                    ProofTactic::Assumption => {
                        if !available.contains(&unfolded_goal)
                            && materialization_equivalent_available_fact(&unfolded_goal, &available)
                                .is_none()
                            && quantified_replay_equivalent_available_fact(
                                &unfolded_goal,
                                &available,
                            )
                            .is_none()
                        {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `assumption` failed: {}",
                                describe_missing_pure_fact(
                                    &unfolded_goal,
                                    &available,
                                    state.resources().facts(),
                                    parameters,
                                    arguments,
                                    &[]
                                )
                            )));
                        }
                        goal_closed = true;
                    }
                    ProofTactic::Normalize => {
                        if !normalizes_context_free(&unfolded_goal) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `normalize` failed because the goal did not normalize to true: {unfolded_goal:?}"
                            )));
                        }
                        goal_closed = true;
                    }
                    ProofTactic::Intro
                    | ProofTactic::Split
                    | ProofTactic::Left
                    | ProofTactic::Right
                    | ProofTactic::Contradiction(_) => {
                        let contradiction_fact = match tactic {
                            ProofTactic::Contradiction(surface_fact) => Some(
                                lower_point_proposition_with_values(
                                    surface_fact,
                                    &available,
                                    values.clone(),
                                    &array_refs,
                                    pre_state,
                                    state,
                                    result,
                                    program_point_states,
                                    predicate_environment,
                                    click_function_environment,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: `contradiction` could not lower fact: {message}"
                                    ))
                                })?,
                            ),
                            _ => None,
                        };
                        let mut logical_goal = unfolded_goal;
                        goal_closed = apply_logical_goal_tactic(
                            tactic,
                            &mut logical_goal,
                            &mut available,
                            contradiction_fact,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: {message}"
                            ))
                        })?;
                        goal = Some(logical_goal);
                    }
                    ProofTactic::Derive(derive) => {
                        let derivation_lowering_facts = prepared_derivation_lowering_facts
                            .as_ref()
                            .expect("derive lowering facts should be prepared");
                        let premises = derive
                            .premises
                            .iter()
                            .map(|premise| {
                                if let Some(recorded) = surface_propositions.and_then(
                                    |propositions| {
                                        propositions.available_kernel(premise, &available)
                                    },
                                ) {
                                    Ok(recorded.clone())
                                } else {
                                    lower_point_proposition_with_values(
                                        premise,
                                        derivation_lowering_facts,
                                        values.clone(),
                                        &array_refs,
                                        pre_state,
                                        state,
                                        result,
                                        program_point_states,
                                        predicate_environment,
                                        click_function_environment,
                                    )
                                }
                            })
                            .collect::<Result<Vec<_>, _>>()
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower `{}` premise: {message}",
                                    tactic_name(tactic)
                                ))
                            })?;
                        check_atomic_derivation_goal(
                            tactic,
                            &unfolded_goal,
                            premises,
                            &unfolded_goal,
                            &available,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: {message}"
                            ))
                        })?;
                        goal_closed = true;
                    }
                    ProofTactic::Rewrite(surface_equality) => {
                        let equality = lower_point_proposition_with_values(
                            surface_equality,
                            &available,
                            values.clone(),
                            &array_refs,
                            pre_state,
                            state,
                            result,
                            program_point_states,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` {proof_name} proof {outer_tactic_index}: `rewrite` could not lower equality: {message}"
                            ))
                        })?;
                        goal = Some(
                            rewrite_proposition_by_exact_equality(
                                &unfolded_goal,
                                &equality,
                                &available,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{claim_label}` {proof_name} proof {outer_tactic_index}: {message}"
                                ))
                            })?,
                        );
                    }
                    _ => unreachable!(),
                }
            }
            ProofTactic::Simp => use_simp = true,
            ProofTactic::If(_) => unreachable!("proof-level if tactics are expanded before replay"),
            _ => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` {proof_name} proof {outer_tactic_index}, tactic {inner_tactic_index}: `{}` is not available in a pure proof",
                    tactic_name(tactic)
                )));
            }
        }
    }
    add_have_case_assumptions(
        proof_case,
        proof_case.tactics.len(),
        &mut available,
        claim_label,
        outer_tactic_index,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        program_point_states,
        predicate_environment,
        click_function_environment,
    )?;

    let fact = match fact {
        Some(fact) => fact,
        None => {
            if let Some(prelowered_goal) = prelowered_goal {
                prelowered_goal.clone()
            } else {
                lower_point_proposition_with_values(
                    proposition,
                    &available,
                    values,
                    &array_refs,
                    pre_state,
                    state,
                    result,
                    program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not lower pure goal: {message}"
                    ))
                })?
            }
        }
    };
    if goal_closed {
        return Ok(fact);
    }
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        goal.as_ref().unwrap_or(&fact),
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index}: could not unfold pure goal: {message}"
        ))
    })?;
    if pure_fact_is_replay_available(&goal, &available)
        || (use_simp && matches!(simp_proposition(&goal, &assumptions), SimpProposition::True))
    {
        return Ok(fact);
    }
    let failure = describe_missing_pure_fact(
        &goal,
        &available,
        state.resources().facts(),
        parameters,
        arguments,
        &[],
    );
    if proof_name == "have" {
        Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: `have` failed: {failure}"
        )))
    } else {
        Err(ClickError::new(format!(
            "`{claim_label}` {proof_name} proof {outer_tactic_index} failed: {failure}"
        )))
    }
}

#[allow(clippy::too_many_arguments)]
fn add_have_case_assumptions(
    proof_case: &ExpandedProofCase,
    inner_tactic_index: usize,
    available: &mut Vec<Proposition>,
    claim_label: &str,
    outer_tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    for case_assumption in proof_case
        .assumptions
        .iter()
        .filter(|assumption| assumption.tactic_index == inner_tactic_index)
    {
        let proposition = lower_point_proposition(
            &case_assumption.proposition,
            available,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            program_point_states,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {outer_tactic_index}, `have` tactic {inner_tactic_index}: could not lower `if` condition: {message}"
            ))
        })?;
        available.push(if case_assumption.value {
            proposition
        } else {
            Proposition::Not(Box::new(proposition))
        });
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn finish_ordered_proof_contexts(
    contexts: Vec<ProofReplayContext>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    require_explicit_closers: bool,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_environment: &CExecutionEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut certification_cache = Vec::new();
    let mut captured_paths = Vec::new();
    for context in contexts {
        let path_choices = context.replay.deferred_expansion_path_choices.clone();
        resume_deferred_tactic_expansion_capture(&context.replay)?;
        match finish_ordered_proof_replay(
            context,
            source_path,
            function_block,
            parsed_function,
            claims,
            require_explicit_closers,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            function_environment,
            function,
            arguments,
            tactics,
            &mut certification_cache,
        ) {
            Ok(theorems) => {
                for theorem in theorems {
                    if !verified.contains(&theorem) {
                        verified.push(theorem);
                    }
                }
            }
            Err(error) if error.is_expansion_complete() => {
                let captured = take_path_tactic_expansion_capture()?;
                captured_paths.push(SurfaceReplay {
                    tactics: captured,
                    path_choices,
                    ..SurfaceReplay::default()
                });
            }
            Err(error) => return Err(error),
        }
    }
    if !captured_paths.is_empty() {
        let tactics = if captured_paths
            .iter()
            .all(|path| path.tactics == captured_paths[0].tactics)
        {
            captured_paths[0].tactics.clone()
        } else {
            synthesize_surface_alternatives(captured_paths).map_err(|message| {
                ClickError::new(format!(
                    "could not merge selected deferred tactic across branch contexts: {message}"
                ))
            })?
        };
        let allow_empty = tactics.is_empty();
        return Err(finish_tactic_expansion_capture(
            &SurfaceReplay {
                tactics,
                ..SurfaceReplay::default()
            },
            allow_empty,
        ));
    }
    Ok(verified)
}
