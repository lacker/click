use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn apply_theorem_at_current_point(
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
pub(in crate::lang::click::proof) fn plan_explicit_theorem_application(
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
pub(in crate::lang::click::proof) fn checked_surface_fact_at_outcome(
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
pub(in crate::lang::click::proof) fn apply_theorem_using_at_outcome(
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
pub(in crate::lang::click::proof) fn plan_explicit_theorem_application_at_outcome(
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
pub(in crate::lang::click::proof) fn replay_outcome_apply_certificate(
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
