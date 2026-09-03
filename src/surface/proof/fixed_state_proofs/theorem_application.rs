use super::*;

pub(in crate::surface::proof) struct CheckedFixedStateTheoremApplication {
    pub(in crate::surface::proof) facts: ProofFacts,
    pub(in crate::surface::proof) added_facts: Vec<Proposition>,
}

/// Canonical checker for an explicit theorem application against one fixed
/// symbolic C state. Named premises are the complete evidence set. Ambient proof facts
/// and observable resource facts may only lower those premises and theorem
/// arguments; they cannot discharge an omitted theorem requirement.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn check_fixed_state_theorem_application_using_facts(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    surface_premises: &[ClickProposition],
    claim_label: &str,
    tactic_index: usize,
    available: &ProofFacts,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    surface_propositions: &SurfacePropositionMap,
    unfolded_predicates: &[String],
    effect_facts: &[ExecutionPureFact],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CheckedFixedStateTheoremApplication, ClickError> {
    let resource_facts = state
        .resources()
        .observable_facts_assuming_valid(available.assumptions());
    let mut lowering_assumptions = available.assumptions().clone();
    for fact in resource_facts {
        lowering_assumptions = lowering_assumptions.assume_proposition(fact);
    }

    let mut explicit_premises = Vec::new();
    for surface_premise in surface_premises {
        let freshly_lowered = lower_fixed_state_proposition_with_assumptions(
            surface_premise,
            &lowering_assumptions,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            recorded_snapshots,
            predicate_environment,
            click_function_environment,
        );
        // Prefer the current-state lowering when it is checkable. A retained
        // surface form can also name an older raw load whose value the
        // current memory evaluates through (for example after swapping struct
        // fields); that historical kernel remains the fallback for premises
        // that cannot be checked under the current form.
        let recorded = || {
            surface_propositions
                .available_kernel_matching(surface_premise, |kernel| available.contains(kernel))
                .cloned()
        };
        let premise = match freshly_lowered {
            Ok(fresh) if available.available_across_effects(&fresh, &[]) => fresh,
            Ok(fresh) => recorded().unwrap_or(fresh),
            Err(message) => recorded().ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                ))
            })?,
        };
        if !available.available_across_effects(&premise, &[]) {
            let available_facts = available.to_vec();
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `apply using` requires an exact premise: {}",
                describe_missing_pure_fact(
                    &premise,
                    &available_facts,
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

    let evidence_assumptions = assumptions_from_propositions(&explicit_premises);
    let values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let application_context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        pre_state,
        post_state: state,
        result,
        recorded_snapshots,
    };
    let conclusions = instantiate_theorem_application_with_assumptions(
        theorem_environment,
        application,
        claim_label,
        None,
        tactic_index,
        &explicit_premises,
        &evidence_assumptions,
        &lowering_assumptions,
        &application_context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;

    let mut facts = available.clone();
    let mut added_facts = Vec::new();
    for conclusion in conclusions {
        if !facts.contains_top_level(&conclusion) {
            added_facts.push(conclusion.clone());
        }
        facts = facts.with_kernel_checked_fact(conclusion);
    }

    Ok(CheckedFixedStateTheoremApplication { facts, added_facts })
}

/// Lowers one application's requirements against an already-persistent
/// assumption context. Smart proof-object queries use this entry point so
/// choosing a candidate does not materialize or rescan every ambient fact.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn lower_theorem_application_requirements_with_assumptions(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, String> {
    let theorem = theorem_environment
        .get(&application.name)
        .ok_or_else(|| format!("unknown theorem `{}`", application.name))?;
    let (values, array_refs) = theorem_application_bindings(
        theorem,
        application,
        context,
        assumptions,
        predicate_environment,
        click_function_environment,
    )?;
    // The theorem's parameters shadow any C local of the same name: the
    // application binds them, not the state.
    let bind = |state: &CState| {
        values.iter().fold(state.clone(), |state, (name, value)| {
            state.with_local(name.clone(), value.clone())
        })
    };
    let pre_state = bind(context.pre_state);
    let post_state = bind(context.post_state);
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
            let lowered = lower_fixed_state_proposition_through_kernel(
                requirement,
                assumptions,
                &values,
                &array_refs,
                &pre_state,
                &post_state,
                None,
                context.recorded_snapshots,
                predicate_environment,
                click_function_environment,
            )?;
            unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &lowered,
                assumptions,
            )
            .map(|lowered| lowered.clone())
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn checked_surface_fact_at_outcome(
    view: ExecutionView<'_>,
    unfolded_predicates: &[String],
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
        lower_outcome_proposition_with_recorded_snapshots(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            &lowering_facts,
            surface,
            predicate_environment,
            click_function_environment,
            &view.recorded_snapshots,
        )
        .map_err(ClickError::new)
    };
    let matches_kernel = |lowered: &Proposition| {
        if matches!(match_kind, SurfaceFactMatch::CanonicalExact) {
            return condition_polarity_equivalent(lowered, kernel);
        }
        condition_polarity_equivalent(&lowered.clone(), &kernel.clone())
            || exactly_available_fact(&kernel.clone(), std::slice::from_ref(&lowered.clone()))
                .is_some()
            || quantified_equivalent_available_fact(kernel, std::slice::from_ref(lowered)).is_some()
    };
    // Recorded source forms are the cheapest exact candidates and cover
    // ordinary premises. Check them before synthesizing variants at every
    // retained program point; an ambiguous form simply fails `check` and
    // falls through to the snapshot-qualified search below.
    if let Ok(surface) = view.surface_propositions.checked_surface(kernel, check) {
        return Ok(surface);
    }
    // A statement-indexed form denotes the recorded proposition at that
    // program point. Re-lowering it after the function outcome can
    // materialize a dead local and turn an exact assignment equation into a
    // tautology, even though the recorded form remains a valid premise.
    let recorded_surfaces = view
        .surface_propositions
        .surfaces(kernel)
        .collect::<Vec<_>>();
    for surface in recorded_surfaces.into_iter().rev() {
        if (proposition_contains_at_expression(surface)
            || proposition_contains_old_expression(surface))
            && view
                .surface_propositions
                .available_kernel(surface, available)
                .is_some_and(&matches_kernel)
        {
            return Ok(surface.clone());
        }
    }
    let (exact_snapshots, compatible_snapshots) =
        snapshot_indexed_selectors(kernel, &view.recorded_snapshots);
    for (selector, snapshot_state) in exact_snapshots.iter().chain(&compatible_snapshots) {
        check_verification_deadline()?;
        let Some(base) =
            synthesize_surface_proposition(kernel, parameters, arguments, snapshot_state)
        else {
            continue;
        };
        let Some(variants) = comparison_snapshot_variants(&base, std::slice::from_ref(*selector))
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
    if let Ok(surface) = view.surface_propositions.surface(kernel) {
        bases.push(surface.clone());
    }
    for recorded in view.surface_propositions.kernel_facts() {
        check_verification_deadline()?;
        // The quantifier-shape test is checked first on purpose: it is the
        // weaker of the two conditions, so whenever it holds the mutual
        // `derive_simp_proposition` search below is redundant — and on nested
        // quantified predicate bodies that search costs minutes.
        if (matches!(
            (kernel, recorded),
            (Proposition::ForAll { .. }, Proposition::ForAll { .. })
        ) || quantified_equivalent_available_fact(kernel, std::slice::from_ref(recorded))
            .is_some())
            && let Ok(surface) = view.surface_propositions.surface(recorded)
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
    let selectors = exact_snapshots
        .iter()
        .chain(&compatible_snapshots)
        .map(|(selector, _)| (*selector).clone())
        .collect::<Vec<_>>();
    for indexed_snapshots in [&exact_snapshots, &compatible_snapshots] {
        let indexed_selectors = indexed_snapshots
            .iter()
            .map(|(selector, _)| (*selector).clone())
            .collect::<Vec<_>>();
        for base in &bases {
            check_verification_deadline()?;
            let Some(variants) = comparison_snapshot_variants(base, &indexed_selectors) else {
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
    for (selector, snapshot_state) in exact_snapshots.iter().chain(&compatible_snapshots) {
        check_verification_deadline()?;
        let Some(base) =
            synthesize_surface_proposition(kernel, parameters, arguments, snapshot_state)
        else {
            continue;
        };
        let Some(variants) = comparison_snapshot_variants(&base, std::slice::from_ref(*selector))
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
    // it has no form of its own. Unfold a form of the FOLDED fact at
    // the surface instead — the same rewrite the script's `unfold(...)`
    // performs — and let the round trip below decide whether the result is the
    // fact we were asked for.
    if matches!(
        kernel,
        Proposition::ForAll { .. } | Proposition::Exists { .. }
    ) && !unfolded_predicates.is_empty()
    {
        // A drain that unfolds an ambient predicate replaces the folded fact
        // with its quantified body, so the body can carry a recorded folded
        // form while no Predicate fact survives in `available` for the
        // loop below to start from. Unfold that recorded form at the
        // surface and let the round trip decide.
        let mut kernel_folded_bases = Vec::new();
        for surface in view.surface_propositions.surfaces(kernel) {
            if matches!(surface, ClickProposition::PredicateCall { .. })
                && !kernel_folded_bases.contains(surface)
            {
                kernel_folded_bases.push(surface.clone());
            }
        }
        for base in &kernel_folded_bases {
            check_verification_deadline()?;
            let Some(variants) = comparison_snapshot_variants(base, &selectors) else {
                continue;
            };
            for candidate in variants {
                check_verification_deadline()?;
                let Ok(unfolded) = unfold_structural_invariant_proposition(
                    predicate_environment,
                    &candidate,
                    unfolded_predicates,
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
            for surface in view.surface_propositions.surfaces(fact) {
                if !folded_bases.contains(surface) {
                    folded_bases.push(surface.clone());
                }
            }
            let (folded_exact_snapshots, folded_compatible_snapshots) =
                snapshot_indexed_selectors(fact, &view.recorded_snapshots);
            for state in std::iter::once(post_state).chain(
                folded_exact_snapshots
                    .iter()
                    .chain(&folded_compatible_snapshots)
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
                let Some(variants) = comparison_snapshot_variants(base, &selectors) else {
                    continue;
                };
                for candidate in variants {
                    check_verification_deadline()?;
                    let Ok(unfolded) = unfold_structural_invariant_proposition(
                        predicate_environment,
                        &candidate,
                        unfolded_predicates,
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
                "no checked surface form for post-execution fact",
                kernel,
            ))
        })?;
    if matches_kernel(&check(&surface)?) {
        Ok(surface)
    } else {
        Err(ClickError::new(format!(
            "synthesized post-execution form did not lower to {kernel:?}"
        )))
    }
}
